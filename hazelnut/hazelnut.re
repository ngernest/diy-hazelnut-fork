open Sexplib.Std;
open Monad_lib.Monad; // Uncomment to use the let*/let+ monad syntax

let compare_string = String.compare;
let compare_int = Int.compare;

module Htyp = {
  [@deriving (sexp, compare, show({with_path: false}))]
  type t =
    | Arrow(t, t)
    | Num
    | Hole;
};

module Hexp = {
  [@deriving (sexp, compare, show({with_path: false}))]
  type t =
    | Var(string)
    | Lam(string, t)
    | Ap(t, t)
    | Lit(int)
    | Plus(t, t)
    | Asc(t, Htyp.t)
    | EHole // Empty Hole
    | NEHole(t); // Non-empty hole
};

module Ztyp = {
  [@deriving (sexp, compare, show({with_path: false}))]
  type t =
    | Cursor(Htyp.t)
    | LArrow(t, Htyp.t)
    | RArrow(Htyp.t, t);
};

module Zexp = {
  [@deriving (sexp, compare, show({with_path: false}))]
  type t =
    | Cursor(Hexp.t)
    | Lam(string, t)
    | LAp(t, Hexp.t)
    | RAp(Hexp.t, t)
    | LPlus(t, Hexp.t)
    | RPlus(Hexp.t, t)
    | LAsc(t, Htyp.t)
    | RAsc(Hexp.t, Ztyp.t)
    | NEHole(t);
};

module Child = {
  [@deriving (sexp, compare)]
  type t =
    | One
    | Two;
};

module Dir = {
  [@deriving (sexp, compare)]
  type t =
    | Child(Child.t)
    | Parent;
};

module Shape = {
  [@deriving (sexp, compare)]
  type t =
    | Arrow
    | Num
    | Asc
    | Var(string)
    | Lam(string)
    | Ap
    | Lit(int)
    | Plus
    | NEHole;
};

module Action = {
  [@deriving (sexp, compare)]
  type t =
    | Move(Dir.t)
    | Construct(Shape.t)
    | Del
    | Finish;
};

module TypCtx = Map.Make(String);
type typctx = TypCtx.t(Htyp.t);

exception Unimplemented;

// =====================================================================
// STEP 1: Type compatibility helpers (Definition 1-3 in the paper)
//
// These helpers are used pervasively by the typing and action rules.
// Implement them first — the test suite can verify them in isolation.
// =====================================================================

// Type consistency (Definition 1, Figure 9):
//   TCRefl:  τ ~ τ                    (reflexivity for base types)
//   TCHole1: ⦇⦈ ~ τ                   (hole is consistent with anything)
//   TCHole2: τ ~ ⦇⦈                   (symmetric)
//   TCArr:   τ₁ ~ τ₁' ∧ τ₂ ~ τ₂'  →  (τ₁→τ₂) ~ (τ₁'→τ₂')
let rec consistent = (t1: Htyp.t, t2: Htyp.t): bool => {
  switch (t1, t2) {
  | (Hole, _)
  | (_, Hole)
  | (Num, Num) => true
  | (Arrow(t11, t12), Arrow(t1', t2')) =>
    consistent(t11, t1') && consistent(t12, t2')
  | _ => false
  };
};

// Type inconsistency (Definition 2): τ ⌿~ τ'  iff  ¬(τ ~ τ')
let inconsistent = (t1: Htyp.t, t2: Htyp.t): bool => {
  !consistent(t1, t2);
};

// Matched arrow types (Definition 3, Figure 9):
//   MAArr:  (τ₁→τ₂) ▸→ (τ₁, τ₂)
//   MAHole: ⦇⦈ ▸→ (⦇⦈, ⦇⦈)
let matched_arrow = (t: Htyp.t): option((Htyp.t, Htyp.t)) => {
  switch (t) {
  | Arrow(t1, t2) => Some((t1, t2))
  | Hole => Some((Hole, Hole))
  | _ => None
  };
};

// =====================================================================
// STEP 2: Cursor erasure (Appendix A.2)
//
// These strip the cursor position from a zipper, recovering the
// underlying H-type or H-expression. Needed by the action semantics
// and the webapp's theorem checks.
// =====================================================================

// Type cursor erasure (Appendix A.2.1):
//   ETTop:   erase(▶τ̇◀)   = τ̇
//   ETArrL:  erase(τ̂ → τ̇) = erase(τ̂) → τ̇
//   ETArrR:  erase(τ̇ → τ̂) = τ̇ → erase(τ̂)
let rec erase_typ = (zt: Ztyp.t): Htyp.t =>
  switch (zt) {
  | Cursor(ht) => ht // ETTop
  | LArrow(t_hat, t_dot) => Arrow(erase_typ(t_hat), t_dot) // ETArrL
  | RArrow(t_dot, t_hat) => Arrow(t_dot, erase_typ(t_hat)) // ETArrR
  };

// Expression cursor erasure (Appendix A.2.2):
//   EETop:    erase(▶ė◀)   = ė
//   EEAscL:   erase(ê : τ̇) = erase(ê) : τ̇
//   EEAscR:   erase(ė : τ̂) = ė : erase_typ(τ̂)
//   EELam:    erase(λx.ê)  = λx.erase(ê)
//   EEApL:    erase(ê ė)   = erase(ê) ė
//   EEApR:    erase(ė ê)   = ė erase(ê)
//   EEPlusL:  erase(ê + ė) = erase(ê) + ė
//   EEPlusR:  erase(ė + ê) = ė + erase(ê)
//   EENEHole: erase(⦇ê⦈)   = ⦇erase(ê)⦈
let rec erase_exp = (zexp: Zexp.t): Hexp.t =>
  switch (zexp) {
  | Cursor(hexp) => hexp // EETop
  | LAsc(e_hat, t_dot) => Asc(erase_exp(e_hat), t_dot) // EEAscL
  | RAsc(e_dot, t_hat) => Asc(e_dot, erase_typ(t_hat)) // EEAscR
  | Lam(x, e_hat) => Lam(x, erase_exp(e_hat)) // EELam
  | LAp(e_hat, e_dot) => Ap(erase_exp(e_hat), e_dot) // EEApL
  | RAp(e_dot, e_hat) => Ap(e_dot, erase_exp(e_hat)) // EEApR
  | LPlus(e_hat, e_dot) => Plus(erase_exp(e_hat), e_dot) // EEPlusL
  | RPlus(e_dot, e_hat) => Plus(e_dot, erase_exp(e_hat)) // EEPlusR
  | NEHole(e_hat) => NEHole(erase_exp(e_hat)) // EENEHole
  };

// =====================================================================
// STEP 3: Bidirectional type system (Section 3.1, Figure 4)
//
// syn and ana are mutually recursive. syn returns the synthesized type
// (or None if the expression is ill-typed); ana returns whether the
// expression checks against the given type.
// =====================================================================

// Type synthesis — Γ ⊢ e ⇒ τ:
//   SVar    (1a): Γ(x) = τ                               →  Γ ⊢ x ⇒ τ
//   SAp     (1b): Γ ⊢ e₁ ⇒ τ₁, τ₁ ▸→ (τ₂,τ), Γ ⊢ e₂ ⇐ τ₂  →  Γ ⊢ e₁(e₂) ⇒ τ
//   SNum    (1c):                                         →  Γ ⊢ n ⇒ num
//   SPlus   (1d): Γ ⊢ e₁ ⇐ num, Γ ⊢ e₂ ⇐ num          →  Γ ⊢ e₁+e₂ ⇒ num
//   SAsc    (1e): Γ ⊢ e ⇐ τ                              →  Γ ⊢ (e : τ) ⇒ τ
//   SEHole  (1f):                                         →  Γ ⊢ ⦇⦈ ⇒ ⦇⦈
//   SNEHole (1g): Γ ⊢ e ⇒ τ                              →  Γ ⊢ ⦇e⦈ ⇒ ⦇⦈
//
// Note: Lam has NO synthesis rule — it can only be checked analytically.
let rec syn = (ctx: typctx, e: Hexp.t): option(Htyp.t) => {
  switch (e) {
  | Var(x) =>
    switch (TypCtx.find(x, ctx)) {
    | ty => Some(ty)
    | exception Not_found => None
    }
  | Ap(e1, e2) =>
    let* t1 = syn(ctx, e1);
    let* (t2, t) = matched_arrow(t1);
    if (ana(ctx, e2, t2)) {
      Some(t);
    } else {
      None;
    };
  | Lit(_) => Some(Num)
  | Plus(e1, e2) =>
    if (ana(ctx, e1, Num) && ana(ctx, e2, Num)) {
      Some(Num);
    } else {
      None;
    }
  | Asc(e, ty) =>
    if (ana(ctx, e, ty)) {
      Some(ty);
    } else {
      None;
    }
  | EHole => Some(Hole)
  | NEHole(e) =>
    let+ _ = syn(ctx, e);
    Htyp.Hole;
  | Lam(_, _) => None // No synthesis rule for lambdas
  };
}

// Type analysis — Γ ⊢ e ⇐ τ:
//   ALam      (2a): τ ▸→ (τ₁,τ₂), Γ,x:τ₁ ⊢ e ⇐ τ₂    →  Γ ⊢ λx.e ⇐ τ
//   ASubsume  (2b): Γ ⊢ e ⇒ τ', τ ~ τ'                  →  Γ ⊢ e ⇐ τ
and ana = (ctx: typctx, e: Hexp.t, t: Htyp.t): bool => {
  switch (e) {
  | Lam(x, e) =>
    switch (matched_arrow(t)) {
    | Some((t1, t2)) =>
      let extended_ctx = TypCtx.add(x, t1, ctx);
      ana(extended_ctx, e, t2);
    | None => false
    }
  | _ =>
    switch (syn(ctx, e)) {
    | Some(t') => consistent(t, t')
    | None => false
    }
  };
};

// =====================================================================
// STEP 4: Action semantics (Section 3.3)
//
// This is the heart of Hazelnut. You will need to implement several
// internal helpers before tackling the main action functions:
//
//   type_action : (Ztyp.t, Action.t) → option(Ztyp.t)
//     Type actions: move, delete, and construct on type zippers.
//     Rules: TMArrChild1/2, TMArrParent1/2, TMDel, TMConArrow, TMConNum,
//            TMArrZip1, TMArrZip2
//
//   move_exp : (Zexp.t, Dir.t) → option(Zexp.t)
//     Expression movement: move the cursor up/down the tree.
//     Handle each Zexp form's Child(One)/Child(Two)/Parent cases,
//     plus zipper recursion (delegate to type_action for RAsc).
//
// A suggested implementation order within the actions:
//   1. Movement (Move)    — simplest, no type changes
//   2. Deletion (Del)     — replaces cursor target with a hole
//   3. Construction       — the bulk of the rules
//   4. Finishing (Finish) — unwraps non-empty holes
//   5. Zipper rules       — recursive propagation through the tree
// =====================================================================

// TODO: rename this function to `type_action` when it is actually used
let rec _type_action = (zty: Ztyp.t, action: Action.t): option(Ztyp.t) =>
  switch (zty, action) {
  | (Cursor(Arrow(t1, t2)), Move(Child(One))) =>
    // TMArrChild1
    Some(LArrow(Cursor(t1), t2))
  | (Cursor(Arrow(t1, t2)), Move(Child(Two))) =>
    // TMArrChild2
    Some(RArrow(t1, Cursor(t2)))
  | (LArrow(Cursor(t1), t2), Move(Parent))
  | (RArrow(t1, Cursor(t2)), Move(Parent)) =>
    // TMArrParent1, TMArrParent2
    Some(Cursor(Arrow(t1, t2)))
  | (Cursor(_), Del) => Some(Cursor(Hole)) // TMDel
  | (Cursor(t), Construct(Arrow)) =>
    // TMConArrow
    Some(RArrow(t, Cursor(Hole)))
  | (Cursor(Hole), Construct(Num)) =>
    // TMConNum
    Some(Cursor(Num))
  | (LArrow(t1, t2), _) =>
    let+ t1' = _type_action(t1, action);
    Ztyp.LArrow(t1', t2);
  | (RArrow(t1, t2), _) =>
    let+ t2' = _type_action(t2, action);
    Ztyp.RArrow(t1, t2');
  | _ => None
  };

// TODO: see Appendix A.3.2 for expression movement rules
let _move_exp = (zexp: Zexp.t, action: Action.t): option(Zexp.t) => {
  switch (zexp, action) {
  | (Cursor(Asc(e, t)), Move(Child(One))) =>
    // EMAscChild1
    Some(LAsc(Cursor(e), t))
  | (Cursor(Asc(e, t)), Move(Child(Two))) =>
    // EMAscChild2
    Some(RAsc(e, Cursor(t)))
  | _ => raise(Unimplemented)
  };
};

// Synthetic action — Γ ⊢ ê ⇒ τ --α--> ê' ⇒ τ':
//
// Base cases on (ê, α):
//   SAMove        (7a):  (ê, move δ) → move cursor
//   SADel         (13a): (▶ė◀, del)  → ▶⦇⦈◀ ⇒ ⦇⦈
//   SAConAsc      (13c): (▶ė◀, construct asc) → ė : ▶τ̇◀
//   SAConVar      (13e): (▶⦇⦈◀, construct var x) → ▶x◀ ⇒ Γ(x)
//   SAConLam      (13g): (▶⦇⦈◀, construct lam x) → λx.⦇⦈ : ▶⦇⦈◀→⦇⦈
//   SAConApArr    (13h): (▶ė◀, construct ap) when τ ▸→ → ė(▶⦇⦈◀)
//   SAConApOtw    (13i): (▶ė◀, construct ap) when τ ⌿~ (⦇⦈→⦇⦈) → ⦇ė⦈(▶⦇⦈◀)
//   SAConNumLit   (13j): (▶⦇⦈◀, construct lit n) → ▶n◀ ⇒ num
//   SAConPlus1    (13k): (▶ė◀, construct plus) when τ ~ num → ė + ▶⦇⦈◀
//   SAConPlus2    (13l): (▶ė◀, construct plus) when τ ⌿~ num → ⦇ė⦈ + ▶⦇⦈◀
//   SAConNEHole   (13m): (▶ė◀, construct nehole) → ⦇▶ė◀⦈
//   SAFinish      (15a): (▶⦇ė⦈◀, finish) → ▶ė◀ ⇒ syn(ė)
//
// Zipper cases (action propagates into a subterm):
//   SAZipAsc1     (18b): LAsc(ê, τ̇)  — action on expression in ascription
//   SAZipAsc2     (18c): RAsc(ė, τ̂)  — action on type in ascription
//   SAZipApArr    (18d): LAp(ê, ė)   — action on function in application
//   SAZipApAna    (18e): RAp(ė, ê)   — action on argument in application
//   SAZipPlus1    (18f): LPlus(ê, ė) — action on left of plus
//   SAZipPlus2    (18g): RPlus(ė, ê) — action on right of plus
//   SAZipHole     (18h): NEHole(ê)   — action inside non-empty hole
let syn_action =
    (ctx: typctx, (ze: Zexp.t, t: Htyp.t), a: Action.t)
    : option((Zexp.t, Htyp.t)) => {
  let _ = (ctx, ze, t, a);
  raise(Unimplemented);
}

// Analytic action — Γ ⊢ ê --α--> ê' ⇐ τ:
//
// Base cases:
//   AAMove        (7b):  (ê, move δ) → move cursor
//   AADel         (5):   (▶ė◀, del)  → ▶⦇⦈◀
//   AAConAsc      (13b): (▶ė◀, construct asc) → ė : ▶τ̇◀
//   AAConVar      (13d): (▶⦇⦈◀, construct var x) — subsume or wrap in NEHole
//   AAConLam1     (13e): (▶⦇⦈◀, construct lam x) when τ ▸→  → λx.▶⦇⦈◀
//   AAConLam2     (13f): (▶⦇⦈◀, construct lam x) when τ ⌿~ (⦇⦈→⦇⦈)
//   AAConNumLit   (13k): (▶⦇⦈◀, construct lit n) — subsume or wrap in NEHole
//   AAFinish      (15b): (▶⦇ė⦈◀, finish) when Γ ⊢ e ⇐ τ → ▶ė◀
//
// Zipper case:
//   AAZipLam      (18a): Lam(x, ê) — action inside lambda body
//
// Subsumption fallthrough:
//   AASubsume     (16b): if none of the above match, try syn_action
//                        and check that the result type is consistent with τ.
and ana_action =
    (ctx: typctx, ze: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  let _ = (ctx, ze, a, t);
  raise(Unimplemented);
};
