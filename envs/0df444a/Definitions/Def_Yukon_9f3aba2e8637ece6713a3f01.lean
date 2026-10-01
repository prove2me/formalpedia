-- Prove2me | Definitions.Def_Yukon_9f3aba2e8637ece6713a3f01
-- name    : Yukon_9f3aba2e8637ece6713a3f01
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:05:32.37242+00:00
-- url     : https://prove2.me/theorems/becebbe8-bd24-4518-a276-cc67522b76c6
-- title:
--   YukonModule.VCVio.OracleComp.OracleComp.part0
-- statement:
--   Source module VCVio.OracleComp.OracleComp. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/OracleComp/OracleComp.lean
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/OracleComp/OracleComp.lean
--
--   yukon-proof-operation:7573732c7d4ac97f9b984cb40e0227c0e8854f5d542f2d234bce8e033000a42e
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246NzU3MzczMmM3ZDRhYzk3ZjliOTg0Y2I0MGUwMjI3YzBlODg1NGY1ZDU0MmYyZDIzNGJjZThlMDMzMDAwYTQyZSIsImhhc2giOiJiNTZiZDEwOWE2MzI0MDQ3ZThiNWJhMmU4M2ZmNmEwNDY2NTZmNDQ1YjZkMGUwMTE0ZGZhZmUwMmI5ZGMzOWIwIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl85ZjNhYmEyZTg2MzdlY2U2NzEzYTNmMDEiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import Definitions.Def_Yukon_0c415a7ac30982e40294fe41

public import Definitions.Def_Yukon_724dee21e2f24de1aadc0f0e



public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Init
public import Lean.Message
public import Batteries.Tactic.Lint.Basic
public import Init
public import Batteries.Tactic.Lint
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Definitions.Def_Yukon_67bc98b5f0d16609cb699923
public import Definitions.Def_Yukon_135b1e0f495a7a36531945f6
public import Definitions.Def_Yukon_d6a80e883014f27d904e1d8e
meta import Definitions.Def_Yukon_67bc98b5f0d16609cb699923
meta import Definitions.Def_Yukon_724dee21e2f24de1aadc0f0e
meta import Definitions.Def_Yukon_0c415a7ac30982e40294fe41
meta import Definitions.Def_Yukon_135b1e0f495a7a36531945f6
meta import Definitions.Def_Yukon_d6a80e883014f27d904e1d8e
set_option backward.isDefEq.respectTransparency.types false
/-!
# Computations with Oracle Access

-/

@[expose] public section

universe u v w

open OracleSpec

/-- `OracleComp spec α` represents computations with oracle access to oracles in `spec`,
where the final return value has type `α`, represented as a free monad over the `PFunctor`
corresponding to `spec.` -/
@[reducible]
def OracleComp {ι : Type u} (spec : OracleSpec.{u, v} ι) :
    Type w → Type (max u v w) :=
  PFunctor.FreeM spec.toPFunctor

variable {α β γ : Type v} {ι} {spec : OracleSpec.{u, v} ι}

namespace OracleComp

open scoped OracleSpec.PrimitiveQuery

/-- Interpret a raw polynomial free program as an oracle computation.

This is the explicit abstraction boundary for generic PolyFun constructions;
downstream semantics should use this function instead of unfolding
`OracleComp`. -/
@[reducible]
def ofFreeM {α : Type w} (oa : PFunctor.FreeM spec.toPFunctor α) : OracleComp spec α := oa

/-- Expose the polynomial free program underlying an oracle computation. -/
@[reducible]
def toFreeM {α : Type w} (oa : OracleComp spec α) : PFunctor.FreeM spec.toPFunctor α := oa

theorem ofFreeM_toFreeM {α : Type w} (oa : OracleComp spec α) :
    ofFreeM (toFreeM oa) = oa := rfl

theorem toFreeM_ofFreeM {α : Type w} (oa : PFunctor.FreeM spec.toPFunctor α) :
    toFreeM (ofFreeM oa) = oa := rfl

/-- Make one oracle query at input `t`, then continue with `k` on the response.

This is the `PFunctor.FreeM.liftBind` constructor specialized to `OracleComp`;
the `@[match_pattern]` attribute makes it usable both as a term and as a
`match` pattern. -/
@[match_pattern, reducible]
def queryBind {α} (t : spec.Domain) (k : spec.Range t → OracleComp spec α) :
    OracleComp spec α :=
  PFunctor.FreeM.liftBind t k

theorem ofFreeM_pure {α : Type v} (x : α) :
    ofFreeM (PFunctor.FreeM.pure x : PFunctor.FreeM spec.toPFunctor α) =
      (pure x : OracleComp spec α) := rfl

theorem ofFreeM_bind {α β : Type v}
    (oa : PFunctor.FreeM spec.toPFunctor α)
    (next : α → PFunctor.FreeM spec.toPFunctor β) :
    ofFreeM (PFunctor.FreeM.bind oa next) =
      (ofFreeM oa >>= fun x => ofFreeM (next x)) := rfl

theorem ofFreeM_map {α β : Type v}
    (f : α → β) (oa : PFunctor.FreeM spec.toPFunctor α) :
    ofFreeM (PFunctor.FreeM.map f oa) = f <$> ofFreeM oa := rfl

/-- Manually lift an `OracleQuery` to an `OracleComp`. -/
@[reducible]
protected def lift {ι} {spec : OracleSpec ι} {α} (q : OracleQuery spec α) :
    OracleComp spec α := liftM q

protected lemma liftM_def (q : OracleQuery spec α) :
    liftM (n := OracleComp spec) q = PFunctor.FreeM.liftObj q := rfl

@[simp, grind .]
lemma liftM_ne_pure (q : OracleQuery spec α) (x : α) :
    liftM (n := OracleComp spec) q ≠ pure x := PFunctor.FreeM.liftObj_ne_pure q x

@[simp, grind .]
lemma pure_ne_liftM (x : α) (q : OracleQuery spec α) :
    pure x ≠ liftM (n := OracleComp spec) q := PFunctor.FreeM.pure_ne_liftObj q x

@[simp, grind =]
protected lemma liftM_map (q : OracleQuery spec α) (f : α → β) :
    liftM (n := OracleComp spec) (f <$> q) = f <$> liftM q := rfl

/-- `coin` is the computation representing a coin flip, given a coin flipping oracle. -/
@[inline]
def coin : OracleComp coinSpec Bool := coinSpec.query ()

@[grind =, aesop safe norm]
lemma coin_def : coin = coinSpec.query () := rfl

protected lemma pure_def (x : α) :
    (pure x : OracleComp spec α) = PFunctor.FreeM.pure x := rfl

protected lemma bind_def (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    oa >>= ob = PFunctor.FreeM.bind oa ob := rfl

/-- Cases eliminator on `OracleComp` exposing the high-level `pure` /
`queryBind` alternatives. Registered as the default `cases` eliminator so that
`cases oa with | pure x => ... | queryBind t k => ...` works transparently on
top of the free-monad substrate. -/
@[elab_as_elim, cases_eliminator]
def casesOn {α} {motive : OracleComp spec α → Sort*}
    (oa : OracleComp spec α)
    (pure : (x : α) → motive (PFunctor.FreeM.pure x : OracleComp spec α))
    (queryBind : (t : spec.Domain) →
      (k : spec.Range t → OracleComp spec α) →
      motive (OracleComp.queryBind (spec := spec) t k)) :
    motive oa :=
  match oa with
  | .pure x => pure x
  | .queryBind t k => queryBind t k

/-- Structural recursion eliminator on `OracleComp` exposing the high-level
`pure` / `queryBind` alternatives, with an induction hypothesis on every
continuation in the `queryBind` case. Registered as the default `induction`
eliminator so that
`induction oa with | pure x => ... | queryBind t k ih => ...`
works transparently on top of the free-monad substrate. -/
@[elab_as_elim, induction_eliminator]
def recOn {α} {motive : OracleComp spec α → Sort*}
    (oa : OracleComp spec α)
    (pure : (x : α) → motive (PFunctor.FreeM.pure x : OracleComp spec α))
    (queryBind : (t : spec.Domain) →
      (k : spec.Range t → OracleComp spec α) →
      ((u : spec.Range t) → motive (k u)) →
      motive (OracleComp.queryBind (spec := spec) t k)) :
    motive oa :=
  match oa with
  | .pure x => pure x
  | .queryBind t k => queryBind t k (fun u => recOn (k u) pure queryBind)

protected lemma failure_def : (failure : OptionT (OracleComp spec) α) = OptionT.fail := rfl

protected lemma orElse_def (oa oa' : OptionT (OracleComp spec) α) : (oa <|> oa') = OptionT.mk
    (do match ← OptionT.run oa with | some a => pure (some a) | _  => OptionT.run oa') := by
  simp only [HOrElse.hOrElse, OrElse.orElse, Alternative.orElse, OptionT.orElse]
  refine congr_arg OptionT.mk <| bind_congr fun x => by aesop

@[aesop safe apply, grind =>]
protected lemma bind_congr' {oa oa' : OracleComp spec α} {ob ob' : α → OracleComp spec β}
    (h : oa = oa') (h' : ∀ x, ob x = ob' x) : oa >>= ob = oa' >>= ob' := h ▸ bind_congr h'

@[simp] -- NOTE: debatable if this should be simp
lemma guard_eq {spec : OracleSpec ι} (p : Prop) [Decidable p] :
    (guard p : OptionT (OracleComp spec) Unit) = if p then pure () else failure := rfl

-- NOTE: This should maybe be a `@[simp]` lemma? `apply_ite` can't be a simp lemma in general.
lemma ite_bind (p : Prop) [Decidable p] (oa oa' : OracleComp spec α)
    (ob : α → OracleComp spec β) : ite p oa oa' >>= ob = ite p (oa >>= ob) (oa' >>= ob) :=
  apply_ite (· >>= ob) p oa oa'

/-- Nicer induction rule for `OracleComp` that uses monad notation.
Allows inductive definitions on computations by considering the two cases:
* `return x` / `pure x` for any `x`
* `do let u ← query i t; oa u` (with inductive results for `oa u`)
See `oracleComp_emptySpec_equiv` for an example of using this in a proof.
If the final result needs to be a `Type` and not a `Prop`, see `OracleComp.construct`. -/
@[elab_as_elim]
protected theorem inductionOn {α} {C : OracleComp spec α → Prop}
    (pure : (a : α) → C (pure a))
    (query_bind : (t : spec.Domain) →
      (oa : spec.Range t → OracleComp spec α) →
        (∀ u, C (oa u)) → C (query t >>= oa))
    (oa : OracleComp spec α) : C oa :=
  PFunctor.FreeM.induction pure query_bind oa

/-- Version of `OracleComp.inductionOn` that includes an `OptionT` in the monad stack
and requires an explicit case to handle `failure`. -/
@[elab_as_elim]
protected theorem inductionOnOptional {α} {C : OptionT (OracleComp spec) α → Prop}
    (pure : (a : α) → C (pure a))
    (query_bind : (t : spec.Domain) →
      (oa : spec.Range t → OptionT (OracleComp spec) α) → (∀ u, C (oa u)) →
      C (query t >>= oa))
    (failure : C failure)
    (oa : OptionT (OracleComp spec) α) : C oa :=
  PFunctor.FreeM.induction
    (fun | some x => pure x | none => failure)
    (fun t => query_bind t) oa

/-- Version of `OracleComp.inductionOn` with the computation at the start. -/
@[elab_as_elim]
protected theorem induction {α} {C : OracleComp spec α → Prop}
    (oa : OracleComp spec α) (pure : (a : α) → C (pure a))
    (query_bind : (t : spec.Domain) →
      (oa : spec.Range t → OracleComp spec α) → (∀ u, C (oa u)) → C (query t >>= oa)) : C oa :=
  PFunctor.FreeM.induction pure query_bind oa

/-- Version of `OracleComp.inductionOnOptional` with the computation at the start. -/
@[elab_as_elim]
protected theorem inductionOptional {α} {C : OptionT (OracleComp spec) α → Prop}
    (oa : OptionT (OracleComp spec) α) (pure : (a : α) → C (pure a))
    (query_bind : (t : spec.Domain) →
      (oa : spec.Range t → OptionT (OracleComp spec) α) → (∀ u, C (oa u)) →
      C (query t >>= oa))
    (failure : C failure) : C oa :=
  PFunctor.FreeM.induction
    (fun | some x => pure x | none => failure)
    query_bind oa

section construct

/-- Version of `construct` with automatic induction on the `query` in when defining the
`query_bind` case. Can be useful with `spec.DecidableEq` and `spec.FiniteRange`.
`mapM`/`simulateQ` is usually preferable to this if the object being constructed is a monad. -/
@[elab_as_elim]
protected def construct {α}
    {C : OracleComp spec α → Type*}
    (pure : (a : α) → C (pure a))
    (query_bind : (t : spec.Domain) →
      (oa : spec.Range t → OracleComp spec α) →
      ((u : spec.Range t) → C (oa u)) → C (query t >>= oa))
    (oa : OracleComp spec α) : C oa :=
  OracleComp.recOn oa pure query_bind

@[simp] lemma construct_pure {α} (x : α)
    {C : OracleComp spec α → Type*} (h_pure : (a : α) → C (pure a))
    (h_query_bind : (t : spec.Domain) →
        (oa : spec.Range t → OracleComp spec α) →
        ((u : spec.Range t) → C (oa u)) → C (query t >>= oa)) :
    OracleComp.construct h_pure h_query_bind (pure x) = h_pure x := rfl

@[simp] lemma construct_query (t : spec.Domain)
    {C : OracleComp spec (spec.Range t) → Type*} (h_pure : (u : spec.Range t) → C (pure u))
    (h_query_bind : (t' : spec.Domain) →
      (oa : spec.Range t' → OracleComp spec (spec.Range t)) →
      ((u : spec.Range t') → C (oa u)) → C (query t' >>= oa)) :
    (OracleComp.construct h_pure h_query_bind
        (query t : OracleComp spec (spec.Range t)) : C (query t)) =
      h_query_bind t pure h_pure := rfl

@[simp] lemma construct_query_bind {α} (t : spec.Domain) (mx : spec.Range t → OracleComp spec α)
    {C : OracleComp spec α → Type*} (h_pure : (a : α) → C (pure a))
    (h_query_bind : (t : spec.Domain) →
        (mx : spec.Range t → OracleComp spec α) →
        ((u : spec.Range t) → C (mx u)) → C (liftM (query t) >>= mx)) :
    OracleComp.construct h_pure h_query_bind (liftM (query t) >>= mx) =
      h_query_bind t mx fun u => OracleComp.construct h_pure h_query_bind (mx u) := rfl

end construct

section noConfusion

variable (x : α) (y : β) (t : spec.Domain) (u : spec.Range t)
  (oa : β → OracleComp spec α) (ou : spec.Range t → OracleComp spec α)

/-- Returns `true` for computations that don't query any oracles or fail, else `false`. -/
def isPure {α : Type _} : OracleComp spec α → Bool
  | .pure _ => true
  | .queryBind _ _ => false

@[simp] lemma isPure_pure : isPure (pure x : OracleComp spec α) = true := rfl
@[simp] lemma isPure_query : isPure (query t : OracleComp spec _) = false := rfl
@[simp] lemma isPure_query_bind : isPure (liftM (OracleSpec.query t) >>= ou) = false := rfl

@[simp] lemma pure_ne_query :
    (pure u : OracleComp spec _) ≠ query t := by simp [OracleSpec.query_def]
@[simp] lemma query_ne_pure :
    (query t : OracleComp spec _) ≠ pure u := by simp [OracleSpec.query_def]

lemma pure_eq_query_iff_false : pure u = (query t : OracleComp spec _) ↔ False := by simp
lemma query_eq_pure_iff_false : (query t : OracleComp spec _) = pure u ↔ False := by simp

end noConfusion

/-- Given a computation `oa : OracleComp spec α`, construct a value `x : α`,
by assuming each query returns the `default` value given by the `Inhabited` instance. -/
def defaultResult [spec.Inhabited] (oa : OracleComp spec α) : α :=
  PFunctor.FreeM.liftM (m := Id) (fun _ => default) oa

/-- Total number of queries in a computation across all possible execution paths.
Can be a helpful alternative to `sizeOf` when proving recursive calls terminate. -/
def totalQueries [spec.Fintype] {α : Type v} (oa : OracleComp spec α) : ℕ := by
  induction oa using OracleComp.construct with
  | pure x => exact 0
  | query_bind t oa rec_n => exact 1 + ∑ x, rec_n x

section inj

/-- Two `pure` computations are equal iff they return the same value. -/
@[simp] lemma pure_inj (x y : α) : pure (f := OracleComp spec) x = pure y ↔ x = y :=
  PFunctor.FreeM.pure_inj x y

/-- Binding two computations gives a pure operation iff the first computation is pure
and the second computation does something pure with the result. -/
@[simp] lemma bind_eq_pure_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) (y : β) :
    oa >>= ob = pure y ↔ ∃ x : α, oa = pure x ∧ ob x = pure y :=
  PFunctor.FreeM.bind_eq_pure_iff oa ob y

/-- Binding two computations gives a pure operation iff the first computation is pure
and the second computation does something pure with the result. -/
@[simp] lemma pure_eq_bind_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) (y : β) :
    pure y = oa >>= ob ↔ ∃ x : α, oa = pure x ∧ ob x = pure y :=
  eq_comm.trans (bind_eq_pure_iff oa ob y)

alias ⟨_, bind_eq_pure⟩ := bind_eq_pure_iff
alias ⟨_, pure_eq_bind⟩ := pure_eq_bind_iff

end inj

end OracleComp


