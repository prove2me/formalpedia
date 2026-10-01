-- Prove2me | Definitions.Def_Yukon_b72a997d3500e16e073e2af5
-- name    : Yukon_b72a997d3500e16e073e2af5
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:12:26.057764+00:00
-- url     : https://prove2.me/theorems/fefcdd66-4295-4dd5-98b6-c65425fc2535
-- title:
--   YukonModule.VCVio.OracleComp.FinRatPMF.part0
-- statement:
--   Source module VCVio.OracleComp.FinRatPMF.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/OracleComp/FinRatPMF.lean
--
--   yukon-proof-operation:3738f04e18e0e5612c86e988a5a2e86d1dce9eca9468ec81b2599b1618c495a2
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246MzczOGYwNGUxOGUwZTU2MTJjODZlOTg4YTVhMmU4NmQxZGNlOWVjYTk0NjhlYzgxYjI1OTliMTYxOGM0OTVhMiIsImhhc2giOiI5NDA2YzNkZTU2ZjNiMzVjZTVlMjI4ZDRkNGZjMDA3NmMyNmEyYmViOWIzZDc2ZTU2OTY4Njg4YWYxNWNiMWJiIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9iNzJhOTk3ZDM1MDBlMTZlMDczZTJhZjUiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Definitions.Def_Yukon_2b5744019605f484379c669d

public import Definitions.Def_Yukon_0ea8ce6d524d4af5d6af8c16



public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Vector.Defs
public import Mathlib.Data.Finset.Card
public import Init
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Batteries.Control.AlternativeMonad
public import Std.Data.HashMap.Lemmas
public import Mathlib.Data.NNRat.BigOperators
public import Mathlib.Data.FinEnum
public import Mathlib.Data.DFinsupp.BigOperators
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Batteries.Control.OptionT
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Init
public import Lean.Message
public import Batteries.Tactic.Lint.Basic
public import Batteries.Tactic.Lint
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
meta import Definitions.Def_Yukon_0ea8ce6d524d4af5d6af8c16
meta import Definitions.Def_Yukon_2b5744019605f484379c669d
set_option backward.isDefEq.respectTransparency.types false
/-!
# Executable `FinRatPMF` Semantics for `OracleComp`

This file provides a computable oracle evaluator using `FinRatPMF.Raw` and proves that its
denotational semantics agree with the existing `evalDist` semantics of `OracleComp`.
-/

@[expose] public section

open OracleSpec OracleComp

universe u v

namespace FinRatPMF

variable {ι : Type u} {spec : OracleSpec ι}

/-- Computable query implementation using the executable `FinRatPMF.Raw` monad. -/
def finRatImpl [spec.Inhabited] [∀ t : spec.Domain, FinEnum (spec.Range t)] :
    QueryImpl spec Raw :=
  fun t => Raw.uniform (α := spec.Range t)

namespace finRatImpl

variable [spec.Inhabited] [∀ t : spec.Domain, FinEnum (spec.Range t)]

local instance instSpecFintypeOfFinEnum : spec.Fintype where
  fintypeB _ := inferInstance

noncomputable local instance instIsUniformSpec : IsUniformSpec spec :=
  IsUniformSpec.ofFintypeInhabited _

@[simp] lemma toPMF_apply (t : spec.Domain) :
    @Raw.toPMF _ (Classical.decEq _) (finRatImpl (spec := spec) t) =
      PMF.uniformOfFintype (spec.Range t) := by
  letI : DecidableEq (spec.Range t) := Classical.decEq _
  ext x
  simp only [finRatImpl, Raw.toPMF_apply, PMF.uniformOfFintype_apply]
  rw [Raw.prob_eq_prob (Classical.decEq _) FinEnum.decEq, Raw.prob_uniform]
  have hcard : Fintype.card (spec.Range t) ≠ 0 := Fintype.card_ne_zero
  rw [NNRat.cast_inv, ENNReal.coe_inv (by exact_mod_cast hcard)]
  simp

@[simp] lemma evalDist_apply (t : spec.Domain) :
    𝒟[finRatImpl (spec := spec) t] = liftM (PMF.uniformOfFintype (spec.Range t)) := by
  change (liftM (@Raw.toPMF _ (Classical.decEq _) (finRatImpl (spec := spec) t)) : SPMF _) = _
  rw [toPMF_apply]

@[simp] lemma evalDist_simulateQ {α : Type v} (oa : OracleComp spec α) :
    𝒟[simulateQ (finRatImpl (spec := spec)) oa] = 𝒟[oa] := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx h => simp [evalDist_apply, OracleComp.evalDist_query, h]

@[simp] lemma probOutput_simulateQ {α : Type v}
    (oa : OracleComp spec α) (x : α) :
    Pr[= x | simulateQ (finRatImpl (spec := spec)) oa] = Pr[= x | oa] :=
  congrFun (congrArg DFunLike.coe (evalDist_simulateQ (spec := spec) oa)) x

@[simp] lemma probEvent_simulateQ {α : Type v}
    (oa : OracleComp spec α) (p : α → Prop) :
    Pr[ p | simulateQ (finRatImpl (spec := spec)) oa] = Pr[ p | oa] := by
  simp only [probEvent_eq_tsum_indicator, probOutput_simulateQ]

@[simp] lemma support_simulateQ {α : Type v} (oa : OracleComp spec α) :
    support (simulateQ (finRatImpl (spec := spec)) oa) = support oa :=
  Set.ext fun x => mem_support_iff_of_evalDist_eq (evalDist_simulateQ (spec := spec) oa) x

@[simp] lemma finSupport_simulateQ {α : Type v} [DecidableEq α]
    (oa : OracleComp spec α) :
    finSupport (simulateQ (finRatImpl (spec := spec)) oa) = finSupport oa := by
  apply Finset.coe_injective
  rw [coe_finSupport, coe_finSupport, support_simulateQ]

end finRatImpl

namespace Demo

local instance  _root_.FinRatPMF.Demo.instFinEnumBool_vCVio : FinEnum Bool where
  card := 2
  equiv :=
    { toFun := fun b => if b then ⟨1, by decide⟩ else ⟨0, by decide⟩
      invFun := fun i => i.1 = 1
      left_inv := by
        intro b
        cases b <;> rfl
      right_inv := by
        intro i
        fin_cases i <;> rfl }
  decEq := inferInstance

instance  _root_.FinRatPMF.Demo.instFinEnumRangeUnitCoinSpec : (t : coinSpec.Domain) → FinEnum (coinSpec.Range t) := by
  intro t
  change FinEnum Bool
  infer_instance

def xorTwoCoins : FinRatPMF.Raw Bool := do
  let b1 ← FinRatPMF.Raw.coin
  let b2 ← FinRatPMF.Raw.coin
  pure (b1 != b2)

def threeCoinCount : FinRatPMF.Raw Nat := do
  let b1 ← FinRatPMF.Raw.coin
  let b2 ← FinRatPMF.Raw.coin
  let b3 ← FinRatPMF.Raw.coin
  pure (cond b1 1 0 + cond b2 1 0 + cond b3 1 0)

def twoCoinQueries : OracleComp coinSpec Nat := do
  let b1 ← OracleComp.coin
  let b2 ← OracleComp.coin
  pure (cond b1 1 0 + cond b2 1 0)

/-
#eval FinRatPMF.Raw.coin
#eval xorTwoCoins
#eval xorTwoCoins.normalize
#eval threeCoinCount.normalize
#eval! simulateQ (FinRatPMF.finRatImpl (spec := coinSpec)) twoCoinQueries
#eval! (simulateQ (FinRatPMF.finRatImpl (spec := coinSpec)) twoCoinQueries).normalize
#eval! (simulateQ (FinRatPMF.finRatImpl (spec := coinSpec)) twoCoinQueries).normalize.prob 1)
-/

end Demo
end FinRatPMF


