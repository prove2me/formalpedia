-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:58.401425+00:00
-- url     : https://prove2.me/theorems/d0c2e161-91ae-49ae-bf0a-c9093b1199e2
-- title:
--   Is Locally Constant Modulus
-- statement:
--   Definitions and structural lemmas for Is Locally Constant Modulus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantModulus.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped TensorProduct ENNReal
namespace GlobalTheory.SmGL.UnitInd
section Tensor
@[reducible] def core {X : Type} [AddCommGroup X] [Module ℂ X] (B : X →ₗ[ℂ] X →ₗ⋆[ℂ] ℂ)
    (hs : ∀ v w, B w v = starRingEnd ℂ (B v w)) (hp : ∀ v, v ≠ 0 → 0 < (B v v).re) :
    InnerProductSpace.Core ℂ X where
  inner v w := B w v
  conj_inner_symm v w := (hs _ _).symm
  re_inner_nonneg v := by
    by_cases h : v = 0
    · simp [h]
    · exact (hp v h).le
  add_left x y z := map_add _ _ _
  smul_left x y r := by simp
  definite v h := by
    by_contra hv
    simpa [h] using hp v hv
variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable {α : Type} [Fintype α] {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
end Tensor
section Average
variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace X]
end Average
section Local
open GlobalTheory.SplitFlip GlobalTheory.SmGL.UnipHaar
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
variable [MeasurableSpace k] [BorelSpace k]
end Local
section Induction
open GlobalTheory.SplitFlip
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
end Induction
end GlobalTheory.SmGL.UnitInd


