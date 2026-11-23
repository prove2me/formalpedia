-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:54.994386+00:00
-- url     : https://prove2.me/theorems/19fabee0-8c3b-4a16-90f4-610d51290e70
-- title:
--   Partition
-- statement:
--   Definitions and structural lemmas for Partition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/Partition.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Partition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff
noncomputable section
def pa_aff {e : ℕ} (a : ℂ) (ha : a ≠ 0) (b : Fin e → ℂ) : (Fin e → ℂ) ≃ₜ (Fin e → ℂ) where
  toFun y := a • (y - b)
  invFun z := a⁻¹ • z + b
  left_inv y := by simp [smul_smul, inv_mul_cancel₀ ha]
  right_inv z := by simp [smul_smul, mul_inv_cancel₀ ha]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop
def AffineChartStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (j : Fin A.n) (a : ℂ)
    (b : Fin e → ℂ), a ≠ 0 →
    ∃ ψ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ ∧
      ψ.source = (A.chart j).source ∧ ∀ x ∈ ψ.source, ψ x = a • (A.chart j x - b)
def AtlasOfCompatStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {m : ℕ}
    (ψ : Fin m → OpenPartialHomeomorph X (Fin e → ℂ)), (∀ i, IsCompatChart A (ψ i)) →
    (∀ x, ∃ i, x ∈ (ψ i).source) →
    ∃ B : FinHolAtlas e X, A.Compatible B ∧ (∀ i, ∃ j, B.chart j = ψ i) ∧ ∀ j, ∃ i, B.chart j = ψ i
end
end ReciprocityTheory.AnForm.M


