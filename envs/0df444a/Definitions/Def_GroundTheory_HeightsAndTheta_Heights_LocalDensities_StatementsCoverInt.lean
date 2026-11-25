-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsCoverInt
-- name    : GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsCoverInt
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:01.716823+00:00
-- url     : https://prove2.me/theorems/184b7a52-635c-4f14-aeab-01bf81dad82d
-- title:
--   Statements Cover Int
-- statement:
--   Definitions and structural lemmas for Statements Cover Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/StatementsCoverInt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm.M MeasureTheory
noncomputable section
def CoverChartLIntegral.Hyp {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (q : X → Fin e → ℂ) (M₀ : Set X) (Δ : Set (Fin e → ℂ)) (d : ℕ) : Prop :=
  IsOpen M₀ ∧ (∀ i, A.HoloOn M₀ fun x => q x i) ∧ IsClosed Δ ∧
    (∃ h : Set.MapsTo q M₀ Δᶜ, IsCoveringMap h.restrict) ∧
    ∀ z ∉ Δ, (M₀ ∩ q ⁻¹' {z}).encard = d
def CoverChartLIntegral.Statement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] (A : FinHolAtlas e X)
    (χ : ChartPartition A) (q : X → Fin e → ℂ) (M₀ : Set X) (Δ : Set (Fin e → ℂ)) (d : ℕ),
    CoverChartLIntegral.Hyp A q M₀ Δ d → ∀ g : (Fin e → ℂ) → ENNReal, Measurable g →
      ∑ j, ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' M₀,
          ENNReal.ofReal (χ.χ j ((A.chart j).symm y)) *
            ENNReal.ofReal (‖LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) y :
              (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2) * g (q ((A.chart j).symm y)) =
        d * ∫⁻ z in Δᶜ, g z
section Examples
def linePartitionOne : ChartPartition lineAtlas where
  χ _ _ := 1
  smooth _ _ := contDiffOn_const
  nonneg _ _ := zero_le_one
  tsupport_subset _ := fun _ _ => Set.mem_univ _
  sum_eq_one _ := by show ∑ _j : Fin 1, (1 : ℝ) = 1; simp
end Examples
end
end GroundTheory.Heights₂.Heights.FourB


