-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OfFubiniStudyCoverMass
-- name    : GroundTheory_HeightsAndTheta_Heights_LocalDensities_OfFubiniStudyCoverMass
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T12:29:11.726842+00:00
-- url     : https://prove2.me/theorems/222cf4c2-76e5-5435-98d6-dda4a0eadd21
-- title:
--   Of Fubini Study Cover Mass
-- statement:
--   Definitions and structural lemmas for Of Fubini Study Cover Mass, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/OfFubiniStudyCoverMass.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_HypImp
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
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
noncomputable section
namespace GroundTheory.Heights₂.Heights.FourB
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff
namespace OpenSetChart
variable {D : ℕ} {M : Set (Fin D → ℂ)}
open scoped Classical in

def retract (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) (y : Fin D → ℂ) : M :=
  ⟨if y ∈ M then y else x₀, by split_ifs with h; exacts [h, hx₀]⟩
theorem retract_of_mem {x₀ : Fin D → ℂ} (hx₀ : x₀ ∈ M) {y : Fin D → ℂ} (hy : y ∈ M) :
    (retract x₀ hx₀ y : Fin D → ℂ) = y := by
  simp [retract, hy]
def chart (hM : IsOpen M) (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) : OpenPartialHomeomorph M (Fin D → ℂ) where
  toFun := Subtype.val
  invFun := retract x₀ hx₀
  source := Set.univ
  target := M
  map_source' x _ := x.2
  map_target' _ _ := Set.mem_univ _
  left_inv' x _ := Subtype.ext (retract_of_mem hx₀ x.2)
  right_inv' _ hy := retract_of_mem hx₀ hy
  open_source := isOpen_univ
  open_target := hM
  continuousOn_toFun := continuous_subtype_val.continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert (continuous_id : Continuous (id : M → M)) using 1
    funext y
    exact Subtype.ext (retract_of_mem hx₀ y.2)
theorem eventuallyEq_retract (hM : IsOpen M) {x₀ : Fin D → ℂ} (hx₀ : x₀ ∈ M) {y : Fin D → ℂ}
    (hy : y ∈ M) : (fun y' => (retract x₀ hx₀ y' : Fin D → ℂ)) =ᶠ[𝓝 y] id :=
  Filter.eventually_of_mem (hM.mem_nhds hy) fun _ hy' => retract_of_mem hx₀ hy'
def atlas (hM : IsOpen M) (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) : FinHolAtlas D M where
  n := 1
  chart _ := chart hM x₀ hx₀
  cover _ := ⟨0, Set.mem_univ _⟩
  holo _ _ := fun _ hy => analyticAt_id.congr (eventuallyEq_retract hM hx₀ hy.1).symm
def partition (hM : IsOpen M) (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) :
    ChartPartition (atlas hM x₀ hx₀) where
  χ _ _ := 1
  smooth _ := fun _ => contDiffOn_const
  nonneg _ _ := zero_le_one
  tsupport_subset _ := fun _ _ => Set.mem_univ _
  sum_eq_one _ := by
    show ∑ _j : Fin 1, (1 : ℝ) = 1
    simp
end OpenSetChart
open OpenSetChart
end GroundTheory.Heights₂.Heights.FourB


