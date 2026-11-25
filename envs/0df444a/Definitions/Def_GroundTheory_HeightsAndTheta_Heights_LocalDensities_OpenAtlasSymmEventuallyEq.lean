-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OpenAtlasSymmEventuallyEq
-- name    : GroundTheory_HeightsAndTheta_Heights_LocalDensities_OpenAtlasSymmEventuallyEq
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:48.43546+00:00
-- url     : https://prove2.me/theorems/41ff51f4-1380-5b1a-8c60-9e6804fc5822
-- title:
--   Open Atlas Symm Eventually Eq
-- statement:
--   Definitions and structural lemmas for Open Atlas Symm Eventually Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/OpenAtlasSymmEventuallyEq.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
def openAtlas {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ)) (hΩ : Nonempty Ω) :
    FinHolAtlas D Ω where
  n := 1
  chart _ := Ω.openPartialHomeomorphSubtypeCoe hΩ
  cover _ := ⟨0, by simp⟩
  holo _ _ := by
    intro y hy
    have hy' : y ∈ (Ω.openPartialHomeomorphSubtypeCoe hΩ).target := hy.1
    have hev : (Ω.openPartialHomeomorphSubtypeCoe hΩ ∘ (Ω.openPartialHomeomorphSubtypeCoe hΩ).symm)
        =ᶠ[𝓝 y] id := by
      filter_upwards [(Ω.openPartialHomeomorphSubtypeCoe hΩ).open_target.mem_nhds hy'] with z hz
      exact (Ω.openPartialHomeomorphSubtypeCoe hΩ).right_inv hz
    exact analyticAt_id.congr hev.symm
def openAtlasPartition {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ)) (hΩ : Nonempty Ω) :
    ChartPartition (openAtlas Ω hΩ) where
  χ _ _ := 1
  smooth _ _ := contDiffOn_const
  nonneg _ _ := zero_le_one
  tsupport_subset _ := by
    change _ ⊆ (Ω.openPartialHomeomorphSubtypeCoe hΩ).source
    simp
  sum_eq_one _ := by
    change ∑ _ : Fin 1, (1 : ℝ) = 1
    simp
instance {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ)) (hΩ : Nonempty Ω) :
    Subsingleton (Fin (openAtlas Ω hΩ).n) :=
  (inferInstance : Subsingleton (Fin 1))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB


