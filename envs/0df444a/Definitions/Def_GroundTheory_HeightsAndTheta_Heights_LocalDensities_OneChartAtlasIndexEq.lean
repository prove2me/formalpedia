-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OneChartAtlasIndexEq
-- name    : GroundTheory_HeightsAndTheta_Heights_LocalDensities_OneChartAtlasIndexEq
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:16.481262+00:00
-- url     : https://prove2.me/theorems/af0b12b4-85cc-5953-8d1b-ab631906895c
-- title:
--   One Chart Atlas Index Eq
-- statement:
--   Definitions and structural lemmas for One Chart Atlas Index Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/OneChartAtlasIndexEq.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
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
namespace MACompact
variable {D : ℕ} {Ω : Set (Fin D → ℂ)}
def inclChart (hΩ : IsOpen Ω) [Nonempty Ω] : OpenPartialHomeomorph Ω (Fin D → ℂ) :=
  hΩ.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
theorem inclChart_source (hΩ : IsOpen Ω) [Nonempty Ω] : (inclChart hΩ).source = Set.univ := by
  simp [inclChart]
theorem inclChart_target (hΩ : IsOpen Ω) [Nonempty Ω] : (inclChart hΩ).target = Ω := by
  simp [inclChart]
def oneChartAtlas (hΩ : IsOpen Ω) [Nonempty Ω] : FinHolAtlas D Ω where
  n := 1
  chart _ := inclChart hΩ
  cover x := ⟨⟨0, Nat.one_pos⟩, by rw [inclChart_source]; trivial⟩
  holo := by
    intro _ _ y hy
    have hyΩ : y ∈ Ω := by rw [← inclChart_target hΩ]; exact hy.1
    refine analyticAt_id.congr ?_
    filter_upwards [hΩ.mem_nhds hyΩ] with z hz
    exact ((inclChart hΩ).right_inv (by rw [inclChart_target]; exact hz)).symm
def j0 (hΩ : IsOpen Ω) [Nonempty Ω] : Fin (oneChartAtlas hΩ).n := ⟨0, Nat.one_pos⟩
end MACompact
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB


