-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_MultiplicityOne_OpenSubgroupRep
-- name    : GroundTheory_AutomorphicForms_MultiplicityOne_OpenSubgroupRep
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:32:25.284812+00:00
-- url     : https://prove2.me/theorems/abae682c-8299-424e-b76b-20df627b5f50
-- title:
--   Open Subgroup Rep
-- statement:
--   Definitions and structural lemmas for Open Subgroup Rep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MultiplicityOne/OpenSubgroupRep.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_directSum_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.directSum_apply


set_option autoImplicit false
open MeasureTheory Set Filter Topology Function
namespace GroundTheory.Automorphic
noncomputable section
namespace UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def compHom (π : UnitaryRep G H) {G' : Type*} [Group G'] [TopologicalSpace G'] (f : G' →* G)
    (hf : Continuous f) : UnitaryRep G' H :=
  ⟨π.toHom.comp f, fun v => (π.continuous_orbit v).comp hf⟩
@[simp] theorem compHom_apply (π : UnitaryRep G H) {G' : Type*} [Group G'] [TopologicalSpace G']
    (f : G' →* G) (hf : Continuous f) (g : G') : π.compHom f hf g = π (f g) := rfl
set_option linter.unusedSectionVars false
variable [IsTopologicalGroup G] [T2Space G]
open Classical in

def extendZero {L : Subgroup G} (hL : IsOpen (L : Set G)) (f : CompactlySupportedContinuousMap L ℂ) :
    CompactlySupportedContinuousMap G ℂ where
  toFun g := if h : g ∈ L then f ⟨g, h⟩ else 0
  continuous_toFun := by
    classical
    refine continuous_iff_continuousAt.2 fun g => ?_
    by_cases hg : g ∈ L
    · have he : IsOpenEmbedding ((↑) : L → G) := hL.isOpenEmbedding_subtypeVal
      have h1 : ((fun g => if h : g ∈ L then f ⟨g, h⟩ else 0) ∘ ((↑) : L → G)) = f := by
        funext x
        simp [x.2]
      have key : ContinuousAt ((fun g => if h : g ∈ L then f ⟨g, h⟩ else 0) ∘ ((↑) : L → G))
          (⟨g, hg⟩ : L) := by
        rw [h1]
        exact f.continuous.continuousAt
      exact he.continuousAt_iff.1 key
    · have hcl : IsOpen (L : Set G)ᶜ := (Subgroup.isClosed_of_isOpen L hL).isOpen_compl
      refine (continuousAt_const (y := (0 : ℂ))).congr ?_
      filter_upwards [hcl.mem_nhds hg] with x hx
      rw [dif_neg (show x ∉ L from hx)]
  hasCompactSupport' := by
    refine HasCompactSupport.intro (f.hasCompactSupport.isCompact.image continuous_subtype_val)
      fun g hg => ?_
    by_cases h : g ∈ L
    · rw [dif_pos h]
      exact image_eq_zero_of_notMem_tsupport fun ht => hg ⟨⟨g, h⟩, ht, rfl⟩
    · rw [dif_neg h]
variable [MeasurableSpace G] [BorelSpace G]
theorem isFiniteMeasureOnCompacts_comap (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    {L : Subgroup G} (hL : IsOpen (L : Set G)) :
    IsFiniteMeasureOnCompacts (μ.comap ((↑) : L → G)) := by
  refine ⟨fun S hS => ?_⟩
  erw [(MeasurableEmbedding.subtype_coe hL.measurableSet).comap_apply]
  exact (hS.image continuous_subtype_val).measure_lt_top
end UnitaryRep
end
end GroundTheory.Automorphic


