-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
-- name    : GroundTheory_GlobalFields_TateThesis_AdeleMeasure
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:52:42.656828+00:00
-- url     : https://prove2.me/theorems/81786458-005b-4f29-8b5e-4babf69f7b06
-- title:
--   Adele Measure
-- statement:
--   Definitions and structural lemmas for Adele Measure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleMeasure.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasurable
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_exists_sub_mem_integralFiniteAdeles
import Theorems.Thm_GroundTheory_Global_homeomorphMixedSpace_apply
import Theorems.Thm_GroundTheory_Global_isOpen_integralFiniteAdeles
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


set_option autoImplicit false
namespace GroundTheory.Global
open NumberField NumberField.mixedEmbedding IsDedekindDomain MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
theorem countable_numberField : Countable K :=
  (Module.finBasis ℚ K).equivFun.toEquiv.countable_iff.2 inferInstance
instance sigmaCompactSpace_finiteAdeleRing : SigmaCompactSpace (FiniteAdeleRing (𝓞 K) K) := by
  have := countable_numberField K
  rw [← isSigmaCompact_univ_iff]
  have hU : (Set.univ : Set (FiniteAdeleRing (𝓞 K) K)) =
      ⋃ k : K, algebraMap K (FiniteAdeleRing (𝓞 K) K) k +ᵥ
        (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) := by
    refine (Set.eq_univ_of_forall fun a ↦ ?_).symm
    obtain ⟨k, hk⟩ := exists_sub_mem_integralFiniteAdeles a
    refine Set.mem_iUnion.2 ⟨k, ⟨a - algebraMap K _ k, hk, ?_⟩⟩
    simp
  rw [hU]
  exact isSigmaCompact_iUnion_of_isCompact _ fun k ↦
    (isCompact_integralFiniteAdeles K).vadd _
def integralFiniteAdelesPositiveCompacts : TopologicalSpace.PositiveCompacts (FiniteAdeleRing (𝓞 K) K) where
  carrier := integralFiniteAdeles (𝓞 K) K
  isCompact' := isCompact_integralFiniteAdeles K
  interior_nonempty' := by
    rw [isOpen_integralFiniteAdeles.interior_eq]
    exact ⟨0, Subring.zero_mem _⟩
def finiteAdeleMeasure : Measure (FiniteAdeleRing (𝓞 K) K) :=
  (NNReal.sqrt ‖discr K‖₊)⁻¹ • addHaarMeasure (integralFiniteAdelesPositiveCompacts K)
theorem sqrt_discr_ne_zero : NNReal.sqrt ‖discr K‖₊ ≠ 0 := by
  rw [Ne, NNReal.sqrt_eq_zero, nnnorm_eq_zero]
  exact discr_ne_zero K
instance : (finiteAdeleMeasure K).IsAddHaarMeasure := by
  rw [finiteAdeleMeasure]
  exact IsAddHaarMeasure.nnreal_smul _ (inv_ne_zero (sqrt_discr_ne_zero K))
instance : (finiteAdeleMeasure K).Regular := by
  rw [finiteAdeleMeasure]
  infer_instance
def measurableEquivMixedSpace : InfiniteAdeleRing K ≃ᵐ mixedSpace K :=
  (homeomorphMixedSpace K).toMeasurableEquiv
def addEquivMixedSpace : InfiniteAdeleRing K ≃+ mixedSpace K where
  __ := (homeomorphMixedSpace K).toEquiv
  map_add' x y := by
    change homeomorphMixedSpace K (x + y) = homeomorphMixedSpace K x + homeomorphMixedSpace K y
    simp only [homeomorphMixedSpace_apply, map_add]
def infiniteAdeleMeasure : Measure (InfiniteAdeleRing K) :=
  (selfDualMeasure K).map (measurableEquivMixedSpace K).symm
instance : (infiniteAdeleMeasure K).IsAddHaarMeasure :=
  (addEquivMixedSpace K).symm.isAddHaarMeasure_map (selfDualMeasure K)
    (homeomorphMixedSpace K).symm.continuous (homeomorphMixedSpace K).continuous
def adeleMeasure : Measure 𝔸[K] :=
  (infiniteAdeleMeasure K).prod (finiteAdeleMeasure K)
instance : (adeleMeasure K).IsAddHaarMeasure :=
  inferInstanceAs ((infiniteAdeleMeasure K).prod (finiteAdeleMeasure K)).IsAddHaarMeasure
end
end GroundTheory.Global


