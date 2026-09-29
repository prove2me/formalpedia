-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.comap_sectionIdeal_eq_top_and_finrank_eq_zero_of_forall_notMem_support
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/d9f446d6-ab05-54ed-a75a-d6fc494df575

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_comap_sectionIdeal_eq_top_and_finrank_eq_zero_of_forall_notMem_support

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (σ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {k : Type u} [Field k] (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (J : (pullback c t).IdealSheafData)
    (hJ : ∀ x ∈ Set.range (rigSection c t σ), x ∉ J.support) :
    (sectionIdeal c σ t).comap J.subschemeι = ⊤ ∧
      ((sectionIdeal c σ t).comap J.subschemeι).IsInvertible ∧
      IsFinite (((sectionIdeal c σ t).comap J.subschemeι).subschemeι ≫ J.subschemeι ≫ pullback.snd c t) ∧
      ∀ q : Spec (CommRingCat.of k),
        (((sectionIdeal c σ t).comap J.subschemeι).subschemeι ≫ J.subschemeι ≫ pullback.snd c t).finrank q = 0 := by
  have hs_snd : rigSection c t σ ≫ pullback.snd c t = 𝟙 _ := pullback.lift_snd _ _ _
  haveI : IsClosedImmersion (rigSection c t σ) := by
    have : IsClosedImmersion (rigSection c t σ ≫ pullback.snd c t) := by rw [hs_snd]; infer_instance
    exact IsClosedImmersion.of_comp (rigSection c t σ) (pullback.snd c t)
  have hIker : sectionIdeal c σ t = (rigSection c t σ).ker := rfl
  have hsupp : ((sectionIdeal c σ t).support : Set ↥(pullback c t)) = Set.range (rigSection c t σ) := by
    rw [hIker, Scheme.Hom.support_ker, (Scheme.Hom.isClosedEmbedding (rigSection c t σ)).isClosed_range.closure_eq]

  have hK : (sectionIdeal c σ t).comap J.subschemeι = ⊤ := by
    apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
    rw [Scheme.IdealSheafData.support_comap]
    refine le_bot_iff.mp fun w hw => ?_
    have hw' : J.subschemeι w ∈ ((sectionIdeal c σ t).support : Set ↥(pullback c t)) := hw
    rw [hsupp] at hw'
    refine (hJ _ hw' ?_).elim
    rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨w, rfl⟩
  rw [hK]
  refine ⟨rfl, Scheme.IdealSheafData.isInvertible_top, inferInstance, fun q => ?_⟩

  generalize ((⊤ : (J.subscheme).IdealSheafData).subschemeι ≫ J.subschemeι ≫ pullback.snd c t) = g
  haveI : IsOpenImmersion g := isOpenImmersion_of_isEmpty g
  have hns : ¬ Surjective g := fun h => by
    obtain ⟨x, -⟩ := h.surj q
    exact isEmptyElim x
  rw [← Scheme.Hom.one_le_finrank_iff_surjective] at hns
  simp only [Pi.le_def, Pi.one_apply, not_forall, not_le, Nat.lt_one_iff] at hns
  obtain ⟨y, hy⟩ := hns
  rwa [Subsingleton.elim q y]

end S_AlgebraicGeometry_RelPicard_comap_sectionIdeal_eq_top_and_finrank_eq_zero_of_forall_notMem_support
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_comap_sectionIdeal_eq_top_and_finrank_eq_zero_of_forall_notMem_support (solution)
