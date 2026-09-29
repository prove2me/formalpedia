-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.exists_curveModel_iso_ffEquiv_symm_germToFunctionField_eq_of_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/3ca2a852-c1e6-5c37-84d9-542308eee9cf

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_exists_curveModel_iso_ffEquiv_symm_germToFunctionField_eq_of_algEquiv

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u v

theorem solution
    {K : Type u} [Field K] {L L' : Type v} [Field L] [Field L'] [Algebra K L] [Algebra K L']
    (e : L ≃ₐ[K] L') (M : AlgebraicCurve.CurveModel K L) :
    ∃ (M' : AlgebraicCurve.CurveModel K L') (f : M'.C ≅ M.C), f.hom ≫ M.toBase = M'.toBase ∧
      ∀ (V : M.C.Opens) [Nonempty (Scheme.Opens.toScheme V)] [Nonempty (Scheme.Opens.toScheme (f.hom ⁻¹ᵁ V))]
        (t : Γ(M.C, V)),
        M'.ffEquiv.symm (M'.C.germToFunctionField (f.hom ⁻¹ᵁ V) ((f.hom.app V).hom t)) =
          e (M.ffEquiv.symm (M.C.germToFunctionField V t)) := by
  have he : ∀ a : K, e.toRingEquiv (algebraMap K L a) = algebraMap K L' a := fun a => e.commutes a
  refine ⟨{ C := M.C
            toBase := M.toBase
            ffEquiv := e.symm.toRingEquiv.trans M.ffEquiv
            ffEquiv_algebraMap := fun a => ?_
            placeOfPoint := fun x => Place.congrRingEquiv e.toRingEquiv he (M.placeOfPoint x)
            placeOfPoint_bijective := (Place.congrEquiv e.toRingEquiv he).bijective.comp M.placeOfPoint_bijective
            range_stalk_eq := fun x => ?_
            finset_subset_affineOpen := M.finset_subset_affineOpen }, Iso.refl _, Category.id_comp _, ?_⟩
  ·
    show M.ffEquiv (e.symm.toRingEquiv (algebraMap K L' a)) = _
    rw [show e.symm.toRingEquiv (algebraMap K L' a) = algebraMap K L a from e.symm.commutes a]
    exact M.ffEquiv_algebraMap a
  ·
    have h := M.range_stalk_eq x
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      change e.toRingEquiv.symm ((e.symm.toRingEquiv.trans M.ffEquiv).symm (algebraMap _ _ s)) ∈ (M.placeOfPoint x).toValuationSubring
      have hs : M.ffEquiv.symm (algebraMap _ _ s) ∈ (M.placeOfPoint x).toValuationSubring.toSubring := by
        rw [← h]; exact ⟨s, rfl⟩
      rw [RingEquiv.symm_trans_apply]
      change e.symm (e.symm.symm (M.ffEquiv.symm (algebraMap _ _ s))) ∈ _
      rw [AlgEquiv.symm_symm, AlgEquiv.symm_apply_apply]
      exact hs
    · intro hy
      change e.toRingEquiv.symm y ∈ (M.placeOfPoint x).toValuationSubring at hy
      have hy' : e.toRingEquiv.symm y ∈ ((M.ffEquiv.symm : M.C.functionField ≃+* L).toRingHom.comp
          (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField)).range := by
        rw [h]; exact hy
      obtain ⟨s, hs⟩ := hy'
      refine ⟨s, ?_⟩
      change (e.symm.toRingEquiv.trans M.ffEquiv).symm (algebraMap _ _ s) = y
      rw [RingEquiv.symm_trans_apply]
      change e.symm.symm (M.ffEquiv.symm (algebraMap _ _ s)) = y
      rw [show M.ffEquiv.symm (algebraMap _ _ s) = e.toRingEquiv.symm y from hs, AlgEquiv.symm_symm]
      exact e.apply_symm_apply y
  ·
    intro V i1 i2 t
    have key : M.C.germToFunctionField ((Iso.refl M.C).hom ⁻¹ᵁ V) (((Iso.refl M.C).hom.app V).hom t) =
        M.C.germToFunctionField V t := by
      rfl
    change (e.symm.toRingEquiv.trans M.ffEquiv).symm _ = _
    rw [RingEquiv.symm_trans_apply, key]
    rfl

end S_AlgebraicCurve_CurveModel_exists_curveModel_iso_ffEquiv_symm_germToFunctionField_eq_of_algEquiv
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_exists_curveModel_iso_ffEquiv_symm_germToFunctionField_eq_of_algEquiv (solution)
