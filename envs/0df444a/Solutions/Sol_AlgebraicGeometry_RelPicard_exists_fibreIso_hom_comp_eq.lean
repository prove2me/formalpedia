-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_fibreIso_hom_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/53fc0115-be8c-55fb-8d87-be14f027037f

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_fibreIso_hom_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hx : s ≫ t = x) :
    ∃ φ : pullback (pullback.snd c t) s ≅ pullback c x,
      φ.hom ≫ pullback.snd c x = fibreAt c t s ∧
      φ.hom ≫ pullback.fst c x = pullback.fst (pullback.snd c t) s ≫ pullback.fst c t ∧
      φ.hom ≫ baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t) = pullback.fst (pullback.snd c t) s := by

  subst hx
  refine ⟨pullbackLeftPullbackSndIso c t s, ?_, ?_, ?_⟩
  · simp [fibreAt]
  · simp
  · apply pullback.hom_ext
    · simp only [baseChangeSnd, Category.assoc, pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
    · simp only [baseChangeSnd, Category.assoc, pullback.lift_snd, pullbackLeftPullbackSndIso_hom_snd_assoc, pullback.condition]

end S_AlgebraicGeometry_RelPicard_exists_fibreIso_hom_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_fibreIso_hom_comp_eq (solution)
