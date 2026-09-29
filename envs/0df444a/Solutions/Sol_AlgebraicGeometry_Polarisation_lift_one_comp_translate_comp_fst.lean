-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.lift_one_comp_translate_comp_fst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/eb7088f3-383d-5a88-9a52-dd6f7419f7a2

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_lift_one_comp_translate_comp_fst

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f) :
    pullback.lift (L.one (𝟙 (Spec (CommRingCat.of S)))).1 (𝟙 (Spec (CommRingCat.of S))) (by rw [(L.one _).2, Category.comp_id]) ≫
        Polarisation.translate f L (𝟙 (Spec (CommRingCat.of S))) x ≫ pullback.fst f (𝟙 (Spec (CommRingCat.of S))) = x.1 := by
  have hψ : pullback.lift (L.one (𝟙 (Spec (CommRingCat.of S)))).1 (𝟙 (Spec (CommRingCat.of S))) (by rw [(L.one _).2, Category.comp_id]) ≫
      (pullback.snd f (𝟙 (Spec (CommRingCat.of S))) ≫ 𝟙 (Spec (CommRingCat.of S))) = 𝟙 (Spec (CommRingCat.of S)) := by
    rw [← Category.assoc, pullback.lift_snd, Category.id_comp]
  unfold Polarisation.translate
  rw [pullback.lift_fst]
  have key := congrArg Subtype.val (L.mul_natural _ _ _ hψ
    ⟨pullback.fst f (𝟙 (Spec (CommRingCat.of S))), pullback.condition⟩
    (GoodReductionJacobian.schemeHomOverComp (pullback.snd f (𝟙 (Spec (CommRingCat.of S)))) rfl x))
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at key
  rw [key]
  have h1 : GoodReductionJacobian.schemeHomOverComp
      (pullback.lift (L.one (𝟙 (Spec (CommRingCat.of S)))).1 (𝟙 (Spec (CommRingCat.of S))) (by rw [(L.one _).2, Category.comp_id])) hψ
      ⟨pullback.fst f (𝟙 (Spec (CommRingCat.of S))), pullback.condition⟩ = L.one (𝟙 (Spec (CommRingCat.of S))) :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, pullback.lift_fst])
  have h2 : GoodReductionJacobian.schemeHomOverComp
      (pullback.lift (L.one (𝟙 (Spec (CommRingCat.of S)))).1 (𝟙 (Spec (CommRingCat.of S))) (by rw [(L.one _).2, Category.comp_id])) hψ
      (GoodReductionJacobian.schemeHomOverComp (pullback.snd f (𝟙 (Spec (CommRingCat.of S)))) rfl x) = x :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, GoodReductionJacobian.schemeHomOverComp_coe,
      ← Category.assoc, pullback.lift_snd, Category.id_comp])
  rw [h1, h2, L.one_mul]

end S_AlgebraicGeometry_Polarisation_lift_one_comp_translate_comp_fst
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_lift_one_comp_translate_comp_fst (solution)
