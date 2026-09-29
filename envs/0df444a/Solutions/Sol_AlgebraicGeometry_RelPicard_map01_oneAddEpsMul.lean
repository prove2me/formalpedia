-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.map01_oneAddEpsMul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8ff3fc5c-4ada-5e79-bfb5-a22c7fa5726b

import Mathlib
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_map01_oneAddEpsMul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem solution
    {R : Type u} [CommRing R] {C C' : Scheme.{u}} {c : C ⟶ Spec (.of R)} {c' : C' ⟶ Spec (.of R)}
    {A : Type u} [CommRing A] [Algebra R A] {𝒱 : C.TwoAffineOpenCover} {𝒲 : C'.TwoAffineOpenCover}
    (f : HomOver (RingHom.id A) (𝒱.pullback c A) (pullback.snd c (specMap R A))
      (𝒲.pullback c' A) (pullback.snd c' (specMap R A)))
    (fε : HomOver (RingHom.id (DualNumber A))
      (𝒱.pullback c (DualNumber A)) (pullback.snd c (specMap R (DualNumber A)))
      (𝒲.pullback c' (DualNumber A)) (pullback.snd c' (specMap R (DualNumber A))))
    (hcomm : fε.hom ≫ (dualNumberThickening A 𝒱 c).hom = (dualNumberThickening A 𝒲 c').hom ≫ f.hom)
    (t : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) :
    fε.map01 (oneAddEpsMul A 𝒱 c t) = oneAddEpsMul A 𝒲 c' (f.map01 t) := by

  have key : ∀ {X' Y' : Scheme.{u}} (φ ψ : Y' ⟶ X') (_ : φ = ψ) (U : X'.Opens) (W : Y'.Opens)
      (e₁ : W ≤ φ ⁻¹ᵁ U) (e₂ : W ≤ ψ ⁻¹ᵁ U), φ.appLE U W e₁ = ψ.appLE U W e₂ := by
    rintro X' Y' φ ψ rfl U W e₁ e₂; rfl
  rw [oneAddEpsMul, oneAddEpsMul, map_add]
  congr 1
  · rw [HomOver.map01_apply]
    exact map_one (fε.hom.appLE _ _ fε.inf_le).hom
  · rw [HomOver.map01_apply]
    refine (map_mul (fε.hom.appLE _ _ fε.inf_le).hom _ _).trans ?_
    congr 1
    · exact fε.appLE_algebraMap fε.inf_le DualNumber.eps
    · rw [HomOver.map01_apply (dualNumberThickening A 𝒱 c), HomOver.map01_apply f,
        HomOver.map01_apply (dualNumberThickening A 𝒲 c'),
        ← CategoryTheory.ConcreteCategory.comp_apply, ← CategoryTheory.ConcreteCategory.comp_apply,
        Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      rw [key _ _ hcomm]

end S_AlgebraicGeometry_RelPicard_map01_oneAddEpsMul
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_map01_oneAddEpsMul (solution)
