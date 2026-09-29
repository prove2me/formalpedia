-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.of_forall_pullback_iso_of_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/1105e21e-7bb3-5162-999b-fb80fbb481e5

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_of_forall_pullback_iso_of_isOpenImmersion

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

theorem solution
    {Y : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}} (ι : ∀ i, X i ⟶ Y) [∀ i, IsOpenImmersion (ι i)]
    (hι : ∀ y : ↥Y, ∃ (i : I) (x : ↥(X i)), (ι i).base x = y)
    (M : ∀ i, (X i).Modules) (hM : ∀ i, Scheme.Modules.IsInvertible (M i))
    (Mg : Y.Modules) (ψ : ∀ i, (Scheme.Modules.pullback (ι i)).obj Mg ≅ M i) :
    Scheme.Modules.IsInvertible Mg := by
  refine ⟨fun y => ?_⟩
  obtain ⟨i, x, rfl⟩ := hι y
  obtain ⟨U, hxU, ⟨eU⟩⟩ := (hM i).exists_trivialization x
  let e := Scheme.Hom.isoImage (ι i) U
  have hV : ((ι i) ''ᵁ U).ι = e.inv ≫ U.ι ≫ ι i :=
    (Iso.eq_inv_comp e).mpr (Scheme.Hom.isoImage_hom_ι (ι i) U)
  refine ⟨(ι i) ''ᵁ U, (Scheme.Hom.apply_mem_image_iff (ι i)).mpr hxU, ⟨?_⟩⟩
  exact (Scheme.Modules.pullbackCongr hV).app Mg ≪≫
    ((Scheme.Modules.pullbackComp e.inv (U.ι ≫ ι i)).app Mg).symm ≪≫
    (Scheme.Modules.pullback e.inv).mapIso
      (((Scheme.Modules.pullbackComp U.ι (ι i)).app Mg).symm ≪≫ (Scheme.Modules.pullback U.ι).mapIso (ψ i) ≪≫ eU) ≪≫
    Scheme.Modules.pullbackUnitIso e.inv

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_of_forall_pullback_iso_of_isOpenImmersion
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_of_forall_pullback_iso_of_isOpenImmersion (solution)
