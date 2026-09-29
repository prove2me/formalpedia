-- Prove2me | solution 1 for AlgebraicGeometry.epi_specMap_of_injective_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/be69fdde-68b1-5db4-a16d-aa7ada36114e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_epi_specMap_of_injective_of_finite

set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.IdealSheafData.ideal_bot LocallyRingedSpace Surjective Scheme.ker_of_isAffine Scheme.Hom Scheme.forgetToLocallyRingedSpace Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme SheafedSpace.epi_of_base_surjective_of_stalk_mono PresheafedSpace Scheme.Hom.app_injective IsSchemeTheoreticallyDominant LocallyRingedSpace.forgetToSheafedSpace PresheafedSpace.congr_app SheafedSpace.forgetToPresheafedSpace SheafedSpace isSchemeTheoreticallyDominant_iff Scheme.IdealSheafData.ofIdealTop_ideal Scheme.IdealSheafData Scheme.ΓSpecIso"
p2m_open "AlgebraicGeometry"

namespace PresheafedSpace p2m_export "AlgebraicGeometry.PresheafedSpace" "Hom ext Γ congr_app" end PresheafedSpace
p2m_open_scoped "AlgebraicGeometry.PresheafedSpace" in

theorem PresheafedSpace.epi_of_base_surjective_of_mono_c_app {C : Type*} [Category C]
    {X Y : PresheafedSpace C} (f : X ⟶ Y)
    (h₁ : Function.Surjective f.base) (h₂ : ∀ U, Mono (f.c.app U)) : Epi f := by
  constructor
  intro Z ⟨g, gc⟩ ⟨h, hc⟩ e
  obtain rfl : g = h := ConcreteCategory.hom_ext _ _ fun y => by
    rw [← (h₁ y).choose_spec]
    simpa using congr(($e).base.hom (h₁ y).choose)
  suffices hgh : gc = hc by subst hgh; rfl
  refine NatTrans.ext (funext fun U => ?_)
  have key := PresheafedSpace.congr_app e U
  dsimp at key
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at key
  exact (cancel_mono (f.c.app _)).mp key

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "IdealSheafData.ideal_bot ker_of_isAffine Hom Γ forgetToLocallyRingedSpace ΓSpecIso_inv_naturality Hom.app_injective Opens IdealSheafData.ofIdealTop_ideal IdealSheafData ΓSpecIso" end Scheme
p2m_open_scoped "AlgebraicGeometry.Scheme" in

theorem Scheme.epi_of_surjective_of_app_injective {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    (h : ∀ U : Y.Opens, Function.Injective (f.app U)) : Epi f := by
  apply CategoryTheory.Functor.epi_of_epi_map Scheme.forgetToLocallyRingedSpace
  apply CategoryTheory.Functor.epi_of_epi_map LocallyRingedSpace.forgetToSheafedSpace
  apply CategoryTheory.Functor.epi_of_epi_map SheafedSpace.forgetToPresheafedSpace
  apply PresheafedSpace.epi_of_base_surjective_of_mono_c_app _ ‹Surjective f›.surj
  intro U
  exact ConcreteCategory.mono_of_injective (f.app (unop U)) (h (unop U))

theorem isSchemeTheoreticallyDominant_specMap_of_injective {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (hφ : Function.Injective φ) : IsSchemeTheoreticallyDominant (Spec.map φ) := by
  rw [isSchemeTheoreticallyDominant_iff, Scheme.ker_of_isAffine]
  have happ : Function.Injective (Spec.map φ).appTop := by
    have h1 : (Spec.map φ).appTop = (Scheme.ΓSpecIso A).hom ≫ φ ≫ (Scheme.ΓSpecIso B).inv := by
      rw [Scheme.ΓSpecIso_inv_naturality, Iso.hom_inv_id_assoc]
    rw [h1]
    intro x y hxy
    simp only [CategoryTheory.comp_apply] at hxy
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).hom).1
      (hφ ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).inv).1 hxy))
  rw [(RingHom.injective_iff_ker_eq_bot _).mp happ]
  ext U : 2
  simp [Scheme.IdealSheafData.ofIdealTop_ideal, Scheme.IdealSheafData.ideal_bot]

end AlgebraicGeometry

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_epi_specMap_of_injective_of_finite.AlgebraicGeometry in
theorem solution
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : Function.Injective φ) (hfin : φ.Finite) :
    CategoryTheory.Epi (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) := by
  haveI : Surjective (Spec.map (CommRingCat.ofHom φ)) :=
    ⟨hfin.to_isIntegral.comap_surjective hφ⟩
  haveI := isSchemeTheoreticallyDominant_specMap_of_injective (CommRingCat.ofHom φ) hφ
  exact Scheme.epi_of_surjective_of_app_injective _ ((Spec.map (CommRingCat.ofHom φ)).app_injective)

end S_AlgebraicGeometry_epi_specMap_of_injective_of_finite
end P2MW
export P2MW.S_AlgebraicGeometry_epi_specMap_of_injective_of_finite (solution)
