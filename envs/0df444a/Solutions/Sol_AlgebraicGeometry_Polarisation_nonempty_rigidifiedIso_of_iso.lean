-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.nonempty_rigidifiedIso_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/de6109fe-fb80-5a8d-b91f-802ed6aa54e0

import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_map_hom_eq_of_pullback_section_trivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_nonempty_rigidifiedIso_of_iso

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Polarisation
open scoped TensorProduct

universe u

theorem solution
    {T : Type u} [CommRing T] {B : Scheme.{u}} (h : B ⟶ Spec (CommRingCat.of T))
    (hΓ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of T)).inv ≫ h.appTop).hom)
    (e : Spec (CommRingCat.of T) ⟶ B) (he : e ≫ h = 𝟙 _)
    (M M' : B.Modules)
    (α : (Scheme.Modules.pullback e).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of T)).ringCatSheaf)
    (α' : (Scheme.Modules.pullback e).obj M' ≅ SheafOfModules.unit (Spec (CommRingCat.of T)).ringCatSheaf)
    (φ₀ : M ≅ M') :
    Nonempty {φ : M ≅ M' // (Scheme.Modules.pullback e).mapIso φ ≪≫ α' = α} := by

  let μ : (Scheme.Modules.pullback e).obj M ≅ (Scheme.Modules.pullback e).obj M :=
    α ≪≫ α'.symm ≪≫ ((Scheme.Modules.pullback e).mapIso φ₀).symm

  obtain ⟨θ, hθ⟩ := AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_map_hom_eq_of_pullback_section_trivial h e he M ⟨α⟩ μ
  refine ⟨⟨θ ≪≫ φ₀, ?_⟩⟩
  ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc, hθ]
  simp [μ]

end S_AlgebraicGeometry_Polarisation_nonempty_rigidifiedIso_of_iso
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_nonempty_rigidifiedIso_of_iso (solution)
