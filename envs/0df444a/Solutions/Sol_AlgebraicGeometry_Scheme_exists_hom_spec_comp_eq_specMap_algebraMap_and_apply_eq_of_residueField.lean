-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_hom_spec_comp_eq_specMap_algebraMap_and_apply_eq_of_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/18521623-43ab-55fa-a730-04ad55fbd817

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_hom_spec_comp_eq_specMap_algebraMap_and_apply_eq_of_residueField

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R)) (P : X)
    {Ω : Type u} [Field Ω] [Algebra R Ω]
    (φ : X.residueField P ⟶ CommRingCat.of Ω)
    (hφ : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ c.appTop ≫ X.Γevaluation P ≫ φ =
      CommRingCat.ofHom (algebraMap R Ω)) :
    ∃ xη : Spec (CommRingCat.of Ω) ⟶ X,
      xη ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ∧
      xη.base (IsLocalRing.closedPoint Ω) = P := by
  refine ⟨Spec.map φ ≫ X.fromSpecResidueField P, ?_, ?_⟩
  ·
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← Spec.map_comp]
    congr 1
    rw [Scheme.Spec.algebraMap_residueFieldIso_inv_assoc]

    have hnat : (Spec (CommRingCat.of R)).presheaf.germ ⊤ (c.base P) trivial ≫ (Spec (CommRingCat.of R)).residue (c.base P) ≫
        c.residueFieldMap P = c.appTop ≫ X.Γevaluation P := by
      rw [← Category.assoc]
      exact Scheme.Γevaluation_naturality c P
    slice_lhs 2 4 => rw [hnat]
    simpa [Category.assoc] using hφ
  ·
    show (X.fromSpecResidueField P).base ((Spec.map φ).base (IsLocalRing.closedPoint Ω)) = P
    exact Scheme.fromSpecResidueField_apply P _

end S_AlgebraicGeometry_Scheme_exists_hom_spec_comp_eq_specMap_algebraMap_and_apply_eq_of_residueField
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_hom_spec_comp_eq_specMap_algebraMap_and_apply_eq_of_residueField (solution)
