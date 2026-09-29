-- Prove2me | solution 1 for AlgebraicGeometry.eq_of_comp_eq_of_base_closedPoint_eq_of_isIso_residueFieldMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/25b1181a-5105-50d9-a076-40a5d13e8749

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_eq_of_comp_eq_of_base_closedPoint_eq_of_isIso_residueFieldMap

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {K : Type u} [Field K] {X Y : Scheme.{u}} (f : X ⟶ Y) (u u' : Spec (CommRingCat.of K) ⟶ X) (h : u ≫ f = u' ≫ f)
    (hpt : u.base (IsLocalRing.closedPoint K) = u'.base (IsLocalRing.closedPoint K))
    (hκ : IsIso (f.residueFieldMap (u.base (IsLocalRing.closedPoint K)))) :
    u = u' := by
  obtain ⟨⟨x, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective u
  obtain ⟨⟨x', φ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective u'
  have hx : x = x' := by
    simpa [Scheme.SpecToEquivOfField, Scheme.fromSpecResidueField_apply] using hpt
  subst hx
  have hx0 : ((Scheme.SpecToEquivOfField K X).symm ⟨x, φ⟩).base (IsLocalRing.closedPoint K) = x := by
    simp [Scheme.SpecToEquivOfField, Scheme.fromSpecResidueField_apply]
  rw [hx0] at hκ

  have key : (Scheme.SpecToEquivOfField K Y).symm ⟨f.base x, f.residueFieldMap x ≫ φ⟩ =
      (Scheme.SpecToEquivOfField K Y).symm ⟨f.base x, f.residueFieldMap x ≫ φ'⟩ := by
    simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk, Spec.map_comp, Category.assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    simpa [Scheme.SpecToEquivOfField] using h
  have key' := (Scheme.SpecToEquivOfField K Y).symm.injective key
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at key'
  have hφ : φ = φ' := by
    haveI := hκ
    exact (cancel_epi (f.residueFieldMap x)).mp key'
  subst hφ
  rfl

end S_AlgebraicGeometry_eq_of_comp_eq_of_base_closedPoint_eq_of_isIso_residueFieldMap
end P2MW
export P2MW.S_AlgebraicGeometry_eq_of_comp_eq_of_base_closedPoint_eq_of_isIso_residueFieldMap (solution)
