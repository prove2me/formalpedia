-- Prove2me | solution 1 for AlgebraicGeometry.exists_ideal_forall_exists_comp_eq_specMap_comp_iff_le_ker_of_isClosedImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/65f28742-e14c-5336-a514-dea1e2206815

import Mathlib
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_ideal_forall_exists_comp_eq_specMap_iff_forall_map_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_ideal_forall_exists_comp_eq_specMap_comp_iff_le_ker_of_isClosedImmersion

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] {X Z : Scheme.{u}} (ι : Z ⟶ X) [IsClosedImmersion ι]
    (y : Spec (CommRingCat.of R) ⟶ X) :
    ∃ J : Ideal R, ∀ (R' : Type u) [CommRing R'] (ψ : R →+* R'),
      (∃ z : Spec (CommRingCat.of R') ⟶ Z, z ≫ ι = Spec.map (CommRingCat.ofHom ψ) ≫ y) ↔ J ≤ RingHom.ker ψ := by
  haveI : IsClosedImmersion (pullback.snd ι y) := inferInstance
  obtain ⟨J, hJ⟩ := AlgebraicGeometry.IsClosedImmersion.exists_ideal_forall_exists_comp_eq_specMap_iff_forall_map_eq_zero
    (pullback.snd ι y)
  refine ⟨J, fun R' _ ψ => ?_⟩
  constructor
  · rintro ⟨z, hz⟩
    have h1 : ∀ x ∈ J, ψ x = 0 :=
      (hJ R' ψ).mp ⟨pullback.lift z (Spec.map (CommRingCat.ofHom ψ)) hz, pullback.lift_snd _ _ _⟩
    exact fun x hx => (RingHom.mem_ker).mpr (h1 x hx)
  · intro hle
    obtain ⟨t, ht⟩ := (hJ R' ψ).mpr (fun x hx => (RingHom.mem_ker).mp (hle hx))
    exact ⟨t ≫ pullback.fst ι y, by rw [Category.assoc, pullback.condition, ← Category.assoc, ht]⟩

end S_AlgebraicGeometry_exists_ideal_forall_exists_comp_eq_specMap_comp_iff_le_ker_of_isClosedImmersion
end P2MW
export P2MW.S_AlgebraicGeometry_exists_ideal_forall_exists_comp_eq_specMap_comp_iff_le_ker_of_isClosedImmersion (solution)
