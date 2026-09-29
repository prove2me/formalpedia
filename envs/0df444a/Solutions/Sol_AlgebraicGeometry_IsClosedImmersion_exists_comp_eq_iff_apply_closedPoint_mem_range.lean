-- Prove2me | solution 1 for AlgebraicGeometry.IsClosedImmersion.exists_comp_eq_iff_apply_closedPoint_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/6038aaa0-ff8c-5610-9e7f-95deeaceaccf

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_iff_apply_closedPoint_mem_range

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {K : Type u} [Field K] (x : Spec (CommRingCat.of K) ⟶ X) :
    (∃ z : Spec (CommRingCat.of K) ⟶ Z, z ≫ i = x) ↔
      x.base (IsLocalRing.closedPoint K) ∈ Set.range i.base := by
  constructor
  · rintro ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  · intro hmem

    have hpt : ∀ p : ↥(Spec (CommRingCat.of K)), p = IsLocalRing.closedPoint K := fun p =>
      ((PrimeSpectrum.instUnique (R := (CommRingCat.of K))).uniq p).trans
        ((PrimeSpectrum.instUnique (R := (CommRingCat.of K))).uniq (IsLocalRing.closedPoint K)).symm
    have hsurj : Surjective (pullback.fst x i) := by
      refine ⟨fun p => ?_⟩
      obtain ⟨y, hy⟩ := hmem
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := x) (g := i)
        (IsLocalRing.closedPoint K) y hy.symm
      exact ⟨w, by rw [hpt p]; exact hw⟩
    have : IsIso (pullback.fst x i) := isIso_of_isClosedImmersion_of_surjective _
    refine ⟨inv (pullback.fst x i) ≫ pullback.snd x i, ?_⟩
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

end S_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_iff_apply_closedPoint_mem_range
end P2MW
export P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_comp_eq_iff_apply_closedPoint_mem_range (solution)
