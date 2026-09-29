-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.dense_setOf_exists_section_of_henselianLocalRing_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/657dcbb0-4581-5050-8fc0-9a23be320220

import Mathlib
import Theorems.Thm_AlgebraicGeometry_dense_setOf_exists_section_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_dense_setOf_exists_section_of_henselianLocalRing_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] :
    Dense {x : {x : T // t.base x = IsLocalRing.closedPoint R} |
      ∃ s : Spec (CommRingCat.of R) ⟶ T, s ≫ t = 𝟙 _ ∧ s.base (IsLocalRing.closedPoint R) = x.1} := by
  classical
  let κ := IsLocalRing.ResidueField R
  let res : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))

  let ι : pullback t res ⟶ T := pullback.fst t res
  let tκ : pullback t res ⟶ Spec (CommRingCat.of κ) := pullback.snd t res
  have hrange_res : Set.range res.base = {IsLocalRing.closedPoint R} := by
    ext y
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, rfl⟩
      exact IsLocalRing.PrimeSpectrum.comap_residue R z
    · rintro rfl
      exact ⟨IsLocalRing.closedPoint κ, IsLocalRing.PrimeSpectrum.comap_residue R _⟩
  have hrange : Set.range ι.base = {x : T | t.base x = IsLocalRing.closedPoint R} := by
    change Set.range (pullback.fst t res).base = _
    rw [Scheme.Pullback.range_fst, hrange_res]
    rfl

  let S := {x : T // t.base x = IsLocalRing.closedPoint R}
  have hmem : ∀ y, t.base (ι.base y) = IsLocalRing.closedPoint R := fun y => by
    have : ι.base y ∈ Set.range ι.base := ⟨y, rfl⟩
    rw [hrange] at this
    exact this
  let g : ↥(pullback t res) → S := fun y => ⟨ι.base y, hmem y⟩
  have hgc : Continuous g := ι.base.hom.continuous.subtype_mk _
  have hgs : Function.Surjective g := by
    rintro ⟨x, hx⟩
    have : x ∈ Set.range ι.base := by rw [hrange]; exact hx
    obtain ⟨y, rfl⟩ := this
    exact ⟨y, rfl⟩

  have hdense := AlgebraicGeometry.dense_setOf_exists_section_of_isAlgClosed tκ

  refine Dense.mono ?_ ((hgs.denseRange).dense_image hgc hdense)
  rintro _ ⟨y, ⟨s₀, hs₀, rfl⟩, rfl⟩
  have hx₀ : (s₀ ≫ ι) ≫ t = Spec.map (CommRingCat.ofHom (algebraMap R κ)) := by
    rw [Category.assoc, pullback.condition, reassoc_of% hs₀]
    rfl
  obtain ⟨s, hs, hs'⟩ := AlgebraicGeometry.Smooth.exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing t (s₀ ≫ ι) hx₀
  refine ⟨s, hs, ?_⟩
  change s.base (IsLocalRing.closedPoint R) = ι.base (s₀.base (IsLocalRing.closedPoint κ))
  have h1 : (Spec.map (CommRingCat.ofHom (algebraMap R κ))).base (IsLocalRing.closedPoint κ) = IsLocalRing.closedPoint R :=
    IsLocalRing.PrimeSpectrum.comap_residue R _
  rw [← h1, ← Scheme.Hom.comp_apply, hs', Scheme.Hom.comp_apply]

end S_AlgebraicGeometry_Smooth_dense_setOf_exists_section_of_henselianLocalRing_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_dense_setOf_exists_section_of_henselianLocalRing_of_isAlgClosed (solution)
