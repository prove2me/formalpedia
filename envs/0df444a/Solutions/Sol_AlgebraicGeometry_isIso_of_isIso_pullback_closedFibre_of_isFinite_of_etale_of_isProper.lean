-- Prove2me | solution 1 for AlgebraicGeometry.isIso_of_isIso_pullback_closedFibre_of_isFinite_of_etale_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/252b771d-45b2-53e9-b1a0-d0d5c045927a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIso_of_isIso_pullback_closedFibre_of_isFinite_of_etale_of_isProper

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace F1dE121

private theorem exists_specializes_over_closedPoint {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [UniversallyClosed f] (x : X) :
    ∃ x' : X, x ⤳ x' ∧ f.base x' = IsLocalRing.closedPoint R := by
  have hclosed : IsClosed (f.base '' closure {x}) := f.isClosedMap _ isClosed_closure
  have hfx : f.base x ∈ f.base '' closure {x} := ⟨x, subset_closure rfl, rfl⟩
  have hspec : f.base x ⤳ IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint _
  have hmem : IsLocalRing.closedPoint R ∈ f.base '' closure {x} := hspec.mem_closed hclosed hfx
  obtain ⟨x', hx', hfx'⟩ := hmem
  exact ⟨x', specializes_iff_mem_closure.mpr hx', hfx'⟩

private theorem closedPoint_mem_range_residue {R : Type u} [CommRing R] [IsLocalRing R] :
    IsLocalRing.closedPoint R ∈
      Set.range (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))).base := by
  refine ⟨IsLocalRing.closedPoint (IsLocalRing.ResidueField R), ?_⟩
  show PrimeSpectrum.comap (IsLocalRing.residue R) (IsLocalRing.closedPoint _) = _
  exact IsLocalRing.comap_closedPoint (IsLocalRing.residue R)

private theorem apply_eq_of_specializes {α β : Type*} [TopologicalSpace α] {g : α → β}
    (hg : IsLocallyConstant g) {x x' : α} (h : x ⤳ x') : g x' = g x := by
  have hclopen : IsClopen (g ⁻¹' {g x}) := hg.isClopen_fiber (g x)
  exact h.mem_closed hclopen.isClosed (Set.mem_singleton (g x))

end F1dE121

open F1dE121 in

theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X U : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (π : U ⟶ X) [IsFinite π] [AlgebraicGeometry.Etale π]
    (hk : IsIso (pullback.snd π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))))) :
    IsIso π := by
  set ι := pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) with hι
  rw [Scheme.Hom.isIso_iff_finrank_eq]
  have hlc : IsLocallyConstant (Scheme.Hom.finrank π) := Scheme.Hom.isLocallyConstant_finrank π

  have hfib : ∀ y, Scheme.Hom.finrank π (ι.base y) = 1 := by
    intro y
    have h := Scheme.Hom.finrank_pullback_snd π ι y
    rw [Scheme.Hom.finrank_eq_one_of_isIso] at h
    exact h.symm
  funext x
  obtain ⟨x', hxx', hfx'⟩ := F1dE121.exists_specializes_over_closedPoint f x

  have hx'range : x' ∈ Set.range ι.base := by
    rw [hι, Scheme.Pullback.range_fst]
    show f.base x' ∈ Set.range _
    rw [hfx']
    exact F1dE121.closedPoint_mem_range_residue
  obtain ⟨y, rfl⟩ := hx'range
  rw [← F1dE121.apply_eq_of_specializes hlc hxx', hfib y]
  rfl

end S_AlgebraicGeometry_isIso_of_isIso_pullback_closedFibre_of_isFinite_of_etale_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_isIso_of_isIso_pullback_closedFibre_of_isFinite_of_etale_of_isProper (solution)
