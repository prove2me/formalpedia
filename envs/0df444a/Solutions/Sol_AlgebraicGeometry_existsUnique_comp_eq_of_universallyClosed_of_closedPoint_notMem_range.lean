-- Prove2me | solution 1 for AlgebraicGeometry.existsUnique_comp_eq_of_universallyClosed_of_closedPoint_notMem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f832a471-71dd-5441-bc3b-3ecc1347dfee

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_existsUnique_comp_eq_of_universallyClosed_of_closedPoint_notMem_range

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

open AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X Xf X' T : Scheme.{u}} (g : X ⟶ Spec (.of R))
    (i : Xf ⟶ X) [IsOpenImmersion i] (j : X' ⟶ X)
    (hcover : Set.range i ∪ Set.range j = Set.univ)
    (hempty : IsLocalRing.closedPoint R ∉ Set.range (j ≫ g))
    (f : T ⟶ X) [UniversallyClosed (f ≫ g)] :
    ∃! f' : T ⟶ Xf, f' ≫ i = f := by
  have hicl : IsClosed (Set.range i)ᶜ := by
    rw [isClosed_compl_iff, ← Scheme.Hom.coe_opensRange]
    exact i.opensRange.isOpen
  have hrange : Set.range f ⊆ Set.range i := by
    by_contra hne
    obtain ⟨_, ⟨t, rfl⟩, ht⟩ := Set.not_subset.mp hne

    have hZ : IsClosed (f ⁻¹' (Set.range i)ᶜ) := hicl.preimage f.continuous
    have himg : IsClosed ((f ≫ g) '' (f ⁻¹' (Set.range i)ᶜ)) := (f ≫ g).isClosedMap _ hZ
    have hmem : IsLocalRing.closedPoint R ∈ (f ≫ g) '' (f ⁻¹' (Set.range i)ᶜ) :=
      (IsLocalRing.specializes_closedPoint ((f ≫ g) t)).mem_closed himg ⟨t, ht, rfl⟩
    obtain ⟨z, hz, hzc⟩ := hmem
    have hzj : f z ∈ Set.range j :=
      ((hcover.symm ▸ Set.mem_univ (f z) : f z ∈ Set.range i ∪ Set.range j)).resolve_left hz
    obtain ⟨x', hx'⟩ := hzj
    exact hempty ⟨x', by rw [Scheme.Hom.comp_apply, hx', ← Scheme.Hom.comp_apply, hzc]⟩
  refine ⟨IsOpenImmersion.lift i f hrange, IsOpenImmersion.lift_fac i f hrange, fun f' hf' ↦ ?_⟩
  rw [← cancel_mono i, hf', IsOpenImmersion.lift_fac]

end S_AlgebraicGeometry_existsUnique_comp_eq_of_universallyClosed_of_closedPoint_notMem_range
end P2MW
export P2MW.S_AlgebraicGeometry_existsUnique_comp_eq_of_universallyClosed_of_closedPoint_notMem_range (solution)
