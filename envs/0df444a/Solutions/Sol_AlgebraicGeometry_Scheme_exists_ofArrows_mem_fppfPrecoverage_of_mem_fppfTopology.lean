-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_ofArrows_mem_fppfPrecoverage_of_mem_fppfTopology
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/6fcea0e9-27b0-56a3-9ffe-350513063a2d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_ofArrows_mem_fppfPrecoverage_of_mem_fppfTopology

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {R : CommRingCat.{u}} (S : Sieve (Spec R)) (hS : S ∈ Scheme.fppfTopology (Spec R)) :
    ∃ (ι : Type u) (_ : Finite ι) (A : ι → CommRingCat.{u}) (φ : ∀ i, R ⟶ A i),
      Presieve.ofArrows (fun i => Spec (A i)) (fun i => Spec.map (φ i)) ∈ Scheme.fppfPrecoverage (Spec R) ∧
      ∀ i, S (Spec.map (φ i)) := by
  classical
  haveI : (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}).ContainsIdentities :=
    ⟨fun X => ⟨inferInstance, inferInstance⟩⟩
  haveI : (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}).RespectsIso :=
    MorphismProperty.RespectsIso.inf _ _
  haveI : Scheme.fppfPrecoverage.{u}.HasIsos := by
    dsimp only [Scheme.fppfPrecoverage]; infer_instance
  haveI : Scheme.fppfPrecoverage.{u}.HasPullbacks := by
    dsimp only [Scheme.fppfPrecoverage]; infer_instance

  obtain ⟨T, hT, hTS⟩ :=
    (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition (J := Scheme.fppfPrecoverage)).mp hS
  obtain ⟨E, rfl⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hT
  have hE : Presieve.ofArrows E.X E.f ∈ Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation) (Spec R) :=
    E.mem₀
  rw [Scheme.ofArrows_mem_precoverage_iff] at hE
  obtain ⟨hsurj, hP⟩ := hE
  haveI hflat : ∀ k, Flat (E.f k) := fun k => (hP k).1
  haveI hlfp : ∀ k, LocallyOfFinitePresentation (E.f k) := fun k => (hP k).2

  have key : ∀ x : Spec R, ∃ (k : E.I₀) (U : (E.X k).affineOpens), x ∈ Set.range (U.1.ι ≫ E.f k).base := by
    intro x
    obtain ⟨k, y, rfl⟩ := hsurj x
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      (E.X k).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact ⟨k, ⟨U, hU⟩, ⟨⟨y, hyU⟩, rfl⟩⟩
  choose k U hxU using key

  have hopen : ∀ x : Spec R, IsOpen (Set.range ((U x).1.ι ≫ E.f (k x)).base) := fun x =>
    ((E.f (k x)).isOpenMap.comp (U x).1.ι.isOpenMap).isOpen_range
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : Spec R => Set.range ((U x).1.ι ≫ E.f (k x)).base) hopen
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩)

  let W : {x // x ∈ t} → Scheme.{u} := fun z => ((U z.1).1 : Scheme.{u})
  haveI hWaff : ∀ z, IsAffine (W z) := fun z => (U z.1).2
  let g : ∀ z, W z ⟶ Spec R := fun z => (U z.1).1.ι ≫ E.f (k z.1)
  let A : {x // x ∈ t} → CommRingCat.{u} := fun z => Γ(W z, ⊤)
  let φ : ∀ z, R ⟶ A z := fun z => Spec.preimage ((W z).isoSpec.inv ≫ g z)
  have hφ : ∀ z, Spec.map (φ z) = (W z).isoSpec.inv ≫ g z := fun z => Spec.map_preimage _
  refine ⟨{x // x ∈ t}, inferInstance, A, φ, ?_, fun z => ?_⟩
  · change Presieve.ofArrows _ _ ∈ Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation) (Spec R)
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun z => ?_⟩
    · obtain ⟨x', hx't, hx⟩ : ∃ x' ∈ t, x ∈ Set.range ((U x').1.ι ≫ E.f (k x')).base := by
        simpa only [Set.mem_iUnion, exists_prop] using ht (Set.mem_univ x)
      obtain ⟨y, rfl⟩ := hx
      refine ⟨⟨x', hx't⟩, (W ⟨x', hx't⟩).isoSpec.hom.base y, ?_⟩
      rw [hφ]
      change ((W ⟨x', hx't⟩).isoSpec.hom ≫ (W ⟨x', hx't⟩).isoSpec.inv ≫ g ⟨x', hx't⟩).base y = _
      rw [Iso.hom_inv_id_assoc]
    · rw [hφ]
      exact ⟨inferInstance, inferInstance⟩
  · rw [hφ, ← Category.assoc]
    exact S.downward_closed (hTS _ _ (Presieve.ofArrows.mk (k z.1))) _

end S_AlgebraicGeometry_Scheme_exists_ofArrows_mem_fppfPrecoverage_of_mem_fppfTopology
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_ofArrows_mem_fppfPrecoverage_of_mem_fppfTopology (solution)
