-- Prove2me | solution 1 for AlgebraicGeometry.universallyInjective_of_forall_geometricFibre_universallyInjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/4d883764-98f3-5888-9145-0a968c00f3a3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_universallyInjective_of_forall_geometricFibre_universallyInjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {S : Type u} [CommRing S] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of S)) (q : Y ⟶ Spec (CommRingCat.of S))
    (φ : X ⟶ Y) (hφ : φ ≫ q = p)
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k),
      ∃ (X' Y' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of k)) (q' : Y' ⟶ Spec (CommRingCat.of k))
        (φ' : X' ⟶ Y') (iX : X' ⟶ X) (iY : Y' ⟶ Y),
        IsPullback iX p' p (Spec.map (CommRingCat.ofHom sk)) ∧
        IsPullback iY q' q (Spec.map (CommRingCat.ofHom sk)) ∧
        φ' ≫ q' = p' ∧ iX ≫ φ = φ' ≫ iY ∧ UniversallyInjective φ') :
    UniversallyInjective φ := by
  classical
  rw [UniversallyInjective.iff_diagonal]
  refine ⟨fun z => ?_⟩

  let K : Type u := AlgebraicClosure ((pullback φ φ).residueField z)
  obtain ⟨zk, hzk⟩ : ∃ zk : Spec (CommRingCat.of K) ⟶ pullback φ φ, ∀ t : ↥(Spec (CommRingCat.of K)), zk t = z :=
    ⟨Spec.map (CommRingCat.ofHom (algebraMap ((pullback φ φ).residueField z) K)) ≫ (pullback φ φ).fromSpecResidueField z,
      fun t => by
        simp only [Scheme.Hom.comp_apply]
        exact Scheme.fromSpecResidueField_apply z _⟩
  let sk : S →+* K := (Spec.preimage (zk ≫ pullback.fst φ φ ≫ p)).hom
  have hsk : Spec.map (CommRingCat.ofHom sk) = zk ≫ pullback.fst φ φ ≫ p := by
    simp only [sk, CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨X', Y', p', q', φ', iX, iY, hX, hY, hφ', hcomm, hinj⟩ := hfib K sk

  have h1 : (zk ≫ pullback.fst φ φ) ≫ p = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom sk) := by rw [Category.id_comp, hsk, Category.assoc]
  have hpp : pullback.snd φ φ ≫ p = pullback.fst φ φ ≫ p := by
    rw [← hφ, ← Category.assoc, ← Category.assoc, pullback.condition]
  have h2 : (zk ≫ pullback.snd φ φ) ≫ p = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom sk) := by
    rw [Category.id_comp, hsk, Category.assoc, hpp]
  let x₁ : Spec (CommRingCat.of K) ⟶ X' := hX.lift (zk ≫ pullback.fst φ φ) (𝟙 _) h1
  let x₂ : Spec (CommRingCat.of K) ⟶ X' := hX.lift (zk ≫ pullback.snd φ φ) (𝟙 _) h2
  have hx₁ : x₁ ≫ iX = zk ≫ pullback.fst φ φ := hX.lift_fst _ _ _
  have hx₂ : x₂ ≫ iX = zk ≫ pullback.snd φ φ := hX.lift_fst _ _ _
  have hx₁' : x₁ ≫ p' = 𝟙 _ := hX.lift_snd _ _ _
  have hx₂' : x₂ ≫ p' = 𝟙 _ := hX.lift_snd _ _ _

  have heq : x₁ ≫ φ' = x₂ ≫ φ' := by
    apply hY.hom_ext
    · have h12 : x₁ ≫ φ' ≫ iY = x₂ ≫ φ' ≫ iY := by
        rw [← hcomm, ← Category.assoc, hx₁, ← Category.assoc, hx₂, Category.assoc, Category.assoc, pullback.condition]
      simpa only [Category.assoc] using h12
    · rw [Category.assoc, Category.assoc, hφ', hx₁', hx₂']

  let z' : Spec (CommRingCat.of K) ⟶ pullback φ' φ' := pullback.lift x₁ x₂ heq
  let c : pullback φ' φ' ⟶ pullback φ φ :=
    pullback.lift (pullback.fst φ' φ' ≫ iX) (pullback.snd φ' φ' ≫ iX)
      (by rw [Category.assoc, Category.assoc, hcomm, ← Category.assoc, pullback.condition, Category.assoc])
  have hcz : z' ≫ c = zk := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hx₁]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, hx₂]
  have hcΔ : pullback.diagonal φ' ≫ c = iX ≫ pullback.diagonal φ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.diagonal_fst, Category.id_comp, Category.assoc,
        pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.diagonal_snd, Category.id_comp, Category.assoc,
        pullback.diagonal_snd, Category.comp_id]

  haveI := hinj
  have hsurj' : Function.Surjective (pullback.diagonal φ') := ((UniversallyInjective.iff_diagonal φ').mp hinj).1
  let t : ↥(Spec (CommRingCat.of K)) := default
  obtain ⟨x', hx'⟩ := hsurj' (z' t)
  refine ⟨iX x', ?_⟩
  have := congrArg (fun ψ => (ψ : pullback φ' φ' ⟶ pullback φ φ) (pullback.diagonal φ' x')) (rfl : c = c)
  calc pullback.diagonal φ (iX x') = (iX ≫ pullback.diagonal φ) x' := by rw [Scheme.Hom.comp_apply]
    _ = (pullback.diagonal φ' ≫ c) x' := by rw [hcΔ]
    _ = c (z' t) := by rw [Scheme.Hom.comp_apply, hx']
    _ = zk t := by rw [← Scheme.Hom.comp_apply, hcz]
    _ = z := hzk t

end S_AlgebraicGeometry_universallyInjective_of_forall_geometricFibre_universallyInjective
end P2MW
export P2MW.S_AlgebraicGeometry_universallyInjective_of_forall_geometricFibre_universallyInjective (solution)
