-- Prove2me | solution 1 for AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isAffineHom_proj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/b50d133e-5d53-5285-a28a-ed07de294979

import Mathlib
import Theorems.Thm_HomogeneousIdeal_exists_homogeneous_pos_mem_forall_notMem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isAffineHom_proj

universe u v

open CategoryTheory

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme Proj.mem_basicOpen Proj Proj.isAffineOpen_basicOpen Proj.basicOpen IsAffineOpen IsAffineHom"
p2m_open "AlgebraicGeometry"
section ProjOpen
variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
namespace Proj p2m_export "AlgebraicGeometry.Proj" "mem_basicOpen isAffineOpen_basicOpen basicOpen" end Proj
p2m_open_scoped "AlgebraicGeometry.Proj" in

theorem Proj.exists_basicOpen_le_forall_mem_of_finset (U : (Proj 𝒜).Opens) (S : Finset (Proj 𝒜))
    (hS : ∀ x ∈ S, x ∈ U) :
    ∃ (n : ℕ) (f : A), 0 < n ∧ f ∈ 𝒜 n ∧ Proj.basicOpen 𝒜 f ≤ U ∧ ∀ x ∈ S, x ∈ Proj.basicOpen 𝒜 f := by
  classical
  set Z : Set (Proj 𝒜) := (U : Set (Proj 𝒜))ᶜ with hZdef
  have hZ : IsClosed Z := U.isOpen.isClosed_compl
  set J : HomogeneousIdeal 𝒜 := ProjectiveSpectrum.vanishingIdeal Z with hJdef
  have hZJ : ProjectiveSpectrum.zeroLocus 𝒜 (J : Set A) = Z := by
    rw [hJdef, ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact hZ.closure_eq
  have havoid : ∀ p ∈ S.image (fun x : Proj 𝒜 => x.asHomogeneousIdeal),
      ¬ (J ⊓ HomogeneousIdeal.irrelevant 𝒜 ≤ p) := by
    intro p hp hle
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hp
    change (J ⊓ HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ x.asHomogeneousIdeal.toIdeal at hle
    rw [HomogeneousIdeal.toIdeal_inf, x.isPrime.inf_le] at hle
    rcases hle with hle | hle
    ·
      have hxZ : x ∈ Z := by
        rw [← hZJ]
        exact (ProjectiveSpectrum.mem_zeroLocus 𝒜 x _).mpr hle
      exact hxZ (hS x hxS)
    · exact x.not_irrelevant_le hle
  obtain ⟨n, f, hn, hfn, hfI, hf⟩ :=
    (J ⊓ HomogeneousIdeal.irrelevant 𝒜).exists_homogeneous_pos_mem_forall_notMem inf_le_right
      (S.image fun x : Proj 𝒜 => x.asHomogeneousIdeal)
      (fun p hp => by
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hp
        exact x.isPrime)
      havoid
  refine ⟨n, f, hn, hfn, ?_, ?_⟩
  · intro y hy
    by_contra hyU
    have hyZ : y ∈ Z := hyU
    rw [← hZJ] at hyZ
    have hfJ : f ∈ J := (inf_le_left : J ⊓ HomogeneousIdeal.irrelevant 𝒜 ≤ J) hfI
    exact (Proj.mem_basicOpen 𝒜 f y).mp hy ((ProjectiveSpectrum.mem_zeroLocus 𝒜 y _).mp hyZ hfJ)
  · intro x hx
    rw [Proj.mem_basicOpen]
    exact hf _ (Finset.mem_image_of_mem _ hx)

end ProjOpen
end AlgebraicGeometry

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isAffineHom_proj.AlgebraicGeometry in
theorem solution
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {X : AlgebraicGeometry.Scheme.{u}} (ι : X ⟶ AlgebraicGeometry.Proj 𝒜) [AlgebraicGeometry.IsAffineHom ι]
    (S : Finset X) :
    ∃ W : X.Opens, AlgebraicGeometry.IsAffineOpen W ∧ ∀ x ∈ S, x ∈ W := by
  classical
  obtain ⟨n, f, hn, hfn, -, hmem⟩ :=
    AlgebraicGeometry.Proj.exists_basicOpen_le_forall_mem_of_finset 𝒜 ⊤ (S.image ι.base) (fun _ _ => trivial)
  exact ⟨ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f, (AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒜 f hfn hn).preimage ι,
    fun x hx => hmem _ (Finset.mem_image_of_mem _ hx)⟩

end S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isAffineHom_proj
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isAffineHom_proj (solution)
