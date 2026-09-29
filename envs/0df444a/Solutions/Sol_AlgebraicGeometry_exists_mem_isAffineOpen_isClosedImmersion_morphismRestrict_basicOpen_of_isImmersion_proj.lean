-- Prove2me | solution 1 for AlgebraicGeometry.exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/7edccab3-81fb-564f-9802-2693f8954792

import Mathlib
import Theorems.Thm_HomogeneousIdeal_exists_homogeneous_pos_mem_forall_notMem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsClosedImmersion.of_isPreimmersion Scheme.Hom IsAffine.of_isIso Scheme.Hom.image_preimage_eq_opensRange_inf IsAffine Scheme Proj.mem_basicOpen Proj IsClosedImmersion morphismRestrict_base IsImmersion Proj.isAffineOpen_basicOpen Proj.basicOpen IsAffineOpen Scheme.Opens Scheme.Opens.opensRange_ι"
p2m_open "AlgebraicGeometry"

namespace A1ChartFin

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

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
    · have hxZ : x ∈ Z := by
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

end A1ChartFin

theorem A1ChartFin.isAffineOpen_ι_preimage_of_le {Y : Scheme.{u}} {U V : Y.Opens} (hV : IsAffineOpen V) (h : V ≤ U) :
    IsAffineOpen (U.ι ⁻¹ᵁ V) := by
  have himg : IsAffineOpen (U.ι ''ᵁ (U.ι ⁻¹ᵁ V)) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr h]
    exact hV
  haveI : IsAffine (U.ι ''ᵁ U.ι ⁻¹ᵁ V) := himg
  exact IsAffine.of_isIso (U.ι.isoImage (U.ι ⁻¹ᵁ V)).hom

theorem A1ChartFin.isClosedImmersion_morphismRestrict_of_le_coborderRange {X Y : Scheme.{u}} (ι : X ⟶ Y) [IsImmersion ι]
    (W : Y.Opens) (hW : W ≤ ι.coborderRange) : IsClosedImmersion (ι ∣_ W) := by
  apply IsClosedImmersion.of_isPreimmersion
  have hsub : (Subtype.val : ↥W → ↥Y) ⁻¹' coborder (Set.range ι) = Set.univ :=
    Set.eq_univ_of_forall fun w => hW w.2
  have hcl : (Subtype.val : ↥W → ↥Y) ⁻¹' Set.range ι =
      (Subtype.val : ↥W → ↥Y) ⁻¹' closure (Set.range ι) := by
    conv_lhs => rw [← coborder_inter_closure (s := Set.range ι)]
    rw [Set.preimage_inter, hsub, Set.univ_inter]
  have key : IsClosed ((Subtype.val : ↥W → ↥Y) ⁻¹' Set.range ι) := by
    rw [hcl]; exact isClosed_closure.preimage continuous_subtype_val
  rw [morphismRestrict_base]
  erw [Set.range_restrictPreimage]
  exact key

end AlgebraicGeometry

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj.AlgebraicGeometry in
theorem solution
    {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {X : Scheme.{0}} (ι : X ⟶ Proj 𝒜) [IsImmersion ι] (S : Finset X) :
    ∃ (d : ℕ) (F : A) (_ : F ∈ 𝒜 d), 0 < d ∧ (∀ x ∈ S, x ∈ ι ⁻¹ᵁ Proj.basicOpen 𝒜 F) ∧
      IsAffineOpen (ι ⁻¹ᵁ Proj.basicOpen 𝒜 F) ∧ IsClosedImmersion (ι ∣_ Proj.basicOpen 𝒜 F) := by
  classical
  set U := ι.coborderRange with hU
  set g := ι.liftCoborder with hgdef
  have hg : g ≫ U.ι = ι := ι.liftCoborder_ι
  obtain ⟨n, F, hn, hFn, hle, hmem⟩ := A1ChartFin.Proj.exists_basicOpen_le_forall_mem_of_finset 𝒜 U (S.image ι.base) (by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
    rw [← hg]
    exact (g.base x).2)
  refine ⟨n, F, hFn, hn, ?_, ?_, ?_⟩
  · intro x hx
    exact hmem _ (Finset.mem_image_of_mem _ hx)
  · have H : IsAffineOpen ((g ≫ U.ι) ⁻¹ᵁ Proj.basicOpen 𝒜 F) :=
      (A1ChartFin.isAffineOpen_ι_preimage_of_le (Proj.isAffineOpen_basicOpen 𝒜 F hFn hn) hle).preimage g
    rwa [hg] at H
  · exact A1ChartFin.isClosedImmersion_morphismRestrict_of_le_coborderRange ι _ hle

end S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj
end P2MW
export P2MW.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj (solution)
