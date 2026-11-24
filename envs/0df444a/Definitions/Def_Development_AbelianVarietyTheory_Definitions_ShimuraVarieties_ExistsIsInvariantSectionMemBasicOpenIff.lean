-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsInvariantSectionMemBasicOpenIff
-- name    : Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsInvariantSectionMemBasicOpenIff
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T19:28:32.051887+00:00
-- url     : https://prove2.me/theorems/4d29bd1b-da3f-47c1-80e8-a0a9bd486d19
-- title:
--   Exists Is Invariant Section Mem Basic Open Iff
-- statement:
--   Definitions and structural lemmas for Exists Is Invariant Section Mem Basic Open Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsIsInvariantSectionMemBasicOpenIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Theorems.Thm_GlobalTheory_exists_homogeneous_forall_notMem
import Theorems.Thm_GlobalTheory_exists_homogeneous_notMem_of_not_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
namespace GlobalTheory
section FiniteSets
variable {X Y : Scheme.{u}}
theorem mem_basicOpen_iff_not_mem_primeIdealOf {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    (f : Γ(X, U)) : x ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← hU.fromSpec_preimage_basicOpen]
  change x ∈ X.basicOpen f ↔ hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f
  rw [hU.fromSpec_primeIdealOf]
theorem exists_basicOpen_le_of_finite {U : X.Opens} (hU : IsAffineOpen U) (O : X.Opens)
    {s : Set X} (hs : s.Finite) (hsU : s ⊆ U) (hsO : s ⊆ O) :
    ∃ f : Γ(X, U), s ⊆ X.basicOpen f ∧ X.basicOpen f ≤ O := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
  · exact ⟨0, Set.empty_subset _, by rw [Scheme.basicOpen_zero]; exact bot_le⟩
  have hloc : ∀ y : s, ∃ g : Γ(X, U), X.basicOpen g ≤ O ∧ (y : X) ∈ X.basicOpen g :=
    fun y ↦ hU.exists_basicOpen_le ⟨y, hsO y.2⟩ (hsU y.2)
  choose g hgO hyg using hloc
  let P : X → Ideal Γ(X, U) := fun y ↦ if h : y ∈ U then (hU.primeIdealOf ⟨y, h⟩).asIdeal else ⊤
  have hP : ∀ y (h : y ∈ U), P y = (hU.primeIdealOf ⟨y, h⟩).asIdeal := fun y h ↦ dif_pos h
  have hnot : ¬ ((Ideal.span (Set.range g) : Set Γ(X, U)) ⊆ ⋃ i ∈ (↑hs.toFinset : Set X), P i) := by
    rw [Ideal.subset_union_prime y₀ y₀ (fun i hi _ _ ↦ by
      rw [hP i (hsU (hs.mem_toFinset.1 hi))]; infer_instance)]
    rintro ⟨i, hi, hJ⟩
    have his : i ∈ s := hs.mem_toFinset.1 hi
    have h1 := hyg ⟨i, his⟩
    rw [mem_basicOpen_iff_not_mem_primeIdealOf hU (hsU his), ← hP] at h1
    exact h1 (hJ (Ideal.subset_span ⟨⟨i, his⟩, rfl⟩))
  rw [Set.not_subset] at hnot
  obtain ⟨f, hfJ, hf⟩ := hnot
  refine ⟨f, fun y hy ↦ ?_, fun z hz ↦ ?_⟩
  · rw [SetLike.mem_coe, mem_basicOpen_iff_not_mem_primeIdealOf hU (hsU hy), ← hP]
    exact fun h ↦ hf (Set.mem_biUnion (hs.mem_toFinset.2 hy) h)
  · have hz' : ¬ ∀ g' ∈ (Ideal.span (Set.range g) : Set Γ(X, U)), z ∉ X.basicOpen g' :=
      fun h ↦ h f hfJ hz
    rw [← Scheme.mem_zeroLocus_iff, Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff] at hz'
    push_neg at hz'
    obtain ⟨_, ⟨i, rfl⟩, hzi⟩ := hz'
    exact hgO i hzi
class FiniteSubsetsInAffineOpens (X : Scheme.{u}) : Prop where

  exists_isAffineOpen : ∀ s : Set X, s.Finite → ∃ U : X.Opens, IsAffineOpen U ∧ s ⊆ U
namespace FiniteSubsetsInAffineOpens
instance (priority := 900) of_isAffine [IsAffine X] : FiniteSubsetsInAffineOpens X :=
  ⟨fun _ _ ↦ ⟨⊤, isAffineOpen_top X, Set.subset_univ _⟩⟩
theorem exists_isAffineOpen_le [FiniteSubsetsInAffineOpens X] {s : Set X} (hs : s.Finite)
    (O : X.Opens) (hsO : s ⊆ O) : ∃ U : X.Opens, IsAffineOpen U ∧ s ⊆ U ∧ U ≤ O := by
  obtain ⟨U, hU, hsU⟩ := FiniteSubsetsInAffineOpens.exists_isAffineOpen s hs
  obtain ⟨f, hsf, hfO⟩ := exists_basicOpen_le_of_finite hU O hs hsU hsO
  exact ⟨X.basicOpen f, hU.basicOpen f, hsf, hfO⟩
theorem of_isOpenImmersion (f : X ⟶ Y) [IsOpenImmersion f] [FiniteSubsetsInAffineOpens Y] :
    FiniteSubsetsInAffineOpens X := ⟨fun s hs ↦ by
  obtain ⟨V, hV, hsV, hVf⟩ := exists_isAffineOpen_le (X := Y) (hs.image (fun x : X ↦ f x))
    f.opensRange (by rintro _ ⟨x, -, rfl⟩; exact ⟨x, rfl⟩)
  refine ⟨f ⁻¹ᵁ V, ?_, fun x hx ↦ hsV ⟨x, hx, rfl⟩⟩
  rw [← f.isAffineOpen_iff_of_isOpenImmersion, f.image_preimage_eq_opensRange_inf,
    inf_eq_right.2 hVf]
  exact hV⟩
instance opens [FiniteSubsetsInAffineOpens X] (U : X.Opens) : FiniteSubsetsInAffineOpens U :=
  of_isOpenImmersion U.ι
theorem exists_proj_basicOpen {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {s : Set (Proj 𝒜)} (hs : s.Finite) :
    ∃ n, 0 < n ∧ ∃ f ∈ 𝒜 n, s ⊆ Proj.basicOpen 𝒜 f := by
  classical
  let S : Finset (Ideal A) := hs.toFinset.image (fun x : Proj 𝒜 ↦ x.asHomogeneousIdeal.toIdeal)
  have hmemS : ∀ p ∈ S, ∃ x : Proj 𝒜, p = x.asHomogeneousIdeal.toIdeal := by
    intro p hp
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨x, rfl⟩
  obtain ⟨n, hn, f, hf, hfM⟩ := exists_homogeneous_forall_notMem 𝒜
    (S.filter (fun p ↦ Maximal (· ∈ S) p))
    (fun p hp ↦ by
      obtain ⟨x, rfl⟩ := hmemS p (Finset.mem_filter.1 hp).1
      exact x.isPrime)
    (fun p hp ↦ by
      obtain ⟨x, rfl⟩ := hmemS p (Finset.mem_filter.1 hp).1
      exact x.asHomogeneousIdeal.isHomogeneous)
    (fun p hp q hq hqp ↦ (Finset.mem_filter.1 hq).2.eq_of_le (Finset.mem_filter.1 hp).1 hqp)
    (fun p hp ↦ by
      obtain ⟨x, rfl⟩ := hmemS p (Finset.mem_filter.1 hp).1
      obtain ⟨m, y, hy, hyI, hyp⟩ := exists_homogeneous_notMem_of_not_le 𝒜
        (HomogeneousIdeal.irrelevant 𝒜).isHomogeneous (fun h ↦ x.not_irrelevant_le h)
      refine ⟨m, Nat.pos_of_ne_zero ?_, y, hy, hyp⟩
      rintro rfl
      have h0 := (HomogeneousIdeal.mem_irrelevant_iff 𝒜 y).1 hyI
      rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 hy] at h0
      exact hyp (by rw [h0]; exact Ideal.zero_mem _))
  refine ⟨n, hn, f, hf, fun x hx ↦ ?_⟩
  have hxS : x.asHomogeneousIdeal.toIdeal ∈ S := Finset.mem_image.2 ⟨x, hs.mem_toFinset.2 hx, rfl⟩
  obtain ⟨q, hxq, hq⟩ := S.exists_le_maximal hxS
  have hfq := hfM q (Finset.mem_filter.2 ⟨hq.prop, hq⟩)
  rw [SetLike.mem_coe, Proj.mem_basicOpen]
  exact fun h ↦ hfq (hxq h)
instance proj {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] : FiniteSubsetsInAffineOpens (Proj 𝒜) := ⟨fun _ hs ↦ by
  obtain ⟨n, hn, f, hf, hsf⟩ := exists_proj_basicOpen 𝒜 hs
  exact ⟨_, Proj.isAffineOpen_basicOpen 𝒜 f hf hn, hsf⟩⟩
end FiniteSubsetsInAffineOpens
end FiniteSets
section Orbits
variable {G : Type v} [Group G] {X Y : Scheme.{u}}
class OrbitsInAffineOpens (ρ : G →* Aut X) : Prop where

  exists_isAffineOpen : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ g, (ρ g).hom x ∈ U
namespace OrbitsInAffineOpens
instance (priority := 900) of_finiteSubsetsInAffineOpens [Finite G] [FiniteSubsetsInAffineOpens X]
    (ρ : G →* Aut X) : OrbitsInAffineOpens ρ := ⟨fun x ↦ by
  obtain ⟨U, hU, h⟩ := FiniteSubsetsInAffineOpens.exists_isAffineOpen _
    (Set.finite_range fun g ↦ (ρ g).hom x)
  exact ⟨U, hU, fun g ↦ h ⟨g, rfl⟩⟩⟩
instance comp {H : Type w} [Group H] (ρ : G →* Aut X) [OrbitsInAffineOpens ρ] (φ : H →* G) :
    OrbitsInAffineOpens (ρ.comp φ) := ⟨fun x ↦ by
  obtain ⟨U, hU, h⟩ := exists_isAffineOpen (ρ := ρ) x
  exact ⟨U, hU, fun g ↦ h (φ g)⟩⟩
end OrbitsInAffineOpens
variable {ρ : G →* Aut X}
variable [Finite G]
end Orbits
end GlobalTheory


