-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:34.888429+00:00
-- url     : https://prove2.me/theorems/d9b74670-2613-44b0-9532-897dfba73b42
-- title:
--   Span Eq Top Of Forall Maximal
-- statement:
--   Definitions and structural lemmas for Span Eq Top Of Forall Maximal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/SpanEqTopOfForallMaximal.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one')
namespace GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
section Away
variable {S S' S'' T : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
  [CommRing S''] [Algebra R S''] [CommRing T] [Algebra R T]
def IsAway (ρ : S →ₐ[R] S') (g : S) : Prop :=
  @IsLocalization.Away S _ g S' _ (ρ : S →+* S').toAlgebra
abbrev awayHom (R : Type) [CommRing R] {S : Type} [CommRing S] [Algebra R S] (g : S) :
    S →ₐ[R] Localization.Away g := IsScalarTower.toAlgHom R S _
theorem isAway_iff (ρ : S →ₐ[R] S') (g : S) : IsAway ρ g ↔
    IsUnit (ρ g) ∧ (∀ z, ∃ (N : ℕ) (a : S), z * ρ g ^ N = ρ a) ∧
      ∀ a, ρ a = 0 → ∃ N : ℕ, g ^ N * a = 0 := by
  letI := (ρ : S →+* S').toAlgebra
  constructor
  · intro h
    haveI : IsLocalization.Away g S' := h
    refine ⟨IsLocalization.Away.algebraMap_isUnit g, fun z => IsLocalization.Away.surj g z,
      fun a ha => ?_⟩
    obtain ⟨N, hN⟩ := IsLocalization.Away.exists_of_eq (S := S') g (a := a) (b := 0)
      (by rw [map_zero]; exact ha)
    exact ⟨N, by simpa using hN⟩
  · rintro ⟨h1, h2, h3⟩
    refine IsLocalization.Away.mk g h1 h2 fun a b hab => ?_
    obtain ⟨N, hN⟩ := h3 (a - b) (by rw [map_sub, sub_eq_zero]; exact hab)
    exact ⟨N, by rwa [mul_sub, sub_eq_zero] at hN⟩
namespace IsAway
variable {ρ : S →ₐ[R] S'} {g : S}
theorem unit (h : IsAway ρ g) : IsUnit (ρ g) := ((isAway_iff _ _).1 h).1
theorem surj (h : IsAway ρ g) (z : S') : ∃ (N : ℕ) (a : S), z * ρ g ^ N = ρ a :=
  ((isAway_iff _ _).1 h).2.1 z
theorem ker (h : IsAway ρ g) {a : S} (ha : ρ a = 0) : ∃ N : ℕ, g ^ N * a = 0 :=
  ((isAway_iff _ _).1 h).2.2 a ha
theorem comp (h : IsAway ρ g) {ρ' : S' →ₐ[R] S''} {g' : S} (h' : IsAway ρ' (ρ g')) :
    IsAway (ρ'.comp ρ) (g * g') := by
  refine (isAway_iff _ _).2 ⟨?_, fun z => ?_, fun a ha => ?_⟩
  · rw [map_mul]; exact (h.unit.map ρ').mul h'.unit
  · obtain ⟨N, b, hb⟩ := h'.surj z
    obtain ⟨M, a, ha⟩ := h.surj b
    refine ⟨N + M, a * g ^ N * g' ^ M, ?_⟩
    simp only [AlgHom.comp_apply, map_mul, map_pow, ← ha, ← hb]
    ring
  · obtain ⟨N, hN⟩ := h'.ker (a := ρ a) ha
    rw [← map_pow, ← map_mul] at hN
    obtain ⟨M, hM⟩ := h.ker hN
    refine ⟨N + M, ?_⟩
    linear_combination g ^ N * g' ^ M * hM
theorem isOpenImmersion (h : IsAway ρ g) : IsOpenImmersion (spMap ρ).left := by
  letI := (ρ : S →+* S').toAlgebra
  haveI : IsLocalization.Away g S' := h
  exact IsOpenImmersion.of_isLocalization (S := S') g
theorem mem_range (h : IsAway ρ g) (p : PrimeSpectrum S) (hp : g ∉ p.asIdeal) :
    p ∈ Set.range (spMap ρ).left := by
  letI := (ρ : S →+* S').toAlgebra
  haveI : IsLocalization.Away g S' := h
  have := PrimeSpectrum.localization_away_comap_range S' g
  have hp' : p ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) := hp
  rw [← this] at hp'
  exact hp'
end IsAway
end Away
section Glue
variable {X : Over (Spec (CommRingCat.of R))} {A : Type} [CommRing A] [Algebra R A]
  {κ : Type} {s : κ → A} {B : κ → Type} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
def awayCover (hs : Ideal.span (Set.range s) = ⊤) (q : ∀ i, A →ₐ[R] B i)
    (hq : ∀ i, IsAway (q i) (s i)) : (Spec (CommRingCat.of A)).OpenCover :=
  Scheme.Cover.mkOfCovers κ (fun i => Spec (CommRingCat.of (B i))) (fun i => (spMap (q i)).left)
    (fun p => by
      have : ∃ i, s i ∉ (p : PrimeSpectrum A).asIdeal := by
        by_contra! hc
        exact (p : PrimeSpectrum A).isPrime.ne_top
          (top_le_iff.1 (hs ▸ Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hc i)))
      obtain ⟨i, hi⟩ := this
      obtain ⟨y, hy⟩ := (hq i).mem_range p hi
      exact ⟨i, y, hy⟩)
    (fun i => (hq i).isOpenImmersion)
end Glue
section Chart
variable {X : Over (Spec (CommRingCat.of R))} {A A₀ B : Type} [CommRing A] [Algebra R A]
  [CommRing A₀] [Algebra R A₀] [CommRing B] [Algebra R B]
end Chart
end GlobalTheory.SqZero


