-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:46.556516+00:00
-- url     : https://prove2.me/theorems/2123e80f-9e51-45e9-9cb1-673820588ef5
-- title:
--   Range Algebra Map Eq IInf Discrete Valuation Subring
-- statement:
--   Definitions and structural lemmas for Range Algebra Map Eq IInf Discrete Valuation Subring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
namespace GlobalTheory
section KrullAkizuki
variable {A B : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.DimensionLEOne A]
variable [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
end KrullAkizuki
section Existence
variable {L : Type*} [Field L]
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [Algebra R L]
end Existence
section Domination
variable {R L : Type*} [CommRing R] [IsLocalRing R] [Field L]
variable [IsNoetherianRing R] [Algebra R L]
end Domination
section Completion
theorem isDiscreteValuationRing_of_maximalIdeal_eq_span {S : Type*} [CommRing S] [IsLocalRing S]
    [IsHausdorff (maximalIdeal S) S] {π : S} (hπ : maximalIdeal S = Ideal.span {π})
    (hn : ¬ IsNilpotent π) :
    ∃ _ : IsDomain S, IsDiscreteValuationRing S ∧ Irreducible π := by
  classical
  have key : ∀ x : S, x ≠ 0 → ∃ n : ℕ, Associated (π ^ n) x := by
    intro x hx
    have h1 : ∃ n : ℕ, ¬ π ^ (n + 1) ∣ x := by
      by_contra h
      push Not at h
      refine hx (IsHausdorff.haus' (I := maximalIdeal S) x fun n => ?_)
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, hπ, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
      exact (pow_dvd_pow π n.le_succ).trans (h n)
    have h2 : π ^ Nat.find h1 ∣ x := by
      rcases Nat.eq_zero_or_eq_succ_pred (Nat.find h1) with h | h
      · simp [h]
      · rw [h]
        exact of_not_not (Nat.find_min h1 (by omega))
    obtain ⟨u, hu⟩ := h2
    have h3 : IsUnit u := by
      by_contra h
      have h4 : u ∈ maximalIdeal S := h
      rw [hπ, Ideal.mem_span_singleton] at h4
      apply Nat.find_spec h1
      rw [pow_succ]
      exact (mul_dvd_mul_left _ h4).trans (dvd_of_eq hu.symm)
    exact ⟨_, h3.unit, hu.symm⟩
  have : NoZeroDivisors S := ⟨fun {x y} hxy => by
    by_contra h
    push Not at h
    obtain ⟨m, hm⟩ := key x h.1
    obtain ⟨n, hn'⟩ := key y h.2
    have := hm.mul_mul hn'
    rw [hxy, associated_zero_iff_eq_zero, ← pow_add] at this
    exact hn ⟨_, this⟩⟩
  have hd : IsDomain S := NoZeroDivisors.to_isDomain S
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact hn IsNilpotent.zero
  have hirr : Irreducible π :=
    ((Ideal.span_singleton_prime hπ0).mp (hπ ▸ inferInstance)).irreducible
  exact ⟨hd, IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨π, hirr, fun {x} hx => key x hx⟩, hirr⟩
variable (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
theorem algebraMap_adicCompletion_injective_of_dvr :
    Function.Injective (algebraMap V (AdicCompletion (maximalIdeal V) V)) :=
  AdicCompletion.of_injective (maximalIdeal V) V
theorem adicCompletion_isDVR_irreducible {π : V} (hπ : Irreducible π) :
    ∃ _ : IsDomain (AdicCompletion (maximalIdeal V) V),
      IsDiscreteValuationRing (AdicCompletion (maximalIdeal V) V) ∧
      Irreducible (algebraMap V (AdicCompletion (maximalIdeal V) V) π) := by
  refine isDiscreteValuationRing_of_maximalIdeal_eq_span ?_ ?_
  · rw [AdicCompletion.maximalIdeal_eq_map]
    conv_lhs => enter [2]; rw [hπ.maximalIdeal_eq]
    rw [Ideal.map_span, Set.image_singleton]
  · rw [IsNilpotent.map_iff (algebraMap_adicCompletion_injective_of_dvr V)]
    exact fun h => hπ.ne_zero h.eq_zero
instance isDomain_adicCompletion_of_dvr : IsDomain (AdicCompletion (maximalIdeal V) V) :=
  (adicCompletion_isDVR_irreducible V (IsDiscreteValuationRing.exists_irreducible V).choose_spec).1
instance isDiscreteValuationRing_adicCompletion_of_dvr :
    IsDiscreteValuationRing (AdicCompletion (maximalIdeal V) V) :=
  (adicCompletion_isDVR_irreducible V (IsDiscreteValuationRing.exists_irreducible V).choose_spec).2.1
end Completion
section KrullAkizukiFinite
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.DimensionLEOne A]
  (K : Type*) {L : Type*} [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L]
  [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
end KrullAkizukiFinite
section Main
universe u v w
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
end Main
end GlobalTheory


