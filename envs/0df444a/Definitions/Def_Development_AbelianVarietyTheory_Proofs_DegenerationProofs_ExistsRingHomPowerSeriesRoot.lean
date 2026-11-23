-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRingHomPowerSeriesRoot
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRingHomPowerSeriesRoot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:25:29.470813+00:00
-- url     : https://prove2.me/theorems/5230ca0f-90f4-4038-a843-dfa401e1e5b3
-- title:
--   Exists Ring Hom Power Series Root
-- statement:
--   Definitions and structural lemmas for Exists Ring Hom Power Series Root, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsRingHomPowerSeriesRoot.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
namespace GlobalTheory
namespace SeriesRoot
variable {O : Type*} [CommRing O]
noncomputable def residuePart (k l : ℕ) : PowerSeries O →+ PowerSeries O where
  toFun f := PowerSeries.mk fun n => coeff (k * n + l) f
  map_zero' := by ext n; simp
  map_add' f g := by ext n; simp
theorem coeff_residuePart (k l n : ℕ) (f : PowerSeries O) :
    coeff n (residuePart k l f) = coeff (k * n + l) f := by
  simp [residuePart]
theorem coeff_X_pow_mul_expand {k : ℕ} (hk : k ≠ 0) {j : ℕ} (hj : j < k) (g : PowerSeries O)
    (m : ℕ) :
    coeff m (X ^ j * expand k hk g) = if m % k = j then coeff (m / k) g else 0 := by
  rw [coeff_X_pow_mul', coeff_expand]
  by_cases h : m % k = j
  · have hm : m = k * (m / k) + j := by rw [← h]; exact (Nat.div_add_mod m k).symm
    have h1 : j ≤ m := by omega
    have h2 : m - j = k * (m / k) := by omega
    rw [if_pos h1, if_pos h, h2, if_pos (dvd_mul_right _ _),
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hk)]
  · rw [if_neg h]
    split_ifs with h1 h2
    · exfalso
      obtain ⟨c, hc⟩ := h2
      apply h
      have : m = j + k * c := by omega
      rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
    · rfl
    · rfl
theorem sum_residuePart {k : ℕ} (hk : k ≠ 0) (f : PowerSeries O) :
    ∑ l ∈ Finset.range k, X ^ l * expand k hk (residuePart k l f) = f := by
  ext m
  rw [map_sum, Finset.sum_congr rfl
    (fun l hl => coeff_X_pow_mul_expand hk (Finset.mem_range.1 hl) _ m), Finset.sum_ite_eq,
    if_pos (Finset.mem_range.2 (Nat.mod_lt _ (Nat.pos_of_ne_zero hk))), coeff_residuePart,
    Nat.div_add_mod]
theorem residuePart_X_pow_mul_expand {k : ℕ} (hk : k ≠ 0) {j l : ℕ} (hj : j < k) (hl : l < k)
    (g : PowerSeries O) :
    residuePart k l (X ^ j * expand k hk g) = if l = j then g else 0 := by
  ext n
  rw [coeff_residuePart, coeff_X_pow_mul_expand hk hj, Nat.mul_add_mod, Nat.mod_eq_of_lt hl,
    Nat.mul_add_div (Nat.pos_of_ne_zero hk), Nat.div_eq_of_lt hl, add_zero]
  split_ifs <;> simp
variable {K : Type*} [CommRing K]
noncomputable def extendAdd (φ : PowerSeries O →+* K) (k : ℕ) (t : K) : PowerSeries O →+ K where
  toFun f := ∑ l ∈ Finset.range k, t ^ l * φ (residuePart k l f)
  map_zero' := by simp
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]
theorem extendAdd_apply (φ : PowerSeries O →+* K) (k : ℕ) (t : K) (f : PowerSeries O) :
    extendAdd φ k t f = ∑ l ∈ Finset.range k, t ^ l * φ (residuePart k l f) := rfl
theorem extendAdd_X_pow_mul_expand_of_lt (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) (t : K)
    {j : ℕ} (hj : j < k) (g : PowerSeries O) :
    extendAdd φ k t (X ^ j * expand k hk g) = t ^ j * φ g := by
  rw [extendAdd_apply, Finset.sum_eq_single j]
  · rw [residuePart_X_pow_mul_expand hk hj hj, if_pos rfl]
  · intro l hl hlj
    rw [residuePart_X_pow_mul_expand hk hj (Finset.mem_range.1 hl), if_neg hlj, map_zero,
      mul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 hj) h
theorem extendAdd_X_pow_mul_expand (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) (j : ℕ) (g : PowerSeries O) :
    extendAdd φ k t (X ^ j * expand k hk g) = t ^ j * φ g := by
  have h : (X : PowerSeries O) ^ j * expand k hk g =
      X ^ (j % k) * expand k hk (X ^ (j / k) * g) := by
    rw [map_mul, map_pow, expand_X, ← pow_mul, ← mul_assoc, ← pow_add, Nat.mod_add_div]
  rw [h, extendAdd_X_pow_mul_expand_of_lt φ hk t (Nat.mod_lt _ (Nat.pos_of_ne_zero hk)),
    map_mul, map_pow, ← ht, ← pow_mul, ← mul_assoc, ← pow_add, Nat.mod_add_div]
theorem extendAdd_mul (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) (f g : PowerSeries O) :
    extendAdd φ k t (f * g) = extendAdd φ k t f * extendAdd φ k t g := by
  conv_lhs => rw [← sum_residuePart hk f, ← sum_residuePart hk g]
  rw [extendAdd_apply φ k t f, extendAdd_apply φ k t g, Finset.sum_mul_sum, Finset.sum_mul_sum,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_mul_mul_comm, ← pow_add, ← map_mul, extendAdd_X_pow_mul_expand φ hk ht, map_mul,
    pow_add]
  ring
noncomputable def extendHom (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) : PowerSeries O →+* K where
  toFun := extendAdd φ k t
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by simpa using extendAdd_X_pow_mul_expand φ hk ht 0 1
  map_mul' := extendAdd_mul φ hk ht
end SeriesRoot
end GlobalTheory


