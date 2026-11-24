-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormUltrametric
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormUltrametric
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:03:32.069367+00:00
-- url     : https://prove2.me/theorems/7d3714d0-2ca7-4b50-81cf-b398cfe8b0d2
-- title:
--   Witt Vector Gauss Norm Ultrametric
-- statement:
--   Definitions and structural lemmas for Witt Vector Gauss Norm Ultrametric, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorGaussNormUltrametric.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltraSumLe
import Theorems.Thm_GlobalTheory_UltrametricSum_ultra_sum_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.WittGauss
open WittVector
def scaleCoeff (p : ℕ) {S : Type} [CommRing S] (t : S) (x : WittVector p S) : WittVector p S :=
  WittVector.mk p fun n => t ^ p ^ n * x.coeff n
section
variable {R : Type} [CommRing R] (a : R → ℝ) (hb : ∀ x, 0 ≤ a x ∧ a x ≤ 1) (h0 : a 0 = 0)
  (h1 : a 1 = 1) (hm : ∀ x y, a (x * y) = a x * a y) (ha : ∀ x y, a (x + y) ≤ max (a x) (a y))
include h0 ha in
theorem sum_le {ι : Type} (s : Finset ι) (f : ι → R) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i ∈ s, a (f i) ≤ c) : a (∑ i ∈ s, f i) ≤ c := by
  first
  | exact @_root_.GlobalTheory.UltrametricSum.ultra_sum_le
  | exact _root_.GlobalTheory.UltrametricSum.ultra_sum_le
  | (apply _root_.GlobalTheory.UltrametricSum.ultra_sum_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.UltrametricSum.ultra_sum_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UltrametricSum.ultra_sum_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UltrametricSum.ultra_sum_le ..)
include hb h1 hm in
theorem neg_eq (x : R) : a (-x) = a x := by
  have h : a (-1) * a (-1) = 1 := by rw [← hm]; simpa using h1
  have h' : a (-1) = 1 := by nlinarith [(hb (-1)).1, (hb (-1)).2]
  rw [← neg_one_mul, hm, h', one_mul]
def weightRing (c : ℝ) (hc : 0 ≤ c) : Subring (Polynomial R) where
  carrier := {f | ∀ k, a (f.coeff k) ≤ c ^ k}
  zero_mem' k := by simpa [h0] using pow_nonneg hc k
  one_mem' k := by
    rw [Polynomial.coeff_one]
    split_ifs with h
    · simp [h, h1]
    · simpa [h0] using pow_nonneg hc k
  add_mem' {f g} hf hg k := by
    rw [Polynomial.coeff_add]
    exact (ha _ _).trans (max_le (hf k) (hg k))
  neg_mem' {f} hf k := by
    rw [Polynomial.coeff_neg, neg_eq a hb h1 hm]
    exact hf k
  mul_mem' {f g} hf hg k := by
    rw [Polynomial.coeff_mul]
    refine sum_le a h0 ha _ _ _ (pow_nonneg hc k) fun ij hij => ?_
    have e : ij.1 + ij.2 = k := by simpa using hij
    rw [hm, ← e, pow_add]
    exact mul_le_mul (hf _) (hg _) (hb _).1 (pow_nonneg hc _)
end
end GlobalTheory.WittGauss


