-- Prove2me | solution 1 for Arxiv1706_02824.eq30_normally_ordered_coherence
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T22:56:00.167584+00:00
-- url     : https://prove2.me/submissions/40790ff0-39cc-46e1-8017-d2dacbf7663d

import Mathlib
import Definitions.Def_Arxiv1706_02824_Basic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ComplexConjugate

namespace S72C
open Arxiv1706_02824
open scoped ComplexConjugate Nat

lemma hs0 (r : ℝ) : HasSum (fun n : ℕ => r ^ n / (Nat.factorial n)) (Real.exp r) := by
  have h := (Real.summable_pow_div_factorial r).hasSum
  rwa [show Real.exp r = ∑' n : ℕ, r ^ n / (Nat.factorial n) by
    rw [Real.exp_eq_exp_ℝ]; exact congrFun NormedSpace.exp_eq_tsum_div r]

lemma hs1 (r : ℝ) : HasSum (fun n : ℕ => (n : ℝ) * (r ^ n / (Nat.factorial n))) (r * Real.exp r) := by
  have h := (hs0 r).mul_left r
  have h2 : HasSum (fun n : ℕ => (fun n : ℕ => (n : ℝ) * (r ^ n / (Nat.factorial n))) (n + 1)) (r * Real.exp r) := by
    refine h.congr_fun (fun n => ?_)
    simp only [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    push_cast
    field_simp
  have h3 := (hasSum_nat_add_iff (f := fun n : ℕ => (n : ℝ) * (r ^ n / (Nat.factorial n))) 1).mp h2
  simpa using h3

lemma hs2 (r : ℝ) : HasSum (fun n : ℕ => ((n : ℝ) * ((n : ℝ) - 1)) * (r ^ n / (Nat.factorial n)))
    (r ^ 2 * Real.exp r) := by
  have h := (hs0 r).mul_left (r ^ 2)
  have h2 : HasSum (fun n : ℕ => (fun n : ℕ => ((n : ℝ) * ((n : ℝ) - 1)) * (r ^ n / (Nat.factorial n))) (n + 2))
      (r ^ 2 * Real.exp r) := by
    refine h.congr_fun (fun n => ?_)
    simp only [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    push_cast
    field_simp
    ring
  have h3 := (hasSum_nat_add_iff
    (f := fun n : ℕ => ((n : ℝ) * ((n : ℝ) - 1)) * (r ^ n / (Nat.factorial n))) 2).mp h2
  simpa [Finset.sum_range_succ] using h3

lemma normSq_coh (α : ℂ) (n : ℕ) :
    Complex.normSq (coherentState α n) = Real.exp (-(‖α‖ ^ 2)) * ((‖α‖ ^ 2) ^ n / (Nat.factorial n)) := by
  unfold coherentState
  rw [map_div₀, map_mul, map_pow, Complex.normSq_ofReal, Complex.normSq_ofReal,
    Complex.normSq_eq_norm_sq α, Real.mul_self_sqrt (by positivity), ← Real.exp_add]
  ring_nf

lemma expect (α K : ℂ) (q : ℕ → ℝ) (S : ℝ)
    (h : HasSum (fun n => q n * (Real.exp (-(‖α‖ ^ 2)) * ((‖α‖ ^ 2) ^ n / (Nat.factorial n)))) S) :
    fockInner (coherentState α) (fun n => (K * (q n : ℂ)) * coherentState α n) = K * S := by
  unfold fockInner
  have e : ∀ n, conj (coherentState α n) * ((K * (q n : ℂ)) * coherentState α n) =
      K * ((q n * (Real.exp (-(‖α‖ ^ 2)) * ((‖α‖ ^ 2) ^ n / (Nat.factorial n))) : ℝ) : ℂ) := by
    intro n
    rw [← normSq_coh, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]; ring
  simp_rw [e]
  exact ((Complex.hasSum_ofReal.mpr h).mul_left K).tsum_eq

lemma sqc {c : ℝ} (hc : 0 ≤ c) : (Real.sqrt c : ℂ) * (Real.sqrt c : ℂ) = c := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]

lemma negpos (hbar ω : ℝ) (hc : 0 ≤ hbar * ω / 2) (u : ℝ → ℂ) (x y : ℝ) (ψ : ℕ → ℂ) :
    fieldNeg hbar ω u x (fieldPos hbar ω u y ψ) =
      fun n : ℕ => (((hbar * ω / 2 : ℝ) : ℂ) * conj (u x) * u y * ((n : ℝ) : ℂ)) * ψ n := by
  funext n
  cases n with
  | zero => simp [fieldNeg, creation]
  | succ m =>
    simp only [fieldNeg, fieldPos, creation, annihilation]
    have ht := sqc (show (0 : ℝ) ≤ (m : ℝ) + 1 by positivity)
    have hs := sqc hc
    have hI := Complex.I_mul_I
    push_cast at ht hs ⊢
    linear_combination (-(Complex.I * Complex.I) * conj (u x) * u y * ψ (m + 1) *
      (Real.sqrt ((m : ℝ) + 1) : ℂ) * (Real.sqrt ((m : ℝ) + 1) : ℂ)) * hs +
      ((hbar : ℂ) * ω / 2 * (-(Complex.I * Complex.I)) * conj (u x) * u y * ψ (m + 1)) * ht +
      (-((hbar : ℂ) * ω / 2 * conj (u x) * u y * ψ (m + 1) * ((m : ℂ) + 1))) * hI

end S72C
namespace S72C
open Arxiv1706_02824
open scoped ComplexConjugate

lemma expect2 (α K : ℂ) (q : ℕ → ℝ) (S : ℝ) (F : ℕ → ℂ)
    (hF : ∀ n, F n = (K * (q n : ℂ)) * coherentState α n)
    (h : HasSum (fun n => q n * (Real.exp (-(‖α‖ ^ 2)) * ((‖α‖ ^ 2) ^ n / (Nat.factorial n)))) S) :
    fockInner (coherentState α) F = K * S := by
  rw [show F = _ from funext hF]; exact expect α K q S h

lemma w1 (r : ℝ) : HasSum (fun n : ℕ => (n : ℝ) * (Real.exp (-r) * (r ^ n / (Nat.factorial n)))) r := by
  have h := (hs1 r).mul_left (Real.exp (-r))
  have e : Real.exp (-r) * (r * Real.exp r) = r := by
    rw [mul_comm r, ← mul_assoc, ← Real.exp_add]; simp
  rw [e] at h
  exact h.congr_fun (fun n => by ring)

lemma w2 (r : ℝ) : HasSum (fun n : ℕ => ((n : ℝ) * ((n : ℝ) - 1)) *
    (Real.exp (-r) * (r ^ n / (Nat.factorial n)))) (r ^ 2) := by
  have h := (hs2 r).mul_left (Real.exp (-r))
  have e : Real.exp (-r) * (r ^ 2 * Real.exp r) = r ^ 2 := by
    rw [mul_comm (r ^ 2), ← mul_assoc, ← Real.exp_add]; simp
  rw [e] at h
  exact h.congr_fun (fun n => by ring)

lemma w3 (r : ℝ) : HasSum (fun n : ℕ => ((n : ℝ) * (n : ℝ)) *
    (Real.exp (-r) * (r ^ n / (Nat.factorial n)))) (r ^ 2 + r) := by
  exact ((w2 r).add (w1 r)).congr_fun (fun n => by ring)

lemma conj_mul_norm (z : ℂ) : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.conj_mul']; push_cast; ring

lemma I1 (hbar ω : ℝ) (hc : 0 ≤ hbar * ω / 2) (u : ℝ → ℂ) (α : ℂ) (x : ℝ) :
    cohExpect α (intensityOp hbar ω u x) = ((hbar * ω / 2 * ‖α‖ ^ 2 * ‖u x‖ ^ 2 : ℝ) : ℂ) := by
  simp only [cohExpect, intensityOp]
  rw [negpos hbar ω hc]
  rw [expect2 α (((hbar * ω / 2 : ℝ) : ℂ) * conj (u x) * u x) (fun n => (n : ℝ)) (‖α‖ ^ 2) _
    (fun n => rfl) (w1 _)]
  rw [mul_assoc (((hbar * ω / 2 : ℝ) : ℂ)), conj_mul_norm]; push_cast; ring

lemma I2 (hbar ω : ℝ) (hc : 0 ≤ hbar * ω / 2) (u : ℝ → ℂ) (α : ℂ) (x1 x2 : ℝ) :
    cohExpect α (fun ψ => intensityOp hbar ω u x1 (intensityOp hbar ω u x2 ψ)) =
      (((hbar * ω / 2) ^ 2 * (‖α‖ ^ 4 + ‖α‖ ^ 2) * ‖u x1‖ ^ 2 * ‖u x2‖ ^ 2 : ℝ) : ℂ) := by
  simp only [cohExpect, intensityOp]
  rw [negpos hbar ω hc, negpos hbar ω hc]
  rw [expect2 α (((hbar * ω / 2 : ℝ) : ℂ) ^ 2 * (conj (u x1) * u x1) * (conj (u x2) * u x2))
    (fun n => (n : ℝ) * (n : ℝ)) (‖α‖ ^ 2 ^ 2 + ‖α‖ ^ 2) _ (fun n => by push_cast; ring) (by
      have := w3 (‖α‖ ^ 2); convert this using 1; ring)]
  rw [conj_mul_norm, conj_mul_norm]; push_cast; ring

lemma FP (hbar ω : ℝ) (hc : 0 ≤ hbar * ω / 2) (u : ℝ → ℂ) (α : ℂ) (x1 x2 x3 x4 : ℝ) :
    cohExpect α (fun ψ => fieldNeg hbar ω u x1 (fieldPos hbar ω u x2
      (fieldNeg hbar ω u x3 (fieldPos hbar ω u x4 ψ)))) =
      (((hbar * ω / 2) ^ 2 * (‖α‖ ^ 4 + ‖α‖ ^ 2) : ℝ) : ℂ) *
        conj (u x1) * u x2 * conj (u x3) * u x4 := by
  simp only [cohExpect]
  rw [negpos hbar ω hc, negpos hbar ω hc]
  rw [expect2 α (((hbar * ω / 2 : ℝ) : ℂ) ^ 2 * conj (u x1) * u x2 * conj (u x3) * u x4)
    (fun n => (n : ℝ) * (n : ℝ)) (‖α‖ ^ 2 ^ 2 + ‖α‖ ^ 2) _ (fun n => by push_cast; ring) (by
      have := w3 (‖α‖ ^ 2); convert this using 1; ring)]
  push_cast; ring

end S72C
namespace S72C
open Arxiv1706_02824
open scoped ComplexConjugate

lemma NO (hbar ω : ℝ) (hc : 0 ≤ hbar * ω / 2) (u : ℝ → ℂ) (x1 x2 : ℝ) (ψ : ℕ → ℂ) :
    fieldNeg hbar ω u x1 (fieldNeg hbar ω u x2 (fieldPos hbar ω u x1 (fieldPos hbar ω u x2 ψ))) =
      fun n : ℕ => ((((hbar * ω / 2 : ℝ) : ℂ) ^ 2 * (conj (u x1) * u x1) * (conj (u x2) * u x2)) *
        (((n : ℝ) * ((n : ℝ) - 1) : ℝ) : ℂ)) * ψ n := by
  funext n
  match n with
  | 0 => simp [fieldNeg, creation]
  | 1 => simp [fieldNeg, creation]
  | m + 2 =>
    simp only [fieldNeg, fieldPos, creation, annihilation]
    have ht1 := sqc (show (0 : ℝ) ≤ (m : ℝ) + 1 by positivity)
    have ht2 := sqc (show (0 : ℝ) ≤ (m : ℝ) + 1 + 1 by positivity)
    have hs := sqc hc
    have hI := Complex.I_mul_I
    push_cast at ht1 ht2 hs ⊢
    set t1 : ℂ := (Real.sqrt ((m : ℝ) + 1) : ℂ)
    set t2 : ℂ := (Real.sqrt ((m : ℝ) + 1 + 1) : ℂ)
    set s : ℂ := (Real.sqrt (hbar * ω / 2) : ℂ)
    set c : ℂ := (hbar : ℂ) * ω / 2
    set K := conj (u x1) * conj (u x2) * u x1 * u x2 * ψ (m + 2)
    linear_combination ((Complex.I * Complex.I - 1) * s ^ 4 * t1 ^ 2 * t2 ^ 2 * K) * hI +
      ((s * s + c) * t1 ^ 2 * t2 ^ 2 * K) * hs + (c ^ 2 * t2 ^ 2 * K) * ht1 +
      (c ^ 2 * ((m : ℂ) + 1) * K) * ht2

lemma NOE (hbar ω : ℝ) (hc : 0 ≤ hbar * ω / 2) (u : ℝ → ℂ) (α : ℂ) (x1 x2 : ℝ) :
    normalOrderedCorr hbar ω u α x1 x2 =
      (((hbar * ω / 2) ^ 2 * ‖α‖ ^ 4 * ‖u x1‖ ^ 2 * ‖u x2‖ ^ 2 : ℝ) : ℂ) := by
  simp only [normalOrderedCorr, cohExpect]
  rw [NO hbar ω hc]
  rw [expect2 α (((hbar * ω / 2 : ℝ) : ℂ) ^ 2 * (conj (u x1) * u x1) * (conj (u x2) * u x2))
    (fun n => (n : ℝ) * ((n : ℝ) - 1)) ((‖α‖ ^ 2) ^ 2) _ (fun n => rfl) (w2 _)]
  rw [conj_mul_norm, conj_mul_norm]; push_cast; ring

end S72C

open Arxiv1706_02824 S72C in
theorem solution (hbar ω : ℝ) (hhbar : 0 < hbar) (hω : 0 < ω)
    (u0 : ℝ → ℂ) (hnorm : ∫ y : ℝ, ‖u0 y‖ ^ 2 = 1) (α : ℂ) (x1 x2 : ℝ) :
    normalOrderedCorr hbar ω u0 α x1 x2 =
      (((hbar * ω / 2) ^ 2 * ‖α‖ ^ 4 * ‖u0 x1‖ ^ 2 * ‖u0 x2‖ ^ 2 : ℝ) : ℂ) ∧
    (α ≠ 0 → u0 x1 ≠ 0 → u0 x2 ≠ 0 → cohGamma22Normal hbar ω u0 α x1 x2 = 1) ∧
    normalOrderedCorr hbar ω u0 α x1 x2 -
      cohExpect α (intensityOp hbar ω u0 x1) * cohExpect α (intensityOp hbar ω u0 x2) = 0 := by
  have hc : 0 ≤ hbar * ω / 2 := by positivity
  refine ⟨NOE hbar ω hc u0 α x1 x2, fun hα h1 h2 => ?_, ?_⟩
  · unfold cohGamma22Normal
    rw [NOE hbar ω hc, I1 hbar ω hc, I1 hbar ω hc]
    have e1 : (‖α‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hα)
    have e2 : (‖u0 x1‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr h1)
    have e3 : (‖u0 x2‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr h2)
    have h3 : (hbar : ℂ) ≠ 0 := by exact_mod_cast hhbar.ne'
    have h4 : (ω : ℂ) ≠ 0 := by exact_mod_cast hω.ne'
    push_cast
    field_simp
  · rw [NOE hbar ω hc, I1 hbar ω hc, I1 hbar ω hc]; push_cast; ring
