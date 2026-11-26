-- Prove2me | solution 1 for Arxiv1706_02824.eq31_coherent_state_coherence_factor
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T22:56:09.584644+00:00
-- url     : https://prove2.me/submissions/bae20ffd-2fd3-40fc-855f-d3ad056cd624

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

open Arxiv1706_02824 S72C in
theorem solution (hbar ω : ℝ) (hhbar : 0 < hbar) (hω : 0 < ω)
    (u0 : ℝ → ℂ) (hnorm : ∫ y : ℝ, ‖u0 y‖ ^ 2 = 1) (α : ℂ) (x1 x2 : ℝ)
    (h1 : u0 x1 ≠ 0) (h2 : u0 x2 ≠ 0) :
    (α ≠ 0 → cohGamma22 hbar ω u0 α x1 x2 = 1 + (((‖α‖ ^ 2)⁻¹ : ℝ) : ℂ)) ∧
    Tendsto (fun β : ℂ => cohGamma22 hbar ω u0 β x1 x2 - 1) (Bornology.cobounded ℂ) (𝓝 0) := by
  have hc : 0 ≤ hbar * ω / 2 := by positivity
  have key : ∀ β : ℂ, β ≠ 0 → cohGamma22 hbar ω u0 β x1 x2 = 1 + (((‖β‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
    intro β hβ
    unfold cohGamma22
    rw [I2 hbar ω hc, I1 hbar ω hc, I1 hbar ω hc]
    have e1 : (‖β‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hβ)
    have e2 : (‖u0 x1‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr h1)
    have e3 : (‖u0 x2‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr h2)
    have h3 : (hbar : ℂ) ≠ 0 := by exact_mod_cast hhbar.ne'
    have h4 : (ω : ℂ) ≠ 0 := by exact_mod_cast hω.ne'
    push_cast
    field_simp
  refine ⟨key α, ?_⟩
  have hev : (fun β : ℂ => cohGamma22 hbar ω u0 β x1 x2 - 1) =ᶠ[Bornology.cobounded ℂ]
      (fun β : ℂ => (((‖β‖ ^ 2)⁻¹ : ℝ) : ℂ)) := by
    have : ∀ᶠ β : ℂ in Bornology.cobounded ℂ, β ≠ 0 := by
      have := tendsto_norm_cobounded_atTop (E := ℂ)
      filter_upwards [this.eventually_gt_atTop 0] with β hβ
      exact norm_pos_iff.mp hβ
    filter_upwards [this] with β hβ
    rw [key β hβ]; ring
  refine Tendsto.congr' hev.symm ?_
  have h0 : Tendsto (fun β : ℂ => (‖β‖ ^ 2)⁻¹) (Bornology.cobounded ℂ) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      tendsto_norm_cobounded_atTop)
  have := (Complex.continuous_ofReal.tendsto 0).comp h0
  rw [Complex.ofReal_zero] at this
  exact this
