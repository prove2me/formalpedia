-- Prove2me | Definitions.Def_dusart_psi_433_20261014_ZeroCountIntervals
-- name    : dusart_psi_433_20261014_ZeroCountIntervals
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:39:22.412723+00:00
-- url     : https://prove2.me/theorems/7505a482-0e7d-4345-a393-536f1ffac73f
-- title:
--   Dusart smoothing: Zero Count Intervals
-- statement:
--   This module gives the complete zero count intervals component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_IncreasingWeight
noncomputable section
namespace DusartSmoothing
open Complex Real Set MeasureTheory

lemma actual_count_add (a b : ℝ) (ha : 4 ≤ a) (hab : a ≤ b) :
    RvM.Ncount 0 b = RvM.Ncount 0 a + RvM.Ncount a b := by
  classical
  let hfa := RvM.finite_zero_window (b := a) (by norm_num : (0 : ℝ) < 4)
  let hfb := RvM.finite_zero_window (b := b) (by norm_num : (0 : ℝ) < 4)
  let hfab := RvM.finite_zero_window (a := a) (b := b) (by linarith : 0 < a)
  have he : hfb.toFinset = hfa.toFinset ∪ hfab.toFinset := by
    ext ρ
    simp only [Finset.mem_union, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hnt, hl, hu⟩
      rcases le_or_gt ρ.im a with h | h
      · exact Or.inl ⟨hnt, hl, h⟩
      · exact Or.inr ⟨hnt, h, hu⟩
    · rintro (⟨hnt, hl, hu⟩ | ⟨hnt, hl, hu⟩)
      · exact ⟨hnt, hl, hu.trans hab⟩
      · exact ⟨hnt, by linarith, hu⟩
  have hd : Disjoint hfa.toFinset hfab.toFinset := by
    apply Finset.disjoint_left.mpr
    intro ρ hρ hρ'
    have h1 := (hfa.mem_toFinset.mp hρ).2.2
    have h2 := (hfab.mem_toFinset.mp hρ').2.1
    linarith
  rw [RvM.Ncount_zero_eq_four, RvM.Ncount_zero_eq_four a]
  rw [RvM.Ncount, RvM.Ncount, RvM.Ncount,
    finsum_mem_eq_finite_toFinset_sum _ hfb,
    finsum_mem_eq_finite_toFinset_sum _ hfa,
    finsum_mem_eq_finite_toFinset_sum _ hfab, he, Finset.sum_union hd]

lemma actual_interval_window_count_eq (a b t : ℝ) (ha : 4 ≤ a) (hat : a ≤ t) (htb : t ≤ b) :
    finiteZeroCount (RvM.finite_zero_window (a := a) (b := b) (by linarith : 0 < a)).toFinset
      RvM.zeroMult Complex.im t = (RvM.Ncount 0 t : ℝ) - (RvM.Ncount 0 a : ℝ) := by
  classical
  let hf := RvM.finite_zero_window (a := a) (b := b) (by linarith : 0 < a)
  let hft := RvM.finite_zero_window (a := a) (b := t) (by linarith : 0 < a)
  have he : hf.toFinset.filter (fun ρ => ρ.im ≤ t) = hft.toFinset := by
    ext ρ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨hρ, hl, _⟩, hu⟩; exact ⟨hρ, hl, hu⟩
    · rintro ⟨hρ, hl, hu⟩; exact ⟨⟨hρ, hl, hu.trans htb⟩, hu⟩
  have hc : finiteZeroCount hf.toFinset RvM.zeroMult Complex.im t = (RvM.Ncount a t : ℝ) := by
    rw [RvM.Ncount, finsum_mem_eq_finite_toFinset_sum _ hft, Nat.cast_sum, ← he]
    simp [finiteZeroCount, primeStep, Finset.sum_filter, mul_ite]
  have hadd := congrArg (fun n : ℕ => (n : ℝ)) (actual_count_add a t ha hat)
  push_cast at hadd
  rw [hc]
  linarith

lemma intervalIntegrable_actual_count_mul_from (a b : ℝ) (ha : 4 ≤ a) (hab : a ≤ b)
    (g' : ℝ → ℝ) (hc : ContinuousOn g' (Icc a b)) :
    IntervalIntegrable (fun t => (RvM.Ncount 0 t : ℝ) * g' t) volume a b := by
  classical
  let Z := (RvM.finite_zero_window (b := b) (by norm_num : (0 : ℝ) < 4)).toFinset
  have hρ : ∀ ρ ∈ Z, IntervalIntegrable
      (fun t => (RvM.zeroMult ρ : ℝ) * primeStep ρ.im t * g' t) volume a b := by
    intro ρ _
    exact (((primeStep_mono ρ.im).intervalIntegrable (μ := volume)).const_mul
      (RvM.zeroMult ρ : ℝ)).mul_continuousOn (by simpa only [uIcc_of_le hab] using hc)
  have hi : IntervalIntegrable (fun t => finiteZeroCount Z RvM.zeroMult Complex.im t * g' t) volume a b := by
    have he : (fun t => finiteZeroCount Z RvM.zeroMult Complex.im t * g' t) =
        fun t => ∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * primeStep ρ.im t * g' t := by
      funext t; rw [finiteZeroCount, Finset.sum_mul]
    rw [he]
    have hs := IntervalIntegrable.sum Z hρ
    convert hs using 1 <;> try rfl
    funext t; simp only [Finset.sum_apply]
  apply hi.congr
  intro t ht
  rw [uIoc_of_le hab] at ht
  change finiteZeroCount Z RvM.zeroMult Complex.im t * g' t = _
  rw [actual_window_count_eq b t (ha.trans ht.1.le) ht.2]

end DusartSmoothing


