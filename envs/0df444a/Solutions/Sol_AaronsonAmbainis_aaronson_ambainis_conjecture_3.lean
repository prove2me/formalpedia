-- Prove2me | solution 3 for AaronsonAmbainis.aaronson_ambainis_conjecture
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-17T15:39:12.408915+00:00
-- url     : https://prove2.me/submissions/cc842d32-be89-4cfb-a0bd-014ca8e546cf

import Mathlib
import Definitions.Def_AaronsonAmbainis
import Theorems.Thm_AaronsonAmbainis_Short_influence_bound_self
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_eval_zo
import Theorems.Thm_AaronsonAmbainis_Bridge_variance_le_quarter
import Theorems.Thm_AaronsonAmbainis_Bridge_variance_affine
import Theorems.Thm_AaronsonAmbainis_Bridge_inflR_affine
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_add
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_const
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_smul

open AaronsonAmbainis
open Finset

namespace AASolGoal2

lemma arith (ε V I dr : ℝ) (hε : 0 < ε) (hεV : ε ≤ V) (hV : V ≤ 1 / 4) (hd : 1 ≤ dr)
    (h : (4 * V) ^ 12 ≤ 2 ^ 54 * Real.pi ^ 12 * dr ^ 12 * I) : (ε / dr) ^ 39 ≤ I := by
  have hd0 : 0 < dr := by linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ε / dr := ⟨_, rfl⟩
  rw [← hr]
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr4 : r ≤ 1 / 4 := by
    rw [hr]
    exact (div_le_self hε.le hd).trans (by linarith)
  have hεr : ε = r * dr := by
    rw [hr]; field_simp
  have h1 : (4 * ε) ^ 12 ≤ (4 * V) ^ 12 := pow_le_pow_left₀ (by positivity) (by linarith) 12
  have h3 : 2 ^ 24 * r ^ 12 * dr ^ 12 ≤ 2 ^ 54 * Real.pi ^ 12 * I * dr ^ 12 := by
    calc 2 ^ 24 * r ^ 12 * dr ^ 12 = (4 * ε) ^ 12 := by rw [hεr]; ring
      _ ≤ (4 * V) ^ 12 := h1
      _ ≤ 2 ^ 54 * Real.pi ^ 12 * dr ^ 12 * I := h
      _ = 2 ^ 54 * Real.pi ^ 12 * I * dr ^ 12 := by ring
  have h4 : 2 ^ 24 * r ^ 12 ≤ 2 ^ 54 * Real.pi ^ 12 * I :=
    le_of_mul_le_mul_right h3 (by positivity)
  have hI : 0 < I := by
    have hpos : 0 < 2 ^ 54 * Real.pi ^ 12 * I := lt_of_lt_of_le (by positivity) h4
    by_contra hn
    push Not at hn
    have : 2 ^ 54 * Real.pi ^ 12 * I ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hn
    linarith
  have hpi : Real.pi ^ 12 ≤ 4 ^ 12 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_le_four 12
  have h5 : 2 ^ 54 * Real.pi ^ 12 * I ≤ 2 ^ 54 * 4 ^ 12 * I :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpi (by positivity)) hI.le
  have h6 : r ^ 12 ≤ 2 ^ 54 * I := by
    have := h4.trans h5
    norm_num at this ⊢
    linarith
  have h7 : r ^ 27 ≤ (1 / 4) ^ 27 := pow_le_pow_left₀ hr0.le hr4 27
  calc r ^ 39 = r ^ 12 * r ^ 27 := by ring
    _ ≤ r ^ 12 * (1 / 4) ^ 27 := mul_le_mul_of_nonneg_left h7 (by positivity)
    _ ≤ (2 ^ 54 * I) * (1 / 4) ^ 27 := mul_le_mul_of_nonneg_right h6 (by positivity)
    _ = I := by ring

lemma flip_eq {N : ℕ} (x : Fin N → Bool) (j : Fin N) :
    flipSet x {j} = AaronsonAmbainis.flipBit x j := by
  funext i
  unfold flipSet AaronsonAmbainis.flipBit
  by_cases h : i = j
  · subst h; simp
  · simp [h]

lemma variance_eq {N : ℕ} (p : MvPolynomial (Fin N) ℝ) :
    variance (cubeEval p) = cubeVar p := by
  simp only [variance, mean, cubeVar, cubeExp, Fintype.card_fin, div_eq_inv_mul]

lemma inflR_eq {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (j : Fin N) :
    inflR (cubeEval p) j = cubeInfl p j / 4 := by
  have h : ∀ x : Fin N → Bool, ((cubeEval p x - cubeEval p (flipSet x {j})) / 2) ^ 2
      = (cubeEval p x - cubeEval p (AaronsonAmbainis.flipBit x j)) ^ 2 / 4 := by
    intro x; rw [flip_eq]; ring
  simp only [inflR, cubeInfl, cubeExp, Fintype.card_fin, h, ← Finset.sum_div]
  ring

end AASolGoal2

theorem solution : ∃ C : ℕ, ∀ (N d : ℕ) (p : MvPolynomial (Fin N) ℝ) (ε : ℝ),
      p.totalDegree ≤ d →
      (∀ x : Fin N → Bool, 0 ≤ AaronsonAmbainis.cubeEval p x ∧ AaronsonAmbainis.cubeEval p x ≤ 1) →
      0 < ε → ε ≤ AaronsonAmbainis.cubeVar p →
      ∃ i : Fin N, (ε / (d : ℝ)) ^ C ≤ AaronsonAmbainis.cubeInfl p i := by
  refine ⟨39, ?_⟩
  intro N d p ε hdeg h01 hε hεV
  have hP : HasDegreeLE (cubeEval p) d := Bridge.hasDegreeLE_eval_zo p hdeg
  obtain ⟨g, hgdef⟩ : ∃ g : Cube (Fin N) → ℝ, g = fun x => -1 + 2 * cubeEval p x := ⟨_, rfl⟩
  have hgdeg : HasDegreeLE g d := by
    rw [hgdef]
    exact Bridge.hasDegreeLE_add (Bridge.hasDegreeLE_const (-1) d) (Bridge.hasDegreeLE_smul 2 hP)
  have hg : ∀ x, |g x| ≤ 1 := by
    intro x
    rw [hgdef]
    exact abs_le.mpr ⟨by linarith [(h01 x).1], by linarith [(h01 x).2]⟩
  have hvg : variance g = 4 * cubeVar p := by
    rw [hgdef]
    exact (Bridge.variance_affine (-1) 2 (cubeEval p)).trans
      (by rw [AASolGoal2.variance_eq]; norm_num)
  have hig : ∀ j, inflR g j = cubeInfl p j := by
    intro j
    rw [hgdef]
    exact (Bridge.inflR_affine (-1) 2 (cubeEval p) j).trans
      (by rw [AASolGoal2.inflR_eq]; ring)
  have hq : cubeVar p ≤ 1 / 4 := by
    rw [← AASolGoal2.variance_eq]
    exact Bridge.variance_le_quarter h01
  have hvpos : 0 < variance g := by rw [hvg]; linarith
  obtain ⟨j, hj⟩ := Short.influence_bound_self d g hg hgdeg hvpos
  rw [hvg, hig] at hj
  have hd : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h
    · exfalso
      have hz : (2:ℝ) ^ 54 * Real.pi ^ 12 * (d:ℝ) ^ 12 * cubeInfl p j = 0 := by
        rw [h0]; simp
      rw [hz] at hj
      have : 0 < (4 * cubeVar p) ^ 12 := by
        have : 0 < 4 * cubeVar p := by linarith
        positivity
      linarith
    · exact h
  exact ⟨j, AASolGoal2.arith ε (cubeVar p) (cubeInfl p j) d hε hεV hq (by exact_mod_cast hd) hj⟩
