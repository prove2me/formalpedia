-- Prove2me | solution 1 for AccelMM.BTMap.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T01:27:39.899674+00:00
-- url     : https://prove2.me/submissions/5ce64163-fadb-4b40-96c6-7eeba7fb79ff

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework
import Definitions.Def_AccelMM_BTMap_Model

namespace Aux_AccelMM_L33

open AccelMM.BTMap

lemma key_lo (a : ℝ) (ha : a ≤ 0) : Real.exp a ≤ 1 + a + a ^ 2 / 2 := by
  let g : ℝ → ℝ := fun t => 1 + t + t ^ 2 / 2 - Real.exp t
  have hd : ∀ t, HasDerivAt g (1 + t - Real.exp t) t := by
    intro t
    have := (((hasDerivAt_id t).const_add 1).add ((hasDerivAt_pow 2 t).div_const 2)).sub
      (Real.hasDerivAt_exp t)
    exact this.congr_deriv (by norm_num <;> ring)
  have hanti : Antitone g := antitone_of_deriv_nonpos (fun t => (hd t).differentiableAt)
    (fun t => by rw [(hd t).deriv]; linarith [Real.add_one_le_exp t])
  have := hanti ha
  simp [g] at this
  linarith

lemma key_hi (a : ℝ) (ha : 0 ≤ a) : Real.exp a ≤ 1 + a + Real.exp a * a ^ 2 / 2 := by
  let g : ℝ → ℝ := fun t => 1 + t + Real.exp t * t ^ 2 / 2 - Real.exp t
  have hd : ∀ t, HasDerivAt g (1 + (Real.exp t * t ^ 2 / 2 + Real.exp t * t) - Real.exp t) t := by
    intro t
    have := (((hasDerivAt_id t).const_add 1).add
      (((Real.hasDerivAt_exp t).mul (hasDerivAt_pow 2 t)).div_const 2)).sub (Real.hasDerivAt_exp t)
    exact this.congr_deriv (by norm_num <;> ring)
  have hmono : Monotone g := monotone_of_deriv_nonneg (fun t => (hd t).differentiableAt)
    (fun t => by
      rw [(hd t).deriv]
      have h1 := Real.add_one_le_exp (-t)
      have h2 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
      have h3 : 0 < Real.exp t := Real.exp_pos t
      nlinarith [sq_nonneg t, mul_le_mul_of_nonneg_left h1 h3.le])
  have := hmono ha
  simp [g] at this
  linarith

lemma key (a : ℝ) : a - Real.exp a + 1 ≥ -(max (Real.exp a) 1) * a ^ 2 / 2 := by
  rcases le_total a 0 with ha | ha
  · have := key_lo a ha
    have hm : max (Real.exp a) 1 = 1 := max_eq_right (Real.exp_le_one_iff.mpr ha)
    rw [hm]; linarith
  · have := key_hi a ha
    have hm : max (Real.exp a) 1 = Real.exp a := max_eq_left (Real.one_le_exp_iff.mpr ha)
    rw [hm]; linarith

lemma pair (ω xi xj yi yj : ℝ) (hxi : |xi| ≤ ω) (hxj : |xj| ≤ ω) (hyi : |yi| ≤ ω)
    (hyj : |yj| ≤ ω) :
    Real.log (Real.exp xi + Real.exp xj) - Real.log (Real.exp yi + Real.exp yj)
      - (Real.exp xi + Real.exp xj) / (Real.exp yi + Real.exp yj) + 1 ≥
      -(Real.exp (2 * ω) / 4) * ((xi - yi) ^ 2 + (xj - yj) ^ 2) := by
  set S := Real.exp yi + Real.exp yj with hS
  have hSpos : 0 < S := by positivity
  set P := Real.exp yi / S
  set R := Real.exp yj / S
  set a := xi - yi
  set b := xj - yj
  have hPR : P + R = 1 := by simp only [P, R]; field_simp; exact hS.symm
  have hP : 0 ≤ P := by positivity
  have hR : 0 ≤ R := by positivity
  have hxi' : Real.exp xi = Real.exp yi * Real.exp a := by rw [← Real.exp_add]; congr 1; ring
  have hxj' : Real.exp xj = Real.exp yj * Real.exp b := by rw [← Real.exp_add]; congr 1; ring
  have hratio : (Real.exp xi + Real.exp xj) / S = P * Real.exp a + R * Real.exp b := by
    simp only [P, R]; rw [hxi', hxj']; field_simp
  have hlog : Real.log (Real.exp xi + Real.exp xj) - Real.log S =
      Real.log (P * Real.exp a + R * Real.exp b) := by
    rw [← hratio, Real.log_div (by positivity) hSpos.ne']
  have hjensen : P * a + R * b ≤ Real.log (P * Real.exp a + R * Real.exp b) := by
    have hc := convexOn_exp.2 (Set.mem_univ a) (Set.mem_univ b) hP hR hPR
    simp only [smul_eq_mul] at hc
    rw [Real.le_log_iff_exp_le (by positivity)]
    exact hc
  -- bounds on weights
  have hlowS : 2 * Real.exp (-ω) ≤ S := by
    rw [abs_le] at hyi hyj
    have := Real.exp_le_exp.mpr hyi.1
    have := Real.exp_le_exp.mpr hyj.1
    linarith
  have he : Real.exp (2 * ω) * Real.exp (-ω) = Real.exp ω := by
    rw [← Real.exp_add]; congr 1; ring
  have hK : ∀ z, |z| ≤ ω → Real.exp z / S ≤ Real.exp (2 * ω) / 2 := by
    intro z hz
    rw [abs_le] at hz
    have := Real.exp_le_exp.mpr hz.2
    rw [div_le_div_iff₀ hSpos (by norm_num)]
    nlinarith [Real.exp_pos (2 * ω)]
  have hPa : P * max (Real.exp a) 1 ≤ Real.exp (2 * ω) / 2 := by
    rw [mul_max_of_nonneg _ _ hP, max_le_iff]
    refine ⟨?_, ?_⟩
    · have : P * Real.exp a = Real.exp xi / S := by simp only [P]; rw [hxi']; ring
      rw [this]; exact hK xi hxi
    · rw [mul_one]; exact hK yi hyi
  have hRb : R * max (Real.exp b) 1 ≤ Real.exp (2 * ω) / 2 := by
    rw [mul_max_of_nonneg _ _ hR, max_le_iff]
    refine ⟨?_, ?_⟩
    · have : R * Real.exp b = Real.exp xj / S := by simp only [R]; rw [hxj']; ring
      rw [this]; exact hK xj hxj
    · rw [mul_one]; exact hK yj hyj
  have ka := key a
  have kb := key b
  have t1 : P * (a - Real.exp a + 1) ≥ -(Real.exp (2 * ω) / 2) * a ^ 2 / 2 := by
    have := mul_le_mul_of_nonneg_left ka hP
    nlinarith [sq_nonneg a, mul_le_mul_of_nonneg_right hPa (sq_nonneg a)]
  have t2 : R * (b - Real.exp b + 1) ≥ -(Real.exp (2 * ω) / 2) * b ^ 2 / 2 := by
    have := mul_le_mul_of_nonneg_left kb hR
    nlinarith [sq_nonneg b, mul_le_mul_of_nonneg_right hRb (sq_nonneg b)]
  rw [hlog, hratio]
  nlinarith

lemma sum_erase_ite {n : ℕ} (f : Fin n → ℝ) (i : Fin n) :
    ∑ j ∈ Finset.univ.erase i, f j = ∑ j, if j = i then 0 else f j := by
  rw [← Finset.filter_ne', Finset.sum_filter]
  apply Finset.sum_congr rfl; intro j _
  by_cases h : j = i <;> simp [h]

lemma degM_ge {n : ℕ} (d : Fin n → Fin n → ℕ) (i : Fin n) : ∑ j, mM d i j ≤ degM d := by
  unfold degM
  exact le_ciSup (f := fun i => ∑ j, mM d i j) (Set.finite_range _).bddAbove i

lemma weight_sum {n : ℕ} (d : Fin n → Fin n → ℕ) (a : Fin n → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, (d i j : ℝ) * (a i ^ 2 + a j ^ 2) ≤ degM d * ∑ i, a i ^ 2 := by
  have e : ∑ i, ∑ j ∈ Finset.univ.erase i, (d i j : ℝ) * (a i ^ 2 + a j ^ 2) =
      ∑ i, a i ^ 2 * ∑ j, mM d i j := by
    simp only [sum_erase_ite]
    have h1 : ∀ i, a i ^ 2 * ∑ j, mM d i j = ∑ j, ((if j = i then 0 else (d i j : ℝ) * a i ^ 2) +
        (if j = i then 0 else (d j i : ℝ) * a i ^ 2)) := by
      intro i
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      unfold mM
      by_cases h : j = i
      · simp [h]
      · rw [if_neg (Ne.symm h), if_neg h, if_neg h]; ring
    simp only [h1, Finset.sum_add_distrib]
    have h2 : ∑ i, ∑ j, (if j = i then 0 else (d j i : ℝ) * a i ^ 2) =
        ∑ i, ∑ j, (if j = i then 0 else (d i j : ℝ) * a j ^ 2) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      by_cases h : j = i
      · subst h; simp
      · rw [if_neg h, if_neg (Ne.symm h)]
    rw [h2, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    split_ifs <;> ring
  rw [e, Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (degM_ge d i) (sq_nonneg _)

end Aux_AccelMM_L33

open AccelMM.BTMap Aux_AccelMM_L33 in
theorem solution {n : ℕ} (d : Fin n → Fin n → ℕ) (ω : ℝ) (hω : 0 ≤ ω)
    (x y : E n) (hx : x ∈ box ω) (hy : y ∈ box ω) :
    surr d x y - loglik d x ≥ -((1 / 2 * Real.exp (2 * ω) * degM d) / 2) * ‖x - y‖ ^ 2 := by
  have hn : ‖x - y‖ ^ 2 = ∑ i, (x i - y i) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]; simp
  have hdiff : surr d x y - loglik d x = ∑ i, ∑ j ∈ Finset.univ.erase i, (d i j : ℝ) *
      (Real.log (Real.exp (x i) + Real.exp (x j)) - Real.log (Real.exp (y i) + Real.exp (y j))
        - (Real.exp (x i) + Real.exp (x j)) / (Real.exp (y i) + Real.exp (y j)) + 1) := by
    unfold surr loglik
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _
    ring
  have hlow : ∑ i, ∑ j ∈ Finset.univ.erase i, (d i j : ℝ) * (-(Real.exp (2 * ω) / 4) *
      ((x i - y i) ^ 2 + (x j - y j) ^ 2)) ≤ surr d x y - loglik d x := by
    rw [hdiff]
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    exact mul_le_mul_of_nonneg_left (pair ω _ _ _ _ (hx i) (hx j) (hy i) (hy j)) (by positivity)
  have hW := weight_sum d (fun i => x i - y i)
  have hre : ∑ i, ∑ j ∈ Finset.univ.erase i, (d i j : ℝ) * (-(Real.exp (2 * ω) / 4) *
      ((x i - y i) ^ 2 + (x j - y j) ^ 2)) = -(Real.exp (2 * ω) / 4) *
      ∑ i, ∑ j ∈ Finset.univ.erase i, (d i j : ℝ) * ((x i - y i) ^ 2 + (x j - y j) ^ 2) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
    ring
  rw [hre] at hlow
  rw [hn]
  have hK : 0 ≤ Real.exp (2 * ω) / 4 := by positivity
  have := mul_le_mul_of_nonneg_left hW hK
  nlinarith
