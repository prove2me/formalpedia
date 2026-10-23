-- Prove2me | solution 1 for AgriSubsidy.Budget.proposition_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T11:46:52.746498+00:00
-- url     : https://prove2.me/submissions/08db39cf-c73f-4ed5-9621-5c702f0bde93

import Mathlib
import Definitions.Def_AgriSubsidy_Budget_Setting

open AgriSubsidy.Budget

namespace AgriProp10Aux

lemma sum_update' {N : ℕ} (q : Fin N → ℝ) (j : Fin N) (x : ℝ) :
    ∑ i, Function.update q j x i = ∑ i, q i + (x - q j) := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ j), Finset.sdiff_singleton_eq_erase,
    ← Finset.add_sum_erase Finset.univ q (Finset.mem_univ j)]
  ring

lemma foc {N : ℕ} (P : AgriSubsidy.Combined.Params) (z t q : Fin N → ℝ) (hβ : 0 < P.β)
    (heq : AgriSubsidy.Budget.IsEquilibrium P z t q) (j : Fin N) (hq : 0 < q j) :
    P.β * q j = P.α - (z j * P.cP + P.cH - t j) - P.β * ∑ i, q i := by
  unfold AgriSubsidy.Budget.IsEquilibrium CournotGame.IsEquilibrium at heq
  obtain ⟨_, h⟩ := heq
  set A := P.α - (z j * P.cP + P.cH - t j) - P.β * (∑ i, q i - q j) with hA
  have key : ∀ x, 0 ≤ x → (A - P.β * x) * x ≤ (A - P.β * q j) * q j := by
    intro x hx
    have := h j x hx
    simp only [CournotGame.profit, game, sum_update', Function.update_self] at this
    have e1 : (A - P.β * x) * x
        = (P.α - (z j * P.cP + P.cH - t j) - P.β * (∑ i, q i + (x - q j))) * x := by
      rw [hA]; ring
    have e2 : (A - P.β * q j) * q j
        = (P.α - (z j * P.cP + P.cH - t j) - P.β * ∑ i, q i) * q j := by
      rw [hA]; ring
    rw [e1, e2]; exact this
  have h0 := key 0 le_rfl
  have hA0 : 0 ≤ A - P.β * q j := by
    by_contra hc
    push Not at hc
    nlinarith
  have hApos : 0 ≤ A := by nlinarith
  have h2 := key (A / (2 * P.β)) (by positivity)
  have e3 : (A - P.β * (A / (2 * P.β))) * (A / (2 * P.β)) = A ^ 2 / (4 * P.β) := by
    field_simp; ring
  rw [e3] at h2
  have h4 : (A - 2 * P.β * q j) ^ 2 ≤ 0 := by
    have : A ^ 2 / (4 * P.β) * (4 * P.β) = A ^ 2 := by field_simp
    nlinarith
  have h5 : A - 2 * P.β * q j = 0 := by
    have := sq_nonneg (A - 2 * P.β * q j)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h4 this)
  rw [hA] at h5
  linarith

lemma sum_aff {N : ℕ} (z : Fin N → ℝ) (c d : ℝ) :
    ∑ j, (c + d * z j) = (N : ℝ) * c + d * ∑ j, z j := by
  simp [Finset.sum_add_distrib, Finset.mul_sum]

lemma sum_aff_mul {N : ℕ} (z : Fin N → ℝ) (a b c d : ℝ) :
    ∑ j, (a + b * z j) * (c + d * z j)
      = (N : ℝ) * (a * c) + (a * d + b * c) * ∑ j, z j + b * d * ∑ j, (z j) ^ 2 := by
  have : ∀ j, (a + b * z j) * (c + d * z j) = a * c + (a * d + b * c) * z j + b * d * (z j) ^ 2 := by
    intro j; ring
  simp [this, Finset.sum_add_distrib, Finset.mul_sum]


lemma sum_z {N : ℕ} (hN : 0 < N) (z : Fin N → ℝ) :
    ∑ j, z j = (N : ℝ) * AgriSubsidy.Combined.zbar z := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold AgriSubsidy.Combined.zbar
  field_simp

lemma sum_zz {N : ℕ} (hN : 0 < N) (z : Fin N → ℝ) :
    ∑ j, (z j) ^ 2 = (N : ℝ) * (vz z + AgriSubsidy.Combined.zbar z ^ 2) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold vz
  field_simp
  ring

lemma vz_nonneg {N : ℕ} (hN : 0 < N) (z : Fin N → ℝ) : 0 ≤ vz z := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have h := sum_aff_mul z (-AgriSubsidy.Combined.zbar z) 1 (-AgriSubsidy.Combined.zbar z) 1
  rw [sum_z hN z, sum_zz hN z] at h
  have h0 : 0 ≤ ∑ j, (-AgriSubsidy.Combined.zbar z + 1 * z j) * (-AgriSubsidy.Combined.zbar z + 1 * z j) :=
    Finset.sum_nonneg (fun j _ => mul_self_nonneg _)
  have : (N : ℝ) * vz z ≥ 0 := by nlinarith
  by_contra hc
  push Not at hc
  have := mul_neg_of_pos_of_neg hn hc
  linarith

lemma combined_design {N : ℕ} (hN : 0 < N) (P : AgriSubsidy.Combined.Params) (z q : Fin N → ℝ)
    (hβ : 0 < P.β) (sP sH : ℝ)
    (heq : IsEquilibrium P z (AgriSubsidy.Combined.combined z sP sH) q) (hpos : ∀ j, 0 < q j) :
    P.β * ((N : ℝ) + 1) * (∑ j, q j)
        = (N : ℝ) * (AgriSubsidy.Combined.abar P z 0 0 + AgriSubsidy.Combined.zbar z * sP + sH) ∧
    P.β * (∑ j, AgriSubsidy.Combined.combined z sP sH j * q j)
      = P.β * (AgriSubsidy.Combined.zbar z * sP + sH) * (∑ j, q j)
          - (N : ℝ) * vz z * sP * (P.cP - sP) := by
  have hβ0 : P.β ≠ 0 := hβ.ne'
  have hq : ∀ j, q j = (P.α - P.cH + sH - P.β * ∑ i, q i) / P.β + (-(P.cP - sP) / P.β) * z j := by
    intro j
    have := foc P z _ q hβ heq j (hpos j)
    simp only [AgriSubsidy.Combined.combined] at this
    field_simp
    linarith
  set M := (P.α - P.cH + sH - P.β * ∑ i, q i) / P.β with hM_def
  set d := -(P.cP - sP) / P.β with hd_def
  have hM : P.β * M = P.α - P.cH + sH - P.β * ∑ i, q i := by rw [hM_def]; field_simp
  have hd : P.β * d = -(P.cP - sP) := by rw [hd_def]; field_simp
  have h1 : ∑ j, q j = (N : ℝ) * M + d * ((N : ℝ) * AgriSubsidy.Combined.zbar z) := by
    rw [← sum_z hN z, ← sum_aff z M d]
    exact Finset.sum_congr rfl (fun j _ => hq j)
  have h2 : ∑ j, AgriSubsidy.Combined.combined z sP sH j * q j
      = (N : ℝ) * (sH * M) + (sH * d + sP * M) * ((N : ℝ) * AgriSubsidy.Combined.zbar z)
        + sP * d * ((N : ℝ) * (vz z + AgriSubsidy.Combined.zbar z ^ 2)) := by
    rw [← sum_z hN z, ← sum_zz hN z, ← sum_aff_mul z sH sP M d]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hq j]; simp only [AgriSubsidy.Combined.combined]; ring
  have ha : AgriSubsidy.Combined.abar P z 0 0 = P.α - AgriSubsidy.Combined.zbar z * P.cP - P.cH := by
    unfold AgriSubsidy.Combined.abar; ring
  rw [ha]
  constructor
  · linear_combination P.β * h1 + (N : ℝ) * hM + (N : ℝ) * AgriSubsidy.Combined.zbar z * hd
  · rw [h2]
    linear_combination (-(P.β * (AgriSubsidy.Combined.zbar z * sP + sH))) * h1
      + (N : ℝ) * vz z * sP * hd

lemma lower_bound {N : ℕ} (hN : 0 < N) (P : AgriSubsidy.Combined.Params) (z t q : Fin N → ℝ)
    (hβ : 0 < P.β) (heq : IsEquilibrium P z t q) (hpos : ∀ j, 0 < q j) :
    P.β * ((N : ℝ) + 1) / (N : ℝ) * (∑ j, q j) ^ 2 - AgriSubsidy.Combined.abar P z 0 0 * (∑ j, q j)
      - (N : ℝ) * vz z * P.cP ^ 2 / (4 * P.β) ≤ ∑ j, t j * q j := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hβ0 : P.β ≠ 0 := hβ.ne'
  set Q := ∑ j, q j with hQ
  set zb := AgriSubsidy.Combined.zbar z with hzb
  set A := Q / (N : ℝ) with hA_def
  set k := P.cP / (2 * P.β) with hk_def
  have hk : 2 * P.β * k = P.cP := by rw [hk_def]; field_simp
  set C := 2 * P.β * A + 2 * P.β * k * zb - (P.α - P.cH) + P.β * Q with hC
  have hj : ∀ j, q j * C - P.β * ((A + k * zb) + (-k) * z j) * ((A + k * zb) + (-k) * z j)
      ≤ t j * q j := by
    intro j
    have hf := foc P z t q hβ heq j (hpos j)
    have ht : t j = P.β * q j + P.β * Q - P.α + z j * P.cP + P.cH := by linarith
    have e : t j * q j - (q j * C - P.β * ((A + k * zb) + (-k) * z j) * ((A + k * zb) + (-k) * z j))
        = P.β * (q j - A + k * (z j - zb)) ^ 2 := by
      rw [ht, hC]; linear_combination (z j * q j) * (-hk)
    have : 0 ≤ P.β * (q j - A + k * (z j - zb)) ^ 2 := by positivity
    linarith
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at hsum
  have e2 : ∑ j, P.β * ((A + k * zb) + (-k) * z j) * ((A + k * zb) + (-k) * z j)
      = P.β * ∑ j, ((A + k * zb) + (-k) * z j) * ((A + k * zb) + (-k) * z j) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [e2, sum_aff_mul, sum_z hN z, sum_zz hN z, ← hzb] at hsum
  have ha : AgriSubsidy.Combined.abar P z 0 0 = P.α - zb * P.cP - P.cH := by
    rw [hzb]; unfold AgriSubsidy.Combined.abar; ring
  rw [ha]
  refine le_trans (le_of_eq ?_) hsum
  rw [hC, hA_def, hk_def]
  field_simp
  ring


lemma quad_mono (c a0 Qb Q : ℝ) (hc : 0 < c) (hQb : 0 < Qb) (ha : a0 < c * Qb) (hQ : Qb ≤ Q) :
    (c * Qb - a0) * Qb ≤ c * Q ^ 2 - a0 * Q := by
  have h1 : 0 ≤ Q - Qb := by linarith
  have h2 : 0 ≤ c * (Q + Qb) - a0 := by nlinarith
  nlinarith [mul_nonneg h1 h2]

lemma plant_alg (β n zb V a0 cP Qb p s Q b : ℝ) (hβ : 0 < β) (hn : 0 < n) (hzb : 0 < zb)
    (hV : 0 ≤ V) (hup : 0 < zb * p) (hQb : β * (n + 1) * Qb = n * (a0 + zb * p))
    (hpos : 0 < β * (zb * p) * Qb - n * V * p * (cP - p))
    (hQ : β * (n + 1) * Q = n * (a0 + zb * s)) (hQQ : Qb ≤ Q)
    (hb : β * b = β * (zb * s) * Q - n * V * s * (cP - s)) :
    β * (zb * p) * Qb - n * V * p * (cP - p) ≤ β * b := by
  have hp : 0 < p := by
    by_contra hc; push Not at hc; nlinarith
  have hsp : p ≤ s := by
    have : n * (a0 + zb * p) ≤ n * (a0 + zb * s) := by
      rw [← hQb, ← hQ]; exact mul_le_mul_of_nonneg_left hQQ (by positivity)
    have : zb * p ≤ zb * s := by nlinarith
    exact le_of_mul_le_mul_left this hzb
  have hk1 : 0 < β * zb * Qb - n * V * (cP - p) := by
    have : p * (β * zb * Qb - n * V * (cP - p)) > 0 := by nlinarith
    exact pos_of_mul_pos_right this hp.le
  have hkey : (n + 1) * V * (cP - p) < zb * (a0 + zb * p) := by
    have h3 : n * ((n + 1) * V * (cP - p)) < n * (zb * (a0 + zb * p)) := by
      have : (n + 1) * (β * zb * Qb - n * V * (cP - p)) > 0 := by positivity
      nlinarith
    exact lt_of_mul_lt_mul_left h3 hn.le
  have hs0 : 0 ≤ s := by linarith
  have hbr : 0 ≤ zb * (a0 + zb * p) + zb ^ 2 * s + (n + 1) * V * (s + p - cP) := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ n + 1) hV) hs0, sq_nonneg zb,
      mul_nonneg (sq_nonneg zb) hs0]
  have hid : (n + 1) * (β * b - (β * (zb * p) * Qb - n * V * p * (cP - p)))
      = n * (s - p) * (zb * (a0 + zb * p) + zb ^ 2 * s + (n + 1) * V * (s + p - cP)) := by
    linear_combination (n + 1) * hb + (zb * s) * hQ - (zb * p) * hQb
  have : 0 ≤ (n + 1) * (β * b - (β * (zb * p) * Qb - n * V * p * (cP - p))) := by
    rw [hid]; exact mul_nonneg (mul_nonneg hn.le (by linarith)) hbr
  have : 0 ≤ β * b - (β * (zb * p) * Qb - n * V * p * (cP - p)) :=
    by
      by_contra hc; push Not at hc
      have := mul_neg_of_pos_of_neg (by linarith : (0:ℝ) < n + 1) hc
      linarith
  linarith

end AgriProp10Aux

open AgriProp10Aux in
theorem solution {N : ℕ} (hN : 0 < N) (P : AgriSubsidy.Combined.Params) (z : Fin N → ℝ)
    (hS : Standing P z) (Qbar : ℝ)
    (hQ : QC P z 0 0 < Qbar)
    (hP : AllActiveAt P z (AgriSubsidy.Combined.combined z (sPP P z Qbar) 0))
    (hH : AllActiveAt P z (AgriSubsidy.Combined.combined z 0 (sHH P z Qbar)))
    (hC : AllActiveAt P z (AgriSubsidy.Combined.combined z (sCP P) (sCH P z Qbar))) :
    (Qbar ≤ QC P z P.cP 0 →
      optBudget P z (combinedProg z) Qbar ≤ optBudget P z (selectiveProg z) Qbar ∧
      optBudget P z (selectiveProg z) Qbar ≤ optBudget P z (plantingProg z) Qbar ∧
      optBudget P z (plantingProg z) Qbar ≤ optBudget P z (harvestingProg z) Qbar) ∧
    (QC P z P.cP 0 < Qbar →
      optBudget P z (combinedProg z) Qbar ≤ optBudget P z (selectiveProg z) Qbar ∧
      optBudget P z (selectiveProg z) Qbar ≤ optBudget P z (harvestingProg z) Qbar ∧
      optBudget P z (harvestingProg z) Qbar ≤ optBudget P z (plantingProg z) Qbar) ∧
    (vz z = 0 →
      optBudget P z (plantingProg z) Qbar = optBudget P z (harvestingProg z) Qbar ∧
      optBudget P z (harvestingProg z) Qbar = optBudget P z (combinedProg z) Qbar ∧
      optBudget P z (combinedProg z) Qbar = optBudget P z (selectiveProg z) Qbar) := by
  obtain ⟨_, hβ, -, hz⟩ := hS
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hV := vz_nonneg hN z
  have hzb : 0 < AgriSubsidy.Combined.zbar z := by
    unfold AgriSubsidy.Combined.zbar
    exact div_pos (Finset.sum_pos (fun j _ => hz j) ⟨⟨0, hN⟩, Finset.mem_univ _⟩) hn
  -- names for the key constants
  have hu_def : sHH P z Qbar = P.β * ((N : ℝ) + 1) / (N : ℝ) * Qbar
      - AgriSubsidy.Combined.abar P z 0 0 := rfl
  have hp_def : sPP P z Qbar = sHH P z Qbar / AgriSubsidy.Combined.zbar z := rfl
  have hsCH : sCH P z Qbar = sHH P z Qbar - P.cP * AgriSubsidy.Combined.zbar z / 2 := rfl
  have hsCP : sCP P = P.cP / 2 := rfl
  have hQbu : P.β * ((N : ℝ) + 1) * Qbar = (N : ℝ) * (AgriSubsidy.Combined.abar P z 0 0 + sHH P z Qbar) := by
    rw [hu_def]; field_simp; ring
  have hQ' : AgriSubsidy.Combined.abar P z 0 0 < P.β * ((N : ℝ) + 1) / (N : ℝ) * Qbar := by
    unfold QC at hQ
    have h1 : (N : ℝ) * AgriSubsidy.Combined.abar P z 0 0 < P.β * ((N : ℝ) + 1) * Qbar := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)] at hQ; linarith
    rw [div_mul_eq_mul_div, lt_div_iff₀ hn]; linarith
  have hu : 0 < sHH P z Qbar := by rw [hu_def]; linarith
  have hzp : AgriSubsidy.Combined.zbar z * sPP P z Qbar = sHH P z Qbar := by
    rw [hp_def]; field_simp
  have hp : 0 < sPP P z Qbar := by rw [hp_def]; positivity
  have hc : 0 < P.β * ((N : ℝ) + 1) / (N : ℝ) := by positivity
  -- harvesting design
  obtain ⟨qH, heqH, hposH⟩ := hH
  obtain ⟨dH1, dH2⟩ := combined_design hN P z qH hβ 0 (sHH P z Qbar) heqH hposH
  have hQH : ∑ j, qH j = Qbar := by
    have : P.β * ((N : ℝ) + 1) * (∑ j, qH j) = P.β * ((N : ℝ) + 1) * Qbar := by
      rw [dH1, hQbu]; ring
    exact mul_left_cancel₀ (by positivity) this
  have hQbar : 0 < Qbar := by
    rw [← hQH]; exact Finset.sum_pos (fun j _ => hposH j) ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  set bH := ∑ j, AgriSubsidy.Combined.combined z 0 (sHH P z Qbar) j * qH j with hbH_def
  have hbH : bH = sHH P z Qbar * Qbar := by
    rw [hQH] at dH2
    have : P.β * bH = P.β * (sHH P z Qbar * Qbar) := by rw [dH2]; ring
    exact mul_left_cancel₀ hβ.ne' this
  -- planting design
  obtain ⟨qP, heqP, hposP⟩ := hP
  obtain ⟨dP1, dP2⟩ := combined_design hN P z qP hβ (sPP P z Qbar) 0 heqP hposP
  have hQP : ∑ j, qP j = Qbar := by
    have : P.β * ((N : ℝ) + 1) * (∑ j, qP j) = P.β * ((N : ℝ) + 1) * Qbar := by
      rw [dP1, hQbu, hzp]; ring
    exact mul_left_cancel₀ (by positivity) this
  set bP := ∑ j, AgriSubsidy.Combined.combined z (sPP P z Qbar) 0 j * qP j with hbP_def
  have hbP : P.β * bP = P.β * (sHH P z Qbar) * Qbar
      - (N : ℝ) * vz z * sPP P z Qbar * (P.cP - sPP P z Qbar) := by
    rw [dP2, hQP, hzp]; ring
  have hbPpos : 0 < bP := by
    rw [hbP_def]
    refine Finset.sum_pos (fun j _ => ?_) ⟨⟨0, hN⟩, Finset.mem_univ _⟩
    simp only [AgriSubsidy.Combined.combined]
    have := hposP j; have := hz j; positivity
  -- combined design
  obtain ⟨qC, heqC, hposC⟩ := hC
  obtain ⟨dC1, dC2⟩ := combined_design hN P z qC hβ (sCP P) (sCH P z Qbar) heqC hposC
  have hzC : AgriSubsidy.Combined.zbar z * sCP P + sCH P z Qbar = sHH P z Qbar := by
    rw [hsCP, hsCH]; ring
  have hQC : ∑ j, qC j = Qbar := by
    have : P.β * ((N : ℝ) + 1) * (∑ j, qC j) = P.β * ((N : ℝ) + 1) * Qbar := by
      rw [dC1, hQbu, add_assoc, hzC]
    exact mul_left_cancel₀ (by positivity) this
  set bC := ∑ j, AgriSubsidy.Combined.combined z (sCP P) (sCH P z Qbar) j * qC j with hbC_def
  set L := sHH P z Qbar * Qbar - (N : ℝ) * vz z * P.cP ^ 2 / (4 * P.β) with hL_def
  have hbC : bC = L := by
    have : P.β * bC = P.β * L := by
      rw [dC2, hQC, hzC, hL_def, hsCP]; field_simp; ring
    exact mul_left_cancel₀ hβ.ne' this
  -- general lower bound
  have hLow : ∀ prog b, b ∈ feasibleBudgets P z prog Qbar → L ≤ b := by
    rintro prog b ⟨t, -, q, heq, hpos, hQq, rfl⟩
    have h1 := lower_bound hN P z t q hβ heq hpos
    have h2 := quad_mono _ _ _ _ hc hQbar hQ' hQq
    rw [← hu_def] at h2
    rw [hL_def]; linarith
  -- harvesting optimum
  have hBH : optBudget P z (harvestingProg z) Qbar = bH := by
    apply IsLeast.csInf_eq
    refine ⟨⟨_, ⟨sHH P z Qbar, rfl⟩, qH, heqH, hposH, hQH.ge, rfl⟩, ?_⟩
    rintro b ⟨t, ⟨s, rfl⟩, q, heq, hpos, hQq, rfl⟩
    obtain ⟨e1, e2⟩ := combined_design hN P z q hβ 0 s heq hpos
    have hs : sHH P z Qbar ≤ s := by
      have : (N : ℝ) * (AgriSubsidy.Combined.abar P z 0 0 + sHH P z Qbar)
          ≤ (N : ℝ) * (AgriSubsidy.Combined.abar P z 0 0 + s) := by
        have := mul_le_mul_of_nonneg_left hQq (by positivity : (0:ℝ) ≤ P.β * ((N : ℝ) + 1))
        rw [hQbu] at this; rw [e1] at this; linarith
      have := le_of_mul_le_mul_left this hn
      linarith
    have hb : ∑ j, AgriSubsidy.Combined.combined z 0 s j * q j = s * ∑ j, q j := by
      have : P.β * (∑ j, AgriSubsidy.Combined.combined z 0 s j * q j) = P.β * (s * ∑ j, q j) := by
        rw [e2]; ring
      exact mul_left_cancel₀ hβ.ne' this
    rw [hbH, hb]
    exact mul_le_mul hs hQq hQbar.le (by linarith)
  -- planting optimum
  have hBP : optBudget P z (plantingProg z) Qbar = bP := by
    apply IsLeast.csInf_eq
    refine ⟨⟨_, ⟨sPP P z Qbar, rfl⟩, qP, heqP, hposP, hQP.ge, rfl⟩, ?_⟩
    rintro b ⟨t, ⟨s, rfl⟩, q, heq, hpos, hQq, rfl⟩
    obtain ⟨e1, e2⟩ := combined_design hN P z q hβ s 0 heq hpos
    have hQbp : P.β * ((N : ℝ) + 1) * Qbar = (N : ℝ) * (AgriSubsidy.Combined.abar P z 0 0
        + AgriSubsidy.Combined.zbar z * sPP P z Qbar) := by rw [hQbu, hzp]
    have hpos' : 0 < P.β * (AgriSubsidy.Combined.zbar z * sPP P z Qbar) * Qbar
        - (N : ℝ) * vz z * sPP P z Qbar * (P.cP - sPP P z Qbar) := by
      rw [hzp, ← hbP]; positivity
    have := plant_alg P.β (N : ℝ) (AgriSubsidy.Combined.zbar z) (vz z)
      (AgriSubsidy.Combined.abar P z 0 0) P.cP Qbar (sPP P z Qbar) s (∑ j, q j)
      (∑ j, AgriSubsidy.Combined.combined z s 0 j * q j) hβ hn hzb hV (by rw [hzp]; exact hu)
      hQbp hpos' (by rw [e1]; ring) hQq (by rw [e2]; ring)
    rw [hzp, ← hbP] at this
    exact le_of_mul_le_mul_left this hβ
  have hBC : optBudget P z (combinedProg z) Qbar = L := by
    apply IsLeast.csInf_eq
    refine ⟨⟨_, ⟨(sCP P, sCH P z Qbar), rfl⟩, qC, heqC, hposC, hQC.ge, hbC.symm⟩, ?_⟩
    exact fun b hb => hLow _ b hb
  -- selective program
  have hselP : selective z (sPP P z Qbar) 0 = AgriSubsidy.Combined.combined z (sPP P z Qbar) 0 := by
    funext j
    simp only [selective, AgriSubsidy.Combined.combined, add_zero]
    have := hz j
    exact max_eq_left (by positivity)
  have hselH : selective z 0 (sHH P z Qbar) = AgriSubsidy.Combined.combined z 0 (sHH P z Qbar) := by
    funext j
    simp only [selective, AgriSubsidy.Combined.combined, mul_zero, zero_add]
    exact max_eq_right hu.le
  have memSP : bP ∈ feasibleBudgets P z (selectiveProg z) Qbar :=
    ⟨_, ⟨(sPP P z Qbar, 0), hselP⟩, qP, heqP, hposP, hQP.ge, rfl⟩
  have memSH : bH ∈ feasibleBudgets P z (selectiveProg z) Qbar :=
    ⟨_, ⟨(0, sHH P z Qbar), hselH⟩, qH, heqH, hposH, hQH.ge, rfl⟩
  have hbdd : BddBelow (feasibleBudgets P z (selectiveProg z) Qbar) := ⟨L, fun b hb => hLow _ b hb⟩
  have hBS1 : L ≤ optBudget P z (selectiveProg z) Qbar :=
    le_csInf ⟨_, memSP⟩ (fun b hb => hLow _ b hb)
  have hBS2 : optBudget P z (selectiveProg z) Qbar ≤ bP := csInf_le hbdd memSP
  have hBS3 : optBudget P z (selectiveProg z) Qbar ≤ bH := csInf_le hbdd memSH
  -- threshold
  have hQCc : QC P z P.cP 0 = (N : ℝ) / (P.β * ((N : ℝ) + 1))
      * (AgriSubsidy.Combined.abar P z 0 0 + AgriSubsidy.Combined.zbar z * P.cP) := by
    unfold QC AgriSubsidy.Combined.abar; ring
  have hthr : Qbar ≤ QC P z P.cP 0 ↔ sPP P z Qbar ≤ P.cP := by
    rw [hQCc, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    constructor
    · intro h
      have h2 : (N : ℝ) * (AgriSubsidy.Combined.abar P z 0 0 + sHH P z Qbar)
          ≤ (N : ℝ) * (AgriSubsidy.Combined.abar P z 0 0 + AgriSubsidy.Combined.zbar z * P.cP) := by
        rw [← hQbu]; linarith
      have h3 := le_of_mul_le_mul_left h2 hn
      have : AgriSubsidy.Combined.zbar z * sPP P z Qbar ≤ AgriSubsidy.Combined.zbar z * P.cP := by
        rw [hzp]; linarith
      exact le_of_mul_le_mul_left this hzb
    · intro h
      have h1 := mul_le_mul_of_nonneg_left h hzb.le
      rw [hzp] at h1
      have h2 := mul_le_mul_of_nonneg_left
        (add_le_add_right h1 (AgriSubsidy.Combined.abar P z 0 0)) hn.le
      linarith
  have hgap : P.β * bP - P.β * bH = -((N : ℝ) * vz z * sPP P z Qbar * (P.cP - sPP P z Qbar)) := by
    rw [hbP, hbH]; ring
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have hpc := hthr.mp h
    rw [hBC, hBP, hBH]
    refine ⟨hBS1, hBS2, ?_⟩
    have : 0 ≤ (N : ℝ) * vz z * sPP P z Qbar * (P.cP - sPP P z Qbar) := by
      have := sub_nonneg.mpr hpc; positivity
    exact le_of_mul_le_mul_left (by linarith) hβ
  · have hpc : P.cP < sPP P z Qbar := by
      by_contra hc'; push Not at hc'; exact absurd (hthr.mpr hc') (not_le.mpr h)
    rw [hBC, hBP, hBH]
    refine ⟨hBS1, hBS3, ?_⟩
    have : 0 ≤ (N : ℝ) * vz z * sPP P z Qbar * (sPP P z Qbar - P.cP) := by
      have := sub_nonneg.mpr hpc.le; positivity
    exact le_of_mul_le_mul_left (by linarith) hβ
  · have e1 : bP = bH := by
      have : P.β * bP = P.β * bH := by rw [hbP, hbH, h]; ring
      exact mul_left_cancel₀ hβ.ne' this
    have e2 : L = bH := by rw [hL_def, hbH, h]; ring
    rw [hBC, hBP, hBH]
    refine ⟨e1, e2.symm, ?_⟩
    exact le_antisymm hBS1 (by linarith)
