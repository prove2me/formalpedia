-- Prove2me | solution 1 for AdaptiveStepIPM.WideNbhd.lemma_2c
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:58:55.173435+00:00
-- url     : https://prove2.me/submissions/f4a3fb73-482f-4fb4-9f73-632a9ef65164

import Mathlib
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Neighborhoods
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Algorithm2

open AdaptiveStepIPM.WideNbhd Matrix

private theorem residual_sq (z μ γ : ℝ) (hz : 0 < z) (hμ : 0 ≤ μ) (hγ : 0 ≤ γ)
    (hbound : γ * μ ≤ 2 * z) :
    ((γ * μ - z) / Real.sqrt z)^2 ≤ z := by
  have hs := Real.sqrt_pos.mpr hz
  have hs2 := Real.sq_sqrt hz.le
  rw [div_pow, hs2]
  apply (div_le_iff₀ hz).mpr
  nlinarith [mul_nonneg (mul_nonneg hγ hμ) (sub_nonneg.mpr hbound)]

private theorem residual_chain (z μ β γ : ℝ) (hz : 0 < z) (hμ : 0 < μ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγβ : γ ≤ 2 * (1 - β))
    (hlo : (1 - β) * μ ≤ z) (hhi : z ≤ (1 + β) * μ) :
    (γ / Real.sqrt (1 - β) - Real.sqrt (1 - β)) * Real.sqrt μ ≤
        Real.sqrt (1 - β) * Real.sqrt μ ∧
    (γ * μ - z) / Real.sqrt z ≤
        (γ / Real.sqrt (1 - β) - Real.sqrt (1 - β)) * Real.sqrt μ ∧
    (γ / Real.sqrt (1 + β) - Real.sqrt (1 + β)) * Real.sqrt μ ≤
        (γ * μ - z) / Real.sqrt z ∧
    -(Real.sqrt (1 + β) * Real.sqrt μ) ≤
        (γ / Real.sqrt (1 + β) - Real.sqrt (1 + β)) * Real.sqrt μ := by
  have ha := Real.sqrt_pos.mpr (show 0 < 1 - β by linarith)
  have hb := Real.sqrt_pos.mpr (show 0 < 1 + β by linarith)
  have hm := Real.sqrt_pos.mpr hμ
  have hu := Real.sqrt_pos.mpr hz
  have ha2 := Real.sq_sqrt (show 0 ≤ 1 - β by linarith)
  have hb2 := Real.sq_sqrt (show 0 ≤ 1 + β by linarith)
  have hm2 := Real.sq_sqrt hμ.le
  have hu2 := Real.sq_sqrt hz.le
  have hprodA : (Real.sqrt (1 - β) * Real.sqrt μ)^2 = (1 - β) * μ := by
    rw [mul_pow, ha2, hm2]
  have hprodB : (Real.sqrt (1 + β) * Real.sqrt μ)^2 = (1 + β) * μ := by
    rw [mul_pow, hb2, hm2]
  have hau : Real.sqrt (1 - β) * Real.sqrt μ ≤ Real.sqrt z := by
    nlinarith [mul_pos ha hm]
  have hub : Real.sqrt z ≤ Real.sqrt (1 + β) * Real.sqrt μ := by
    nlinarith [mul_pos hb hm]
  have hre : (γ * μ - z) / Real.sqrt z = γ * μ / Real.sqrt z - Real.sqrt z := by
    field_simp [hu.ne']
    nlinarith [hu2]
  have heA : (γ / Real.sqrt (1 - β) - Real.sqrt (1 - β)) * Real.sqrt μ =
      γ * μ / (Real.sqrt (1 - β) * Real.sqrt μ) - Real.sqrt (1 - β) * Real.sqrt μ := by
    field_simp [ha.ne', hm.ne']
    nlinarith [hm2]
  have heB : (γ / Real.sqrt (1 + β) - Real.sqrt (1 + β)) * Real.sqrt μ =
      γ * μ / (Real.sqrt (1 + β) * Real.sqrt μ) - Real.sqrt (1 + β) * Real.sqrt μ := by
    field_simp [hb.ne', hm.ne']
    nlinarith [hm2]
  have hdivA := div_le_div_of_nonneg_left (mul_pos hγ0 hμ).le (mul_pos ha hm) hau
  have hdivB := div_le_div_of_nonneg_left (mul_pos hγ0 hμ).le hu hub
  rw [heA, heB, hre]
  refine ⟨?_, by linarith, by linarith, ?_⟩
  · have hda : γ * μ / (Real.sqrt (1 - β) * Real.sqrt μ) ≤
        2 * (Real.sqrt (1 - β) * Real.sqrt μ) := by
      apply (div_le_iff₀ (mul_pos ha hm)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hγβ hμ.le]
    linarith
  · have := div_nonneg (mul_pos hγ0 hμ).le (mul_pos hb hm).le
    linarith


theorem solution {n m : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hγβ : γ ≤ 2 * (1 - β)) (x s : Fin n → ℝ) :
    ((x, s) ∈ NinfMinus A b c β → norm2 (rvec γ x s) ^ 2 ≤ (n : ℝ) * AdaptiveStepIPM.PredCorr.mu x s) ∧
      ((x, s) ∈ Ninf A b c β →
        (∀ j, (γ / Real.sqrt (1 - β) - Real.sqrt (1 - β)) * Real.sqrt (AdaptiveStepIPM.PredCorr.mu x s) ≤
              Real.sqrt (1 - β) * Real.sqrt (AdaptiveStepIPM.PredCorr.mu x s) ∧
            rvec γ x s j ≤ (γ / Real.sqrt (1 - β) - Real.sqrt (1 - β)) * Real.sqrt (AdaptiveStepIPM.PredCorr.mu x s) ∧
            (γ / Real.sqrt (1 + β) - Real.sqrt (1 + β)) * Real.sqrt (AdaptiveStepIPM.PredCorr.mu x s) ≤ rvec γ x s j ∧
            -(Real.sqrt (1 + β) * Real.sqrt (AdaptiveStepIPM.PredCorr.mu x s)) ≤
              (γ / Real.sqrt (1 + β) - Real.sqrt (1 + β)) * Real.sqrt (AdaptiveStepIPM.PredCorr.mu x s)) ∧
        normInf (rvec γ x s) ^ 2 ≤ (1 + β) * AdaptiveStepIPM.PredCorr.mu x s) := by
  classical
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hmu : ∀ (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j), 0 < AdaptiveStepIPM.PredCorr.mu x s := by
    intro hx hs
    unfold AdaptiveStepIPM.PredCorr.mu
    apply div_pos _ hnpos
    exact Finset.sum_pos (fun j _ => mul_pos (hx j) (hs j)) (by
      have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      exact Finset.univ_nonempty)
  have hsum : ∑ j, x j * s j = (n : ℝ) * AdaptiveStepIPM.PredCorr.mu x s := by
    unfold AdaptiveStepIPM.PredCorr.mu
    rw [mul_div_cancel₀ _ hnpos.ne']
    rfl
  constructor
  · intro h
    have hx := h.1.1
    have hs := h.1.2.1
    have hm := hmu hx hs
    have hlo : ∀ j, (1 - β) * AdaptiveStepIPM.PredCorr.mu x s ≤ x j * s j := by
      intro j
      have hv : |min (x j * s j - AdaptiveStepIPM.PredCorr.mu x s) 0| ≤
          normInfNeg (fun j => x j * s j - AdaptiveStepIPM.PredCorr.mu x s) :=
        le_ciSup (Finite.bddAbove_range (fun j => |min (x j * s j - AdaptiveStepIPM.PredCorr.mu x s) 0|)) j
      have hb := hv.trans h.2
      rw [abs_of_nonpos (min_le_right _ _)] at hb
      have := min_le_left (x j * s j - AdaptiveStepIPM.PredCorr.mu x s) 0
      linarith
    have hr : ∀ j, rvec γ x s j ^ 2 ≤ x j * s j := by
      intro j
      exact residual_sq _ _ _ (mul_pos (hx j) (hs j)) hm.le hγ0.le (by
        have := mul_le_mul_of_nonneg_right hγβ hm.le
        have := hlo j
        linarith)
    rw [norm2, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
    exact (Finset.sum_le_sum fun j _ => hr j).trans_eq hsum
  · intro h
    have hx := h.1.1
    have hs := h.1.2.1
    have hm := hmu hx hs
    have hbnds : ∀ j, (1 - β) * AdaptiveStepIPM.PredCorr.mu x s ≤ x j * s j ∧
        x j * s j ≤ (1 + β) * AdaptiveStepIPM.PredCorr.mu x s := by
      intro j
      have hv : |x j * s j - AdaptiveStepIPM.PredCorr.mu x s| ≤
          normInf (fun j => x j * s j - AdaptiveStepIPM.PredCorr.mu x s) :=
        le_ciSup (Finite.bddAbove_range (fun j => |x j * s j - AdaptiveStepIPM.PredCorr.mu x s|)) j
      have hb := abs_le.mp (hv.trans h.2)
      constructor <;> linarith [hb.1, hb.2]
    have hc : ∀ j, _ := fun j => residual_chain (x j * s j) (AdaptiveStepIPM.PredCorr.mu x s)
      β γ (mul_pos (hx j) (hs j)) hm hβ0 hβ1 hγ0 hγβ (hbnds j).1 (hbnds j).2
    refine ⟨hc, ?_⟩
    have hN : normInf (rvec γ x s) ≤ Real.sqrt (1 + β) * Real.sqrt (AdaptiveStepIPM.PredCorr.mu x s) := by
      have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      apply ciSup_le
      intro j
      apply abs_le.mpr
      have hj := hc j
      have hsqr : Real.sqrt (1 - β) ≤ Real.sqrt (1 + β) := Real.sqrt_le_sqrt (by linarith)
      have hmul := mul_le_mul_of_nonneg_right hsqr (Real.sqrt_nonneg (AdaptiveStepIPM.PredCorr.mu x s))
      exact ⟨hj.2.2.2.trans hj.2.2.1, hj.2.1.trans (hj.1.trans hmul)⟩
    have hN0 : 0 ≤ normInf (rvec γ x s) := by
      let j : Fin n := ⟨0, by omega⟩
      exact (abs_nonneg (rvec γ x s j)).trans
        (le_ciSup (Finite.bddAbove_range (fun j => |rvec γ x s j|)) j)
    have hsq : (Real.sqrt (1 + β) * Real.sqrt (AdaptiveStepIPM.PredCorr.mu x s))^2 =
        (1 + β) * AdaptiveStepIPM.PredCorr.mu x s := by
      rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 + β), Real.sq_sqrt hm.le]
    nlinarith [mul_nonneg (Real.sqrt_nonneg (1 + β)) (Real.sqrt_nonneg (AdaptiveStepIPM.PredCorr.mu x s))]

#print axioms solution
