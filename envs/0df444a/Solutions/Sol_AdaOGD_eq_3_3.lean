-- Prove2me | solution 1 for AdaOGD.eq_3_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:08:24.65988+00:00
-- url     : https://prove2.me/submissions/896630db-5f4a-4fd9-bd15-0d66516e013c

import Mathlib
import Definitions.Def_AdaOGD_eta

open AdaOGD in
theorem solution {Ω : Type*} {N : ℕ} (M : Fin N → ℕ → Ω → ℕ) (T : ℕ) (ω : Ω) :
    ∑ t ∈ Finset.Icc 1 (T - 1), (⨆ i : Fin N, 1 / AdaOGD.eta M i (t + 1) ω)
      ≤ Real.log ((T : ℝ) + 1) * Real.sqrt (1 + (AdaOGD.maxDraw M T ω : ℝ)) := by
  have hH : ∀ m : ℕ, ∑ t ∈ Finset.Icc 1 m, (1:ℝ) / ((t:ℝ) + 1) ≤ Real.log ((m:ℝ) + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hm : (0:ℝ) < (m:ℝ) + 1 := by positivity
      have key : 1 / ((m:ℝ) + 1 + 1) ≤ Real.log ((m:ℝ) + 1 + 1) - Real.log ((m:ℝ) + 1) := by
        have h := Real.log_le_sub_one_of_pos (show 0 < ((m:ℝ) + 1) / ((m:ℝ) + 1 + 1) by positivity)
        rw [Real.log_div hm.ne' (by positivity)] at h
        have e : ((m:ℝ) + 1) / ((m:ℝ) + 1 + 1) - 1 = -(1 / ((m:ℝ) + 1 + 1)) := by
          rw [div_sub_one (by positivity)]
          ring
        linarith
      push_cast
      linarith
  have hT : ∀ t ∈ Finset.Icc 1 (T - 1), (⨆ i : Fin N, 1 / AdaOGD.eta M i (t + 1) ω) ≤
      Real.sqrt (1 + (AdaOGD.maxDraw M T ω : ℝ)) * (1 / ((t:ℝ) + 1)) := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    refine Real.iSup_le (fun i => ?_) (by positivity)
    unfold AdaOGD.eta
    rw [Nat.add_sub_cancel, one_div_div]
    have hr : AdaOGD.runMax M i t ω ≤ AdaOGD.maxDraw M T ω := by
      unfold AdaOGD.runMax AdaOGD.maxDraw
      apply Finset.sup_le
      intro s hs
      rw [Finset.mem_Icc] at hs
      have hsT : s ≤ T := by omega
      exact Finset.le_sup (f := fun p : Fin N × ℕ => M p.1 p.2 ω) (b := (i, s))
        (Finset.mem_product.2 ⟨Finset.mem_univ i, Finset.mem_Icc.2 ⟨hs.1, hsT⟩⟩)
    have hr' : (AdaOGD.runMax M i t ω : ℝ) ≤ (AdaOGD.maxDraw M T ω : ℝ) := by exact_mod_cast hr
    have hs : Real.sqrt (1 + (AdaOGD.runMax M i t ω : ℝ)) ≤
        Real.sqrt (1 + (AdaOGD.maxDraw M T ω : ℝ)) := Real.sqrt_le_sqrt (by linarith)
    push_cast
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right hs (by positivity)
  have hTT : ((T - 1 : ℕ) : ℝ) + 1 ≤ (T : ℝ) + 1 := by
    have : ((T - 1 : ℕ) : ℝ) ≤ T := by exact_mod_cast Nat.sub_le T 1
    linarith
  calc ∑ t ∈ Finset.Icc 1 (T - 1), (⨆ i : Fin N, 1 / AdaOGD.eta M i (t + 1) ω)
      ≤ ∑ t ∈ Finset.Icc 1 (T - 1), Real.sqrt (1 + (AdaOGD.maxDraw M T ω : ℝ)) * (1 / ((t:ℝ) + 1)) :=
        Finset.sum_le_sum hT
    _ = Real.sqrt (1 + (AdaOGD.maxDraw M T ω : ℝ)) * ∑ t ∈ Finset.Icc 1 (T - 1), (1 / ((t:ℝ) + 1)) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ Real.sqrt (1 + (AdaOGD.maxDraw M T ω : ℝ)) * Real.log (((T - 1 : ℕ) : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (hH (T - 1)) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (1 + (AdaOGD.maxDraw M T ω : ℝ)) * Real.log ((T : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) hTT) (Real.sqrt_nonneg _)
    _ = Real.log ((T : ℝ) + 1) * Real.sqrt (1 + (AdaOGD.maxDraw M T ω : ℝ)) := mul_comm _ _
