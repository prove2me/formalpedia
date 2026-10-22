-- Prove2me | solution 1 for AdaGrad.Diag.eq_14
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T10:40:50.004398+00:00
-- url     : https://prove2.me/submissions/be38c2a6-7dab-4cb9-9102-b444e92de794

import Mathlib
import Definitions.Def_AdaGrad_Diag_Setup

open AdaGrad.Diag Finset

private lemma s_mono_step {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d))
    (t : ℕ) (i : Fin d) : s g t i ≤ s g (t+1) i := by
  unfold s
  apply Real.sqrt_le_sqrt
  rw [sum_Icc_succ_top (by omega)]
  exact le_add_of_nonneg_right (sq_nonneg _)

private lemma coord_square_bound {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    (v i)^2 ≤ (supNorm v)^2 := by
  have hi : |v i| ≤ supNorm v :=
    le_ciSup (Finite.bddAbove_range (fun j : Fin d => |v j|)) i
  nlinarith [abs_nonneg (v i), sq_abs (v i)]

private lemma telescope (a : ℕ → ℝ) (T : ℕ) (hT : 1 ≤ T) :
    (∑ t ∈ Ico 1 T, (a (t+1)-a t)) = a T-a 1 := by
  induction T with
  | zero => omega
  | succ T ih =>
    by_cases h : T = 0
    · subst T
      simp
    · rw [sum_Ico_succ_top (by omega), ih (by omega)]
      ring

theorem solution {d : ℕ} (δ : ℝ) (x g : ℕ → EuclideanSpace ℝ (Fin d))
    (xstar : EuclideanSpace ℝ (Fin d)) (T : ℕ) (hT : 1 ≤ T) :
    ∑ t ∈ Finset.Ico 1 T,
        (bregman (adaWeights δ g (t + 1)) xstar (x (t + 1))
          - bregman (adaWeights δ g t) xstar (x (t + 1)))
      ≤ (1 / 2) * ∑ t ∈ Finset.Ico 1 T,
          supNorm (xstar - x (t + 1)) ^ 2 * ∑ i, (s g (t + 1) i - s g t i) ∧
    (1 / 2) * ∑ t ∈ Finset.Ico 1 T,
          supNorm (xstar - x (t + 1)) ^ 2 * ∑ i, (s g (t + 1) i - s g t i)
      ≤ (1 / 2) * (Finset.Icc 1 T).sup' (Finset.nonempty_Icc.mpr hT)
            (fun t => supNorm (xstar - x t) ^ 2) * ∑ i, s g T i
        - (1 / 2) * supNorm (xstar - x 1) ^ 2 * ∑ i, s g 1 i := by
  classical
  let R := (Icc 1 T).sup' (nonempty_Icc.mpr hT) (fun t => supNorm (xstar-x t)^2)
  have hR (t : ℕ) (ht : t ∈ Icc 1 T) : supNorm (xstar-x t)^2 ≤ R :=
    le_sup' (f := fun t => supNorm (xstar-x t)^2) ht
  have hS : 0 ≤ ∑ i, s g 1 i := sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hinc (t : ℕ) : 0 ≤ ∑ i, (s g (t+1) i-s g t i) :=
    sum_nonneg fun i _ => sub_nonneg.mpr (s_mono_step g t i)
  constructor
  · have hp (t : ℕ) :
        bregman (adaWeights δ g (t+1)) xstar (x (t+1)) -
          bregman (adaWeights δ g t) xstar (x (t+1)) ≤
        (1/2) * (supNorm (xstar-x (t+1))^2 * ∑ i, (s g (t+1) i-s g t i)) := by
      have hs : (∑ i, (s g (t+1) i-s g t i)*(xstar i-x (t+1) i)^2) ≤
          ∑ i, (s g (t+1) i-s g t i)*supNorm (xstar-x (t+1))^2 := by
        apply sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (s_mono_step g t i))
        simpa using coord_square_bound (xstar-x (t+1)) i
      have he : bregman (adaWeights δ g (t+1)) xstar (x (t+1)) -
          bregman (adaWeights δ g t) xstar (x (t+1)) =
          (1/2) * ∑ i, (s g (t+1) i-s g t i)*(xstar i-x (t+1) i)^2 := by
        unfold bregman adaWeights
        rw [← mul_sub, ← sum_sub_distrib]
        congr 1
        apply sum_congr rfl
        intro i _
        ring
      rw [he]
      rw [← sum_mul] at hs
      nlinarith
    calc
      _ ≤ ∑ t ∈ Ico 1 T,
          (1/2) * (supNorm (xstar-x (t+1))^2 * ∑ i, (s g (t+1) i-s g t i)) :=
        sum_le_sum fun t _ => hp t
      _ = _ := (mul_sum ..).symm
  · have hb : (∑ t ∈ Ico 1 T,
          supNorm (xstar-x (t+1))^2 * ∑ i, (s g (t+1) i-s g t i)) ≤
          R * ((∑ i, s g T i)-(∑ i, s g 1 i)) := by
      calc
        _ ≤ ∑ t ∈ Ico 1 T, R * ∑ i, (s g (t+1) i-s g t i) := by
          apply sum_le_sum
          intro t ht
          apply mul_le_mul_of_nonneg_right _ (hinc t)
          exact hR (t+1) (mem_Icc.mpr ⟨by omega, by have := (mem_Ico.mp ht).2; omega⟩)
        _ = _ := by
          rw [← mul_sum]
          congr 1
          simp_rw [sum_sub_distrib]
          simpa only [sum_sub_distrib] using telescope (fun t => ∑ i, s g t i) T hT
    have hfirst := mul_le_mul_of_nonneg_right (hR 1 (mem_Icc.mpr ⟨le_rfl,hT⟩)) hS
    change (1/2) * _ ≤ (1/2) * R * _ - _
    nlinarith
