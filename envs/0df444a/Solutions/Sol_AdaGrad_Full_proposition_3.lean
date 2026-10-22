-- Prove2me | solution 1 for AdaGrad.Full.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T10:58:07.404296+00:00
-- url     : https://prove2.me/submissions/787b60e4-ad97-41fa-bd54-48b78f04fcaf

-- SPDX-License-Identifier: Apache-2.0
-- Uses Nickrobbins95's accepted AdaGrad.Full.lemma_16 as a theorem dependency.
-- The telescoping helpers are reused from suzukasan's diagonal Proposition 3 proof.
import Mathlib
import Definitions.Def_AdaGrad_Full_Algorithm2
import Theorems.Thm_AdaGrad_Full_lemma_16
open AdaGrad.Full
open scoped MatrixOrder InnerProductSpace

private lemma potential_telescope (B : ℕ → ℕ → ℝ) (T : ℕ) (hT : 1 ≤ T) :
    (∑ t ∈ Finset.Icc 1 T, (B t t - B t (t+1))) =
      B 1 1 - B T (T+1) + ∑ t ∈ Finset.Ico 1 T, (B (t+1) (t+1) - B t (t+1)) := by
  induction T, hT using Nat.le_induction with
  | base => simp
  | succ T hT ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ T+1), Finset.sum_Ico_succ_top hT, ih]
    ring

private lemma shift_telescope (a : ℕ → ℝ) (T : ℕ) :
    (∑ t ∈ Finset.Icc 1 T, (a (t+1)-a t)) = a (T+1)-a 1 := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ T+1), ih]
    ring

theorem solution {d : ℕ} (η : ℝ) (hη : 0 < η) (X : Set (EuclideanSpace ℝ (Fin d)))
    (hXc : Convex ℝ X) (hXcl : IsClosed X)
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (hf : ∀ t, ConvexOn ℝ Set.univ (f t))
    (ϕ : EuclideanSpace ℝ (Fin d) → ℝ) (hϕ : ConvexOn ℝ Set.univ ϕ)
    (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (x g : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) (hT : 1 ≤ T)
    (hH : ∀ t ∈ Finset.Icc 1 T, (H t).PosSemidef)
    (hrange : ∀ t ∈ Finset.Icc 1 T, g t ∈ LinearMap.range (Matrix.toEuclideanLin (H t)))
    (hrun : IsQuadMirrorDescentRun η X ϕ f H x g T)
    (hx1 : x 1 ∈ X) (hϕx1 : ∀ y ∈ X, ϕ (x 1) ≤ ϕ y)
    (xstar : EuclideanSpace ℝ (Fin d)) (hstar : xstar ∈ X) :
    AdaGrad.Diag.regret f ϕ x xstar T ≤
      1 / η * bregman (H 1) xstar (x 1)
        + 1 / η * ∑ t ∈ Finset.Ico 1 T,
            (bregman (H (t + 1)) xstar (x (t + 1)) - bregman (H t) xstar (x (t + 1)))
        + η / 2 * ∑ t ∈ Finset.Icc 1 T, dualNormSq (H t) (g t)  := by
  classical
  have hs := Finset.sum_le_sum (fun t (ht : t ∈ Finset.Icc 1 T) =>
    AdaGrad.Full.lemma_16 η hη X hXc hXcl f hf ϕ hϕ H x g T hrun t ht
      (hH t ht) (hrange t ht) xstar hstar)
  have heq : (∑ t ∈ Finset.Icc 1 T,
      (η * (f t (x t)-f t xstar) + η * (ϕ (x (t+1))-ϕ xstar))) =
      η * AdaGrad.Diag.regret f ϕ x xstar T + η * (ϕ (x (T+1))-ϕ (x 1)) := by
    rw [← shift_telescope (fun t => ϕ (x t)) T]
    simp only [AdaGrad.Diag.regret, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [heq, Finset.sum_add_distrib, ← Finset.mul_sum,
    potential_telescope (fun t k => bregman (H t) xstar (x k)) T hT] at hs
  have hTT : T ∈ Finset.Icc 1 T := Finset.mem_Icc.mpr ⟨hT,le_rfl⟩
  have hb : 0 ≤ bregman (H T) xstar (x (T+1)) := by
    unfold bregman mInner
    apply mul_nonneg (by norm_num)
    simpa using (Matrix.isPositive_toEuclideanLin_iff.mpr (hH T hTT)).re_inner_nonneg_right
      (xstar-x (T+1))
  have hp := mul_nonneg hη.le (sub_nonneg.mpr (hϕx1 _ (hrun T hTT).2.1))
  apply (mul_le_mul_iff_right₀ hη).mp
  have hhη : η ≠ 0 := ne_of_gt hη
  field_simp
  nlinarith
