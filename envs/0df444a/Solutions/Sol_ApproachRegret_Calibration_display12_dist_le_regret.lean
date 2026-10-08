-- Prove2me | solution 1 for ApproachRegret.Calibration.display12_dist_le_regret
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T10:50:59.59229+00:00
-- url     : https://prove2.me/submissions/10120ad3-26e0-4de9-9887-e5e8deaf5245

import Mathlib
import Definitions.Def_ApproachRegret_Calibration_Game

set_option autoImplicit false

open ApproachRegret.Calibration in
lemma p38219718_inner_eq {n : ℕ} (v x : ApproachRegret.ToOLO.E n) :
    inner ℝ v x = ∑ i, v i * x i := by
  simp [PiLp.inner_apply, mul_comm]

open ApproachRegret.Calibration in
lemma p38219718_inner_ge {n : ℕ} (v x : ApproachRegret.ToOLO.E n) (hx : x ∈ cube n) :
    -l1norm v ≤ inner ℝ v x := by
  rw [p38219718_inner_eq, l1norm, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h1 : |x i| ≤ 1 := hx i
  have h2 : |v i * x i| ≤ |v i| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) h1
  linarith [neg_abs_le (v i * x i)]

open ApproachRegret.Calibration in
lemma p38219718_sInf_le {n : ℕ} (G : ApproachRegret.ToOLO.E n) :
    sInf ((fun x => inner ℝ G x) '' cube n) ≤ -l1norm G := by
  set s : ApproachRegret.ToOLO.E n := WithLp.toLp 2 (fun i => if 0 ≤ G i then (-1 : ℝ) else 1)
    with hs
  have hsc : s ∈ cube n := by
    intro i
    simp only [hs, PiLp.toLp_apply]
    split_ifs <;> simp
  have hval : inner ℝ G s = -l1norm G := by
    rw [p38219718_inner_eq, l1norm, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hs, PiLp.toLp_apply]
    split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_neg (lt_of_not_ge h)]; ring
  have hbdd : BddBelow ((fun x => inner ℝ G x) '' cube n) := by
    refine ⟨-l1norm G, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact p38219718_inner_ge G x hx
  calc sInf ((fun x => inner ℝ G x) '' cube n) ≤ inner ℝ G s :=
        csInf_le hbdd ⟨s, hsc, rfl⟩
    _ = -l1norm G := hval

open ApproachRegret.Calibration in
lemma p38219718_l1norm_smul {n : ℕ} (c : ℝ) (v : ApproachRegret.ToOLO.E n) :
    l1norm (c • v) = |c| * l1norm v := by
  simp [l1norm, abs_mul, Finset.mul_sum]

open ApproachRegret.Calibration in
lemma p38219718_l1norm_neg {n : ℕ} (v : ApproachRegret.ToOLO.E n) :
    l1norm (-v) = l1norm v := by
  simp [l1norm]

open ApproachRegret.Calibration in
theorem solution (m T : ℕ) (hm : 1 ≤ m) (hT : 1 ≤ T)
    (w : ℕ → Fin (m + 1) → ℝ) (y : ℕ → ℝ) (θ : ℕ → ApproachRegret.ToOLO.E (m + 1))
    (hw : ∀ t, 1 ≤ t → t ≤ T → w t ∈ stdSimplex ℝ (Fin (m + 1)))
    (hy : ∀ t, 1 ≤ t → t ≤ T → y t ∈ Set.Icc (0 : ℝ) 1)
    (hθ : ∀ t, 1 ≤ t → t ≤ T → θ t ∈ cube (m + 1))
    (horacle : ∀ t, 1 ≤ t → t ≤ T → inner ℝ (payoff m (w t) (y t)) (θ t) ≤ eps m / 2)
    (hout : eps m / 2 < l1norm (avgPayoff m T w y)) :
    max 0 (l1norm (avgPayoff m T w y) - eps m / 2)
      ≤ (1 / (T : ℝ)) * linRegret (cube (m + 1)) T (fun t => -payoff m (w t) (y t)) θ := by
  set U : ApproachRegret.ToOLO.E (m + 1) := ∑ t ∈ Finset.Icc 1 T, payoff m (w t) (y t) with hU
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have havg : l1norm (avgPayoff m T w y) = (1 / (T : ℝ)) * l1norm U := by
    rw [avgPayoff, p38219718_l1norm_smul, abs_of_pos (by positivity)]
  -- the sInf term
  have hfun : (fun x => ∑ t ∈ Finset.Icc 1 T, inner ℝ (-payoff m (w t) (y t)) x)
      = (fun x => inner ℝ (-U) x) := by
    funext x
    rw [hU, ← Finset.sum_neg_distrib, sum_inner]
  have hinf : sInf ((fun x => ∑ t ∈ Finset.Icc 1 T, inner ℝ (-payoff m (w t) (y t)) x) ''
      cube (m + 1)) ≤ -l1norm U := by
    rw [hfun]
    have := p38219718_sInf_le (-U)
    rwa [p38219718_l1norm_neg] at this
  have hsum : ∑ t ∈ Finset.Icc 1 T, inner ℝ (-payoff m (w t) (y t)) (θ t)
      ≥ -((T : ℝ) * (eps m / 2)) := by
    have : ∑ t ∈ Finset.Icc 1 T, inner ℝ (payoff m (w t) (y t)) (θ t)
        ≤ ∑ _t ∈ Finset.Icc 1 T, eps m / 2 := by
      apply Finset.sum_le_sum
      intro t ht
      rw [Finset.mem_Icc] at ht
      exact horacle t ht.1 ht.2
    simp only [inner_neg_left, Finset.sum_neg_distrib, Finset.sum_const, Nat.card_Icc,
      nsmul_eq_mul] at this ⊢
    simp only [Nat.add_sub_cancel] at this
    linarith
  have hR : linRegret (cube (m + 1)) T (fun t => -payoff m (w t) (y t)) θ
      ≥ l1norm U - (T : ℝ) * (eps m / 2) := by
    unfold linRegret
    linarith
  rw [havg] at hout ⊢
  have hkey : (1 / (T : ℝ)) * l1norm U - eps m / 2
      ≤ (1 / (T : ℝ)) * linRegret (cube (m + 1)) T (fun t => -payoff m (w t) (y t)) θ := by
    have h1 : (1 / (T : ℝ)) * (l1norm U - (T : ℝ) * (eps m / 2))
        ≤ (1 / (T : ℝ)) * linRegret (cube (m + 1)) T (fun t => -payoff m (w t) (y t)) θ :=
      mul_le_mul_of_nonneg_left hR (by positivity)
    have h2 : (1 / (T : ℝ)) * (l1norm U - (T : ℝ) * (eps m / 2))
        = (1 / (T : ℝ)) * l1norm U - eps m / 2 := by
      field_simp
    linarith
  exact max_le (by linarith) hkey
