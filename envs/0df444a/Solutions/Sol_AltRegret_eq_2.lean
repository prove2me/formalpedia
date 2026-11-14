-- Prove2me | solution 1 for AltRegret.eq_2
-- status  : ACCEPTED   (prove)
-- author  : @Weiqiang
-- created : 2026-11-13T19:28:08.467295+00:00
-- url     : https://prove2.me/submissions/851de10f-64dd-437d-be68-4f2149488a37

import Definitions.Def_AltRegret_potential
open AltRegret Set

private lemma exists_max_sum {d : ℕ} (b v : Fin d → ℝ) (β : ℝ) (hβ : 0 ≤ β) :
    let F := fun y : ℝ => ∑ i, Real.exp (b i-β*(v i-y)^2)
    ∃ m : ℝ, ∀ y, F y ≤ F m := by
  intro F
  let R := ∑ i, |v i|
  have hR : 0 ≤ R := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hv (i) : |v i| ≤ R :=
    Finset.single_le_sum (f := fun j => |v j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hF : Continuous F := by dsimp [F]; fun_prop
  obtain ⟨m,_,hm⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (show -R ≤ R by linarith)) hF.continuousOn
  refine ⟨m,fun y => ?_⟩
  have compare (z : ℝ) (hz : z ∈ Icc (-R) R) (hd : ∀ i, (v i-z)^2 ≤ (v i-y)^2) : F y ≤ F m :=
    (Finset.sum_le_sum fun i _ => Real.exp_le_exp.mpr
      (sub_le_sub_left (mul_le_mul_of_nonneg_left (hd i) hβ) _)).trans (isMaxOn_iff.mp hm z hz)
  by_cases hl : y < -R
  · apply compare (-R) ⟨le_rfl,by linarith⟩
    intro i
    have := (abs_le.mp (hv i)).1
    nlinarith [mul_nonneg (show 0 ≤ -R-y by linarith) (show 0 ≤ 2*v i+R-y by linarith)]
  by_cases hr : R < y
  · apply compare R ⟨by linarith,le_rfl⟩
    intro i
    have := (abs_le.mp (hv i)).2
    nlinarith [mul_nonneg (show 0 ≤ y-R by linarith) (show 0 ≤ y+R-2*v i by linarith)]
  exact isMaxOn_iff.mp hm y ⟨le_of_not_gt hl,le_of_not_gt hr⟩

theorem solution {d : ℕ} (η β : ℝ) (hβ : 0 ≤ β) (c : ℕ → Fin d → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    (∀ θ : ℝ, potentialObjective η β c t θ ≤ potentialObjective η β c t (theta η β c t)) ∧
    potential η β c t = potentialObjective η β c t (theta η β c t) ∧
    potential η β c 1 = Real.log d := by
  classical
  cases d with
  | zero => simp [potential,potentialObjective,ciSup_const]
  | succ d =>
    let v := lossAt c (t-1)
    let b := fun i => -η * effCumLoss c (t-1) i
    let Z := fun y : ℝ => ∑ i, Real.exp (b i-β*(v i-y)^2)
    let B := η * ∑ s ∈ Finset.Icc 1 (t-1), ∑ j, (lossAt c (s-1) j + lossAt c s j) * play η β c s j
    have hZ (y) : 0 < Z y := Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
    have hobj (y) : thetaObjective η β c t y = Real.log (Z y) := rfl
    obtain ⟨m,hm⟩ := exists_max_sum b v β hβ
    have hex : ∃ y, ∀ z, thetaObjective η β c t z ≤ thetaObjective η β c t y :=
      ⟨m,fun z => Real.log_le_log (hZ _) (hm z)⟩
    have hmax (z) : thetaObjective η β c t z ≤ thetaObjective η β c t (theta η β c t) := by
      unfold theta
      rw [dif_pos hex]
      exact Classical.choose_spec hex z
    have hshift (y) : potentialObjective η β c t y = B + thetaObjective η β c t y := by
      rw [hobj, ← Real.log_exp B, ← Real.log_mul (Real.exp_pos _).ne' (hZ y).ne']
      congr 1
      dsimp [potentialObjective,Z]
      rw [Finset.mul_sum]
      apply congrArg Real.log
      apply Finset.sum_congr rfl
      intro i _
      rw [← Real.exp_add]
      congr 1
      dsimp [regretVector,B,b,v,effCumLoss]
      ring
    have hpot (z) : potentialObjective η β c t z ≤ potentialObjective η β c t (theta η β c t) := by
      rw [hshift,hshift]; linarith [hmax z]
    refine ⟨hpot,ciSup_eq_of_forall_le_of_forall_lt_exists_gt hpot (fun l hl => ⟨_,hl⟩),?_⟩
    have hzero : potentialObjective η β c 1 0 = Real.log (d+1 : ℕ) := by
      simp [potentialObjective,regretVector,lossAt]
    apply ciSup_eq_of_forall_le_of_forall_lt_exists_gt _ (fun l hl => ⟨0,by rwa [hzero]⟩)
    intro y
    have he : Real.exp (-(β*(0-y)^2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hβ (sq_nonneg _)))
    simp [potentialObjective,regretVector,lossAt]
    first
    | exact Real.log_le_log (by positivity) (by nlinarith)
    | apply Real.log_le_log (by positivity); simpa using mul_le_mul_of_nonneg_left he (show (0:ℝ) ≤ d+1 by positivity)
