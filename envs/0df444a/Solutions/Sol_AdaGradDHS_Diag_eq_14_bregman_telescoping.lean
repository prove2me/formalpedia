-- Prove2me | solution 1 for AdaGradDHS.Diag.eq_14_bregman_telescoping
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T19:56:40.487447+00:00
-- url     : https://prove2.me/submissions/1e08d564-76cf-416b-900c-475d8a90e0d9

import Mathlib
import Definitions.Def_AdaGradDHS_Diag_bregman
import Definitions.Def_AdaGradDHS_Diag_accNorm
import Definitions.Def_AdaGradDHS_Diag_adagradPsi
import Definitions.Def_AdaGradDHS_Diag_supNorm
import Definitions.Def_AdaGradDHS_Diag_maxSupDev

namespace Aux_AGBT

open AdaGradDHS.Diag

theorem breg_quad {d : ℕ} (c : Fin d → ℝ) (ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hψ : ∀ z, ψ z = 1 / 2 * ∑ i, c i * (z i) ^ 2) (x y : EuclideanSpace ℝ (Fin d)) :
    bregman ψ x y = 1 / 2 * ∑ i, c i * (x i - y i) ^ 2 := by
  have hi : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      HasFDerivAt (fun z : EuclideanSpace ℝ (Fin d) => c i * (z i) ^ 2)
        (c i • (((2 : ℕ) • (y i) ^ (2 - 1)) •
          (EuclideanSpace.proj i : StrongDual ℝ (EuclideanSpace ℝ (Fin d))))) y := by
    intro i _
    have hp : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin d) => z i)
        (EuclideanSpace.proj i : StrongDual ℝ (EuclideanSpace ℝ (Fin d))) y :=
      (EuclideanSpace.proj i : StrongDual ℝ (EuclideanSpace ℝ (Fin d))).hasFDerivAt.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun z => by simp)
    exact (hp.pow 2).const_mul (c i)
  have hs := (HasFDerivAt.fun_sum hi).const_mul (1 / 2 : ℝ)
  have hL : (1 / 2 : ℝ) • ∑ i ∈ (Finset.univ : Finset (Fin d)), c i • (((2 : ℕ) • (y i) ^ (2 - 1)) •
        (EuclideanSpace.proj i : StrongDual ℝ (EuclideanSpace ℝ (Fin d)))) =
      ∑ i, (c i * y i) • (EuclideanSpace.proj i : StrongDual ℝ (EuclideanSpace ℝ (Fin d))) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul, smul_smul]
    congr 1
    rw [nsmul_eq_mul]
    norm_num <;> ring
  have hfd := hs.congr_fderiv hL
  have hψf : ψ = fun z => 1 / 2 * ∑ i, c i * (z i) ^ 2 := funext hψ
  rw [← hψf] at hfd
  have hev : (∑ i, (c i * y i) • (EuclideanSpace.proj i : StrongDual ℝ (EuclideanSpace ℝ (Fin d))))
      (x - y) = ∑ i, c i * y i * (x i - y i) := by
    simp
  unfold bregman
  rw [gradient, InnerProductSpace.toDual_symm_apply, hfd.fderiv, hev, hψ x, hψ y]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem ent_le_sup {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (i : Fin d) : |v i| ≤ supNorm v := by
  unfold supNorm
  have h : ‖v i‖₊ ≤ Finset.univ.sup fun j => ‖v j‖₊ :=
    Finset.le_sup (f := fun j => ‖v j‖₊) (Finset.mem_univ i)
  have h2 : ((‖v i‖₊ : NNReal) : ℝ) ≤ ((Finset.univ.sup fun j => ‖v j‖₊ : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr h
  rw [coe_nnnorm, Real.norm_eq_abs] at h2
  exact h2

theorem sq_entry_le {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    (v i) ^ 2 ≤ supNorm v ^ 2 := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (ent_le_sup v i) 2
  rwa [sq_abs] at h

theorem acc_mono {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) (i : Fin d) :
    accNorm g t i ≤ accNorm g (t + 1) i := by
  unfold accNorm
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (by omega))
  intro _ _ _
  exact sq_nonneg _

theorem sup_le_max {d : ℕ} (x : ℕ → EuclideanSpace ℝ (Fin d)) (xstar : EuclideanSpace ℝ (Fin d))
    (T s : ℕ) (hs : s ∈ Finset.Icc 1 T) : supNorm (xstar - x s) ≤ maxSupDev x xstar T := by
  unfold supNorm maxSupDev
  rw [NNReal.coe_le_coe]
  exact Finset.le_sup (f := fun t => Finset.univ.sup fun i => ‖xstar i - x t i‖₊) hs

theorem supNorm_nonneg {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) : 0 ≤ supNorm v := by
  unfold supNorm
  exact NNReal.coe_nonneg _

theorem tele (F : ℕ → ℝ) (T : ℕ) (hT : 1 ≤ T) :
    ∑ t ∈ Finset.Ico 1 T, (F (t + 1) - F t) = F T - F 1 := by
  induction T, hT using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ih]
    ring

end Aux_AGBT

open AdaGradDHS.Diag in
theorem solution {d : ℕ} (δ : ℝ) (g x : ℕ → EuclideanSpace ℝ (Fin d)) (xstar : EuclideanSpace ℝ (Fin d))
    {T : ℕ} (hT : 1 ≤ T) :
    ∑ t ∈ Finset.Ico 1 T,
        (bregman (adagradPsi δ g (t + 1)) xstar (x (t + 1)) -
          bregman (adagradPsi δ g t) xstar (x (t + 1))) ≤
        1 / 2 * ∑ t ∈ Finset.Ico 1 T,
          supNorm (xstar - x (t + 1)) ^ 2 * ∑ i, (accNorm g (t + 1) i - accNorm g t i) ∧
      1 / 2 * ∑ t ∈ Finset.Ico 1 T,
          supNorm (xstar - x (t + 1)) ^ 2 * ∑ i, (accNorm g (t + 1) i - accNorm g t i) ≤
        1 / 2 * maxSupDev x xstar T ^ 2 * ∑ i, accNorm g T i -
          1 / 2 * supNorm (xstar - x 1) ^ 2 * ∑ i, accNorm g 1 i := by
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _
    rw [Aux_AGBT.breg_quad (fun i => δ + accNorm g (t + 1) i) (adagradPsi δ g (t + 1))
        (fun z => rfl),
      Aux_AGBT.breg_quad (fun i => δ + accNorm g t i) (adagradPsi δ g t) (fun z => rfl)]
    have key : ∑ i, (δ + accNorm g (t + 1) i) * (xstar i - x (t + 1) i) ^ 2 -
        ∑ i, (δ + accNorm g t i) * (xstar i - x (t + 1) i) ^ 2 =
        ∑ i, (accNorm g (t + 1) i - accNorm g t i) * (xstar i - x (t + 1) i) ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have key2 : ∑ i, (accNorm g (t + 1) i - accNorm g t i) * (xstar i - x (t + 1) i) ^ 2 ≤
        supNorm (xstar - x (t + 1)) ^ 2 * ∑ i, (accNorm g (t + 1) i - accNorm g t i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have hw : (xstar i - x (t + 1) i) ^ 2 ≤ supNorm (xstar - x (t + 1)) ^ 2 :=
        Aux_AGBT.sq_entry_le (xstar - x (t + 1)) i
      have hΔ : 0 ≤ accNorm g (t + 1) i - accNorm g t i := sub_nonneg.mpr (Aux_AGBT.acc_mono g t i)
      rw [mul_comm (supNorm (xstar - x (t + 1)) ^ 2)]
      exact mul_le_mul_of_nonneg_left hw hΔ
    linarith
  · have hΔ : ∀ t, ∑ i, (accNorm g (t + 1) i - accNorm g t i) =
        ∑ i, accNorm g (t + 1) i - ∑ i, accNorm g t i := fun t => Finset.sum_sub_distrib _ _
    have htel : ∑ t ∈ Finset.Ico 1 T, (∑ i, accNorm g (t + 1) i - ∑ i, accNorm g t i) =
        ∑ i, accNorm g T i - ∑ i, accNorm g 1 i :=
      Aux_AGBT.tele (fun t => ∑ i, accNorm g t i) T hT
    have hsum : ∑ t ∈ Finset.Ico 1 T,
        supNorm (xstar - x (t + 1)) ^ 2 * ∑ i, (accNorm g (t + 1) i - accNorm g t i) ≤
        maxSupDev x xstar T ^ 2 * (∑ i, accNorm g T i - ∑ i, accNorm g 1 i) := by
      rw [← htel, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro t ht
      rw [hΔ t]
      have hmem : t + 1 ∈ Finset.Icc 1 T := by
        rw [Finset.mem_Ico] at ht
        rw [Finset.mem_Icc]
        omega
      have h1 := Aux_AGBT.sup_le_max x xstar T (t + 1) hmem
      have hsq := pow_le_pow_left₀ (Aux_AGBT.supNorm_nonneg _) h1 2
      have hd : 0 ≤ ∑ i, accNorm g (t + 1) i - ∑ i, accNorm g t i :=
        sub_nonneg.mpr (Finset.sum_le_sum fun i _ => Aux_AGBT.acc_mono g t i)
      exact mul_le_mul_of_nonneg_right hsq hd
    have hF1 : 0 ≤ ∑ i, accNorm g 1 i :=
      Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
    have hmem1 : 1 ∈ Finset.Icc 1 T := by
      rw [Finset.mem_Icc]
      omega
    have h1 := Aux_AGBT.sup_le_max x xstar T 1 hmem1
    have hsq1 := pow_le_pow_left₀ (Aux_AGBT.supNorm_nonneg _) h1 2
    have h3 := mul_le_mul_of_nonneg_right hsq1 hF1
    linarith
