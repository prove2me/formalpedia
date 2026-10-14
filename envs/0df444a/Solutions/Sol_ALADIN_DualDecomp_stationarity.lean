-- Prove2me | solution 1 for ALADIN.DualDecomp.stationarity
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:57:11.340755+00:00
-- url     : https://prove2.me/submissions/96a9ab27-c523-4907-8a07-be2f0c9458e1

import Mathlib
import Definitions.Def_ALADIN_DualDecomp_Problem
import Definitions.Def_ALADIN_DualDecomp_Step

open Matrix ALADIN.DualDecomp

theorem solution {N n m nh : ℕ} (P : Problem N n m nh) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (i : Fin N) (yi : Fin n → ℝ) (κi : Fin nh → ℝ)
    (Ci : Matrix (Fin nh) (Fin n) ℝ)
    (hf : ContDiff ℝ 2 (P.f i)) (hh : ContDiff ℝ 2 (P.h i))
    (hstep1 : Step1Solution P 0 Sig x lam i yi κi) :
    grad (P.f i) yi + (P.A i)ᵀ *ᵥ lam + (Cstar P i yi)ᵀ *ᵥ κi = 0 ∧
    modGrad P i yi κi Ci + (P.A i)ᵀ *ᵥ lam + Ciᵀ *ᵥ κi = 0 := by
  let L : (Fin n → ℝ) →L[ℝ] ℝ :=
    ((dotProductBilin ℝ ℝ lam).comp (Matrix.mulVecLin (P.A i))).toContinuousLinearMap
  have hg : grad (decoupledObjective P 0 Sig x lam i) yi =
      grad (P.f i) yi + (P.A i)ᵀ *ᵥ lam := by
    have he : decoupledObjective P 0 Sig x lam i =
        P.f i + L := by
      ext z
      simp [decoupledObjective, L, dotProductBilin]
    ext k
    change (fderiv ℝ (decoupledObjective P 0 Sig x lam i) yi) (Pi.single k 1) = _
    rw [he, fderiv_add (hf.differentiable (by norm_num) yi) L.differentiableAt, L.fderiv]
    change (fderiv ℝ (P.f i) yi) (Pi.single k 1) + lam ⬝ᵥ (P.A i *ᵥ Pi.single k 1) = _
    rw [Matrix.mulVec_single_one]
    simp [grad, mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
  have hc : (Cstar P i yi)ᵀ *ᵥ κi =
      ∑ j, κi j • grad (fun z => P.h i z j) yi := by
    ext k
    simp only [mulVec, dotProduct, transpose_apply, Cstar, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hj
    · ring
    · have hk := (mul_eq_zero.mp (hstep1.2.2.2.1 j)).resolve_right hj
      simp [hk]
  have hs : grad (P.f i) yi + (P.A i)ᵀ *ᵥ lam + (Cstar P i yi)ᵀ *ᵥ κi = 0 := by
    rw [hc, ← hg]
    exact hstep1.2.2.2.2
  refine ⟨hs, ?_⟩
  simp only [modGrad, transpose_sub, sub_mulVec]
  linear_combination hs
