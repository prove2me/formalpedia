-- Prove2me | solution 1 for AdaGradDHS.Diag.bregman_difference_bound
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-14T13:42:33.060981+00:00
-- url     : https://prove2.me/submissions/157e4b59-bd6f-418e-93cc-3e76dd01b971

import Definitions.Def_AdaGradDHS_Diag_bregman
import Definitions.Def_AdaGradDHS_Diag_accNorm
import Definitions.Def_AdaGradDHS_Diag_adagradPsi
import Definitions.Def_AdaGradDHS_Diag_supNorm
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators InnerProductSpace
open AdaGradDHS.Diag

private lemma quad_bregman {d : ℕ} (δ : ℝ) (g : ℕ → EuclideanSpace ℝ (Fin d))
    (t : ℕ) (x y : EuclideanSpace ℝ (Fin d)) :
    bregman (adagradPsi δ g t) x y =
      1 / 2 * ∑ i, (δ + accNorm g t i) * (x i-y i)^2 := by
  have hc (i : Fin d) := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).hasFDerivAt (x := y)
  have hi (i : Fin d) := ((hc i).mul (hc i)).const_mul (δ + accNorm g t i)
  have hd := (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)).const_mul (1/2 : ℝ)
  have hd' : HasFDerivAt (𝕜 := ℝ) (adagradPsi δ g t)
      ((1/2 : ℝ) • ∑ i : Fin d, (δ + accNorm g t i) •
        ((y i) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i +
          (y i) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i)) y := by
    convert hd using 1 <;> first
      | rfl
      | (funext z; simp only [adagradPsi, Pi.mul_apply, PiLp.proj_apply, sq])
      | simp only [PiLp.proj_apply]
  unfold bregman
  rw [inner_gradient_left, hd'.fderiv]
  simp only [adagradPsi, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.add_apply, PiLp.proj_apply, smul_eq_mul]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [PiLp.sub_apply]
  ring

private lemma coordinate_le_sup {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    |x i| ≤ supNorm x := by
  have h : ‖x i‖₊ ≤ Finset.univ.sup (fun j => ‖x j‖₊) := Finset.le_sup (f := fun j => ‖x j‖₊) (Finset.mem_univ i)
  have h' : (‖x i‖₊ : ℝ) ≤ ((Finset.univ.sup fun j => ‖x j‖₊ : NNReal) : ℝ) := by exact_mod_cast h
  simpa only [supNorm, coe_nnnorm, Real.norm_eq_abs] using h'

theorem solution {d : ℕ} (δ : ℝ) (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) (xstar y : EuclideanSpace ℝ (Fin d)) :
    bregman (adagradPsi δ g (t + 1)) xstar y - bregman (adagradPsi δ g t) xstar y =
        1 / 2 * ∑ i, (accNorm g (t + 1) i - accNorm g t i) * (xstar i - y i) ^ 2 ∧
      1 / 2 * ∑ i, (accNorm g (t + 1) i - accNorm g t i) * (xstar i - y i) ^ 2 ≤
        1 / 2 * supNorm (xstar - y) ^ 2 * ∑ i, |accNorm g (t + 1) i - accNorm g t i| := by
  constructor
  · rw [quad_bregman, quad_bregman, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · have hcoord (i : Fin d) : (xstar i-y i)^2 ≤ supNorm (xstar-y)^2 := by
      have ha := coordinate_le_sup (xstar-y) i
      have hs := pow_le_pow_left₀ (abs_nonneg ((xstar-y) i)) ha 2
      simpa only [sq_abs, PiLp.sub_apply] using hs
    calc
      _ ≤ 1/2 * ∑ i, |accNorm g (t+1) i-accNorm g t i| * supNorm (xstar-y)^2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro i hi
        exact (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)).trans
          (mul_le_mul_of_nonneg_left (hcoord i) (abs_nonneg _))
      _ = _ := by rw [← Finset.sum_mul]; ring

#print axioms solution





