-- Prove2me | solution 1 for Arxiv1810_02867.acoustic_constitutive_reorganisation
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T21:56:38.894712+00:00
-- url     : https://prove2.me/submissions/a17a2544-6b1f-4898-b691-32dd9d6b2825

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

set_option autoImplicit false

open MeasureTheory Matrix

namespace S71AR
open Arxiv1810_02867

lemma dlin (a : Fin 3 → ℝ) (c : ℝ) (v : ℝ → Fin 3 → ℝ) (p : ℝ → ℝ)
    (hv : ∀ j, Differentiable ℝ (fun t => v t j)) (hp : Differentiable ℝ p) (t : ℝ) :
    deriv (fun s => ∑ j, a j * v s j + c * p s) t =
      ∑ j, a j * deriv (fun s => v s j) t + c * deriv p t := by
  have h1 : HasDerivAt (fun s => ∑ j, a j * v s j) (∑ j, a j * deriv (fun s => v s j) t) t :=
    HasDerivAt.fun_sum fun j _ => ((hv j t).hasDerivAt.const_mul (a j))
  exact (h1.add ((hp t).hasDerivAt.const_mul c)).deriv

lemma pk (i j : Fin 3) (pr : Space → ℝ → ℝ) (x : Space) (t : ℝ) :
    pdx j (fun y s => -(kd i j * pr y s)) x t = -(kd i j * pdx j pr x t) := by
  unfold pdx pd kd
  split_ifs
  · simp only [one_mul]; exact deriv.neg
  · simp

end S71AR

open Arxiv1810_02867 S71AR in
theorem solution (rho : Space → Fin 3 → Fin 3 → ℝ)
    (S2 S1 : Space → Fin 3 → Fin 3 → Fin 3 → ℝ) (K : Space → ℝ)
    (mom v F : Space → ℝ → Fin 3 → ℝ) (pr Theta q : Space → ℝ → ℝ)
    (hK : ∀ x, K x ≠ 0) (hrho : ∀ x i k, rho x i k = rho x k i)
    (hS21 : ∀ x i k l, S2 x i k l = -S1 x k l i)
    (hbase : ElastoBase mom (fun x t i j => -(kd i j * pr x t))
      (fun x t k l => kd k l * Theta x t / 3) v F (fun x t k l => kd k l * q x t / 3))
    (hcon : WillisConst rho S2 S1 (fun x m n p' q' => kd m n * kd p' q' * K x) mom v
      (fun x t k l => kd k l * Theta x t / 3) (fun x t i j => -(kd i j * pr x t)))
    (hv : ∀ x j, Differentiable ℝ (fun t => v x t j))
    (hpr : ∀ x, Differentiable ℝ (fun t => pr x t)) :
    (∀ x t, Theta x t = -∑ j, zetaAc (K x) (S1 x) j * v x t j - kappaAc (K x) * pr x t) ∧
    (∀ x t i, mom x t i = ∑ j, rhoOAc (rho x) (K x) (S2 x) (S1 x) i j * v x t j +
        xiAc (K x) (S2 x) i * pr x t) ∧
    (∀ x i j, rhoOAc (rho x) (K x) (S2 x) (S1 x) i j = rhoOAc (rho x) (K x) (S2 x) (S1 x) j i) ∧
    (∀ x j, xiAc (K x) (S2 x) j = zetaAc (K x) (S1 x) j) ∧
    AcousticEqs (fun x => rhoOAc (rho x) (K x) (S2 x) (S1 x)) (fun x => xiAc (K x) (S2 x))
      (fun x => kappaAc (K x)) v pr F q := by
  have hT : ∀ x t, Theta x t = -∑ j, zetaAc (K x) (S1 x) j * v x t j - kappaAc (K x) * pr x t := by
    intro x t
    have e0 := (hcon x t).2 0 0
    have e1 := (hcon x t).2 1 1
    have e2 := (hcon x t).2 2 2
    simp (config := { decide := true }) only [kd, Fin.sum_univ_three, if_true, if_false, one_mul,
      zero_mul, mul_one, add_zero, zero_add, mul_zero] at e0 e1 e2
    simp only [zetaAc, kappaAc, Fin.sum_univ_three]
    have hk := hK x
    field_simp
    linear_combination (-1 : ℝ) * (e0 + e1 + e2)
  have hM : ∀ x t i, mom x t i = ∑ j, rhoOAc (rho x) (K x) (S2 x) (S1 x) i j * v x t j +
      xiAc (K x) (S2 x) i * pr x t := by
    intro x t i
    have e := (hcon x t).1 i
    have h0 := hT x t
    simp (config := { decide := true }) only [kd, Fin.sum_univ_three, if_true, if_false, one_mul,
      zero_mul, mul_one, add_zero, zero_add, mul_zero, zero_div] at e
    simp only [rhoOAc, xiAc, zetaAc, kappaAc, Fin.sum_univ_three] at h0 ⊢
    rw [e, h0]; ring
  have hsym : ∀ x i j, rhoOAc (rho x) (K x) (S2 x) (S1 x) i j =
      rhoOAc (rho x) (K x) (S2 x) (S1 x) j i := by
    intro x i j
    simp only [rhoOAc, hS21, Fin.sum_univ_three]
    rw [hrho x i j]; ring
  have hxz : ∀ x j, xiAc (K x) (S2 x) j = zetaAc (K x) (S1 x) j := by
    intro x j
    simp only [xiAc, zetaAc, hS21, Fin.sum_univ_three]; ring
  refine ⟨hT, hM, hsym, hxz, ?_⟩
  intro x t
  constructor
  · intro i
    have e := (hbase x t).1 i
    simp only [pk] at e
    have hs : ∑ j, -(kd i j * pdx j pr x t) = -pdx i pr x t := by
      simp [kd, Finset.sum_neg_distrib]
    rw [hs] at e
    have hd : pdt (cmp mom i) x t = ∑ j, rhoOAc (rho x) (K x) (S2 x) (S1 x) i j *
        pdt (cmp v j) x t + xiAc (K x) (S2 x) i * pdt pr x t := by
      unfold pdt Arxiv1810_02867.cmp
      rw [show (fun s => mom x s i) = fun s => ∑ j, rhoOAc (rho x) (K x) (S2 x) (S1 x) i j *
        v x s j + xiAc (K x) (S2 x) i * pr x s from funext fun s => hM x s i]
      exact dlin _ _ (v x) (pr x) (hv x) (hpr x) t
    rw [hd] at e
    linarith
  · have hd : pdt Theta x t = ∑ j, (-zetaAc (K x) (S1 x) j) * pdt (cmp v j) x t +
        (-kappaAc (K x)) * pdt pr x t := by
      unfold pdt Arxiv1810_02867.cmp
      rw [show (fun s => Theta x s) = fun s => ∑ j, (-zetaAc (K x) (S1 x) j) *
        v x s j + (-kappaAc (K x)) * pr x s from funext fun s => by
          rw [hT x s]; simp only [neg_mul, Finset.sum_neg_distrib]; ring]
      exact dlin _ _ (v x) (pr x) (hv x) (hpr x) t
    have hdk : ∀ k : Fin 3, pdt (fun y s => kd k k * Theta y s / 3) x t = pdt Theta x t / 3 := by
      intro k
      unfold pdt kd
      simp only [if_true, one_mul]
      rw [deriv_div_const]
    have e0 := (hbase x t).2 0 0
    have e1 := (hbase x t).2 1 1
    have e2 := (hbase x t).2 2 2
    simp only [hdk] at e0 e1 e2
    simp only [kd, if_true, one_mul] at e0 e1 e2
    simp only [Fin.sum_univ_three] at hd ⊢
    simp only [hxz, Fin.sum_univ_three]
    linear_combination (-1 : ℝ) * (e0 + e1 + e2) + hd
