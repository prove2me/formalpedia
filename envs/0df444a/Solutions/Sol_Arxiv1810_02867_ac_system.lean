-- Prove2me | solution 1 for Arxiv1810_02867.ac_system
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T21:49:26.759796+00:00
-- url     : https://prove2.me/submissions/d83ec14b-4461-42b8-b84d-aed456fd39cb

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

set_option autoImplicit false

open MeasureTheory Matrix

namespace S71R
open Arxiv1810_02867

lemma emb_upd0 (y : Plane) (s : ℝ) : Function.update (emb y) 0 s = emb (Function.update y 0 s) := by
  ext i; fin_cases i <;> simp [emb, Function.update]

lemma emb_upd2 (y : Plane) (s : ℝ) : Function.update (emb y) 2 s = emb (Function.update y 1 s) := by
  ext i; fin_cases i <;> simp [emb, Function.update]

lemma pd0 (f : Space → ℝ) (y : Plane) : pd (0 : Fin 3) f (emb y) = pd (0 : Fin 2) (restr f) y := by
  unfold pd restr; simp_rw [emb_upd0]; congr 1

lemma pd2 (f : Space → ℝ) (y : Plane) : pd (2 : Fin 3) f (emb y) = pd (1 : Fin 2) (restr f) y := by
  unfold pd restr; simp_rw [emb_upd2]; congr 1

lemma pd1 (f : Space → ℝ) (hf : ∀ x s, f (Function.update x 1 s) = f x) (x : Space) :
    pd (1 : Fin 3) f x = 0 := by
  unfold pd; simp_rw [hf]; simp

lemma ind_s {f : Space → ℝ → ℝ} (h : IndepX2 f) (t : ℝ) :
    ∀ x s, (fun y => f y t) (Function.update x 1 s) = (fun y => f y t) x := by
  intro x s; simp only [h x s]

lemma ind_v {f : Space → ℝ → Fin 3 → ℝ} (h : IndepX2 f) (t : ℝ) (k : Fin 3) :
    ∀ x s, (fun y => cmp f k y t) (Function.update x 1 s) = (fun y => cmp f k y t) x := by
  intro x s; simp only [Arxiv1810_02867.cmp, h x s]

end S71R

open Arxiv1810_02867 S71R in
theorem solution (rhoO : Space → Fin 3 → Fin 3 → ℝ) (xi : Space → Fin 3 → ℝ)
    (kappa : Space → ℝ) (v F : Space → ℝ → Fin 3 → ℝ) (pr q : Space → ℝ → ℝ)
    (hiv : IndepX2 v) (hipr : IndepX2 pr) (hiF : IndepX2 F) (hiq : IndepX2 q)
    (hirho : IndepX2 rhoO) (hixi : IndepX2 xi) (hikappa : IndepX2 kappa)
    (hrhosym : ∀ x i j, rhoO x i j = rhoO x j i)
    (hrho0 : ∀ x, rhoO x 0 1 = 0 ∧ rhoO x 2 1 = 0) (hxi2 : ∀ x, xi x 1 = 0)
    (hA : AcousticEqs rhoO xi kappa v pr F q) :
    ACSystem (restr rhoO) (restr xi) (restr kappa) (restr v) (restr pr) (restr F) (restr q) := by
  intro y t
  obtain ⟨hm, hc⟩ := hA (emb y) t
  have hm0 := hm 0
  have hm2 := hm 2
  simp only [Fin.sum_univ_three] at hm0 hm2 hc
  have e1 : pdx (1 : Fin 3) (cmp v 1) (emb y) t = 0 := pd1 _ (ind_v hiv t 1) _
  have e2 : pdx (0 : Fin 3) (cmp v 0) (emb y) t = pdx (0 : Fin 2) (cmp (restr v) 0) y t :=
    pd0 (fun z => cmp v 0 z t) y
  have e3 : pdx (2 : Fin 3) (cmp v 2) (emb y) t = pdx (1 : Fin 2) (cmp (restr v) 2) y t :=
    pd2 (fun z => cmp v 2 z t) y
  have e4 : pdx (0 : Fin 3) pr (emb y) t = pdx (0 : Fin 2) (restr pr) y t := pd0 (fun z => pr z t) y
  have e5 : pdx (2 : Fin 3) pr (emb y) t = pdx (1 : Fin 2) (restr pr) y t := pd2 (fun z => pr z t) y
  rw [e1, e2, e3, hxi2] at hc
  rw [e4, (hrho0 _).1] at hm0
  rw [e5, (hrho0 _).2] at hm2
  rw [hrhosym (emb y) 0 2] at hm0
  refine ⟨?_, ?_, ?_⟩
  · simp only [restr] at hc ⊢; unfold pdt at *; simp only [Arxiv1810_02867.cmp, restr] at *; linarith
  · simp only [restr] at hm0 ⊢; unfold pdt at *; simp only [Arxiv1810_02867.cmp, restr] at *; linarith
  · simp only [restr] at hm2 ⊢; unfold pdt at *; simp only [Arxiv1810_02867.cmp, restr] at *; linarith
