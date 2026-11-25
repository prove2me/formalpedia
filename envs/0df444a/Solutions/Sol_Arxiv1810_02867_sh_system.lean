-- Prove2me | solution 1 for Arxiv1810_02867.sh_system
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T21:53:05.705951+00:00
-- url     : https://prove2.me/submissions/1d5b73e4-b600-48ca-9ed4-501bd0975855

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

namespace S71R
open Arxiv1810_02867

lemma zF {F : Space → ℝ → Fin 3 → ℝ} (h : IndepX2 F) (y : Plane) (t : ℝ) (l : Fin 3) :
    pdx (1 : Fin 3) (cmp F l) (emb y) t = 0 := pd1 _ (ind_v h t l) _

lemma aF (F : Space → ℝ → Fin 3 → ℝ) (y : Plane) (t : ℝ) (l : Fin 3) :
    pdx (0 : Fin 3) (cmp F l) (emb y) t = pdx (0 : Fin 2) (cmp (restr F) l) y t :=
  pd0 (fun z => cmp F l z t) y

lemma bF (F : Space → ℝ → Fin 3 → ℝ) (y : Plane) (t : ℝ) (l : Fin 3) :
    pdx (2 : Fin 3) (cmp F l) (emb y) t = pdx (1 : Fin 2) (cmp (restr F) l) y t :=
  pd2 (fun z => cmp F l z t) y

end S71R

namespace S71R
open Arxiv1810_02867

lemma zG {G : Space → ℝ → ℝ} (h : IndepX2 G) (y : Plane) (t : ℝ) :
    pdx (1 : Fin 3) G (emb y) t = 0 := pd1 _ (ind_s h t) _

lemma aG (G : Space → ℝ → ℝ) (y : Plane) (t : ℝ) :
    pdx (0 : Fin 3) G (emb y) t = pdx (0 : Fin 2) (restr G) y t := pd0 (fun z => G z t) y

lemma bG (G : Space → ℝ → ℝ) (y : Plane) (t : ℝ) :
    pdx (2 : Fin 3) G (emb y) t = pdx (1 : Fin 2) (restr G) y t := pd2 (fun z => G z t) y

lemma indT {T : Space → ℝ → Fin 3 → Fin 3 → ℝ} (h : IndepX2 T) (i j : Fin 3) :
    IndepX2 (fun y s' => T y s' i j) := by
  intro x s; simp only [h x s]

end S71R

open Arxiv1810_02867 S71R in
theorem solution (rhoO : Space → Fin 3 → Fin 3 → ℝ) (xi : Space → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (s : Space → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (v F : Space → ℝ → Fin 3 → ℝ)
    (tau h : Space → ℝ → Fin 3 → Fin 3 → ℝ)
    (hiv : IndepX2 v) (hitau : IndepX2 tau) (hiF : IndepX2 F) (hih : IndepX2 h)
    (hirho : IndepX2 rhoO) (hixi : IndepX2 xi) (his : IndepX2 s)
    (hrho0 : ∀ x, rhoO x 1 0 = 0 ∧ rhoO x 1 2 = 0)
    (hs0 : ∀ x, s x 0 1 0 0 = 0 ∧ s x 0 1 1 1 = 0 ∧ s x 0 1 2 2 = 0 ∧ s x 0 1 0 2 = 0 ∧
      s x 2 1 0 0 = 0 ∧ s x 2 1 1 1 = 0 ∧ s x 2 1 2 2 = 0 ∧ s x 2 1 0 2 = 0)
    (hxi0 : ∀ x, xi x 0 0 1 = 0 ∧ xi x 0 2 1 = 0 ∧ xi x 1 0 0 = 0 ∧ xi x 1 1 1 = 0 ∧
      xi x 1 2 2 = 0 ∧ xi x 1 0 2 = 0 ∧ xi x 2 0 1 = 0 ∧ xi x 2 2 1 = 0)
    (hxisym : ∀ x i m n, xi x i m n = xi x i n m)
    (htau : ∀ x t i j, tau x t i j = tau x t j i) (hh : ∀ x t k l, h x t k l = h x t l k)
    (hs : ∀ x k l m n, s x k l m n = s x l k m n ∧ s x k l m n = s x k l n m ∧
      s x k l m n = s x m n k l)
    (hE : ElastoEqs rhoO xi s v tau F h) :
    SHSystem (restr rhoO) (restr xi) (restr s) (restr v) (restr tau) (restr F) (restr h) := by
  intro y t
  obtain ⟨h1, h2⟩ := hE (emb y) t
  have a := h1 1
  have b := h2 0 1
  have c := h2 2 1
  simp only [Fin.sum_univ_three] at a b c
  rw [zG (indT hitau 1 1), aG, bG] at a
  rw [zF hiv, aF] at b
  rw [zF hiv, bF] at c
  have T01 : (fun y s' => tau y s' 0 1) = (fun y s' => tau y s' 1 0) :=
    funext fun y => funext fun s' => htau y s' 0 1
  have T21 : (fun y s' => tau y s' 2 1) = (fun y s' => tau y s' 1 2) :=
    funext fun y => funext fun s' => htau y s' 2 1
  have T20 : (fun y s' => tau y s' 2 0) = (fun y s' => tau y s' 0 2) :=
    funext fun y => funext fun s' => htau y s' 2 0
  rw [T01, T21, T20] at a b c
  set x := emb y with hx
  obtain ⟨r1, r2⟩ := hrho0 x
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := hs0 x
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := hxi0 x
  have e1 : xi x 1 0 1 = xi x 1 1 0 := hxisym x 1 0 1
  have e2 : xi x 1 2 1 = xi x 1 1 2 := hxisym x 1 2 1
  have e3 : xi x 1 2 0 = 0 := by rw [hxisym]; exact k6
  have e4 : s x 0 1 0 1 = s x 0 1 1 0 := (hs x 0 1 0 1).2.1
  have e5 : s x 0 1 2 1 = s x 0 1 1 2 := (hs x 0 1 2 1).2.1
  have e6 : s x 0 1 2 0 = 0 := by rw [(hs x 0 1 2 0).2.1]; exact s4
  have e7 : s x 2 1 0 1 = s x 2 1 1 0 := (hs x 2 1 0 1).2.1
  have e8 : s x 2 1 2 1 = s x 2 1 1 2 := (hs x 2 1 2 1).2.1
  have e9 : s x 2 1 2 0 = 0 := by rw [(hs x 2 1 2 0).2.1]; exact s8
  have e10 : s x 2 1 1 0 = s x 0 1 1 2 := by
    rw [(hs x 2 1 1 0).2.2, (hs x 1 0 2 1).1, (hs x 0 1 2 1).2.1]
  have e11 : xi x 0 1 0 = 0 := by rw [hxisym]; exact k1
  have e12 : xi x 2 1 0 = 0 := by rw [hxisym]; exact k7
  have e13 : xi x 0 1 2 = 0 := by rw [hxisym]; exact k2
  have e14 : xi x 2 1 2 = 0 := by rw [hxisym]; exact k8
  have hh1 : h x t 0 1 = h x t 1 0 := hh x t 0 1
  have hh2 : h x t 2 1 = h x t 1 2 := hh x t 2 1
  rw [r1, r2, k3, k4, k5, k6, e1, e2, e3] at a
  rw [k1, k7, e1, s1, s2, s3, s4, e4, e5, e6, hh1] at b
  rw [k2, k8, e2, s5, s6, s7, s8, e7, e8, e9, e10, hh2] at c
  refine ⟨?_, ?_, ?_⟩
  all_goals
    unfold restr at a b c ⊢
    simp only [pdt, Arxiv1810_02867.cmp, ← hx] at a b c ⊢
    linarith
