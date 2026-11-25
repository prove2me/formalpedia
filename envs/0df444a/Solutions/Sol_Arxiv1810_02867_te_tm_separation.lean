-- Prove2me | solution 1 for Arxiv1810_02867.te_tm_separation
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T21:51:18.228877+00:00
-- url     : https://prove2.me/submissions/f9e33d10-898e-4135-9246-ce03c8524c11

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

open Arxiv1810_02867 S71R in
theorem solution (eO xi mu : Space → Fin 3 → Fin 3 → ℝ)
    (E H Je Jm : Space → ℝ → Fin 3 → ℝ)
    (hiE : IndepX2 E) (hiH : IndepX2 H) (hiJe : IndepX2 Je) (hiJm : IndepX2 Jm)
    (hieO : IndepX2 eO) (hixi : IndepX2 xi) (himu : IndepX2 mu)
    (heOsym : ∀ x i l, eO x i l = eO x l i) (hmusym : ∀ x j k, mu x j k = mu x k j)
    (heO0 : ∀ x, eO x 1 0 = 0 ∧ eO x 1 2 = 0) (hmu0 : ∀ x, mu x 1 0 = 0 ∧ mu x 1 2 = 0)
    (hxi0 : ∀ x, xi x 0 0 = 0 ∧ xi x 1 1 = 0 ∧ xi x 2 2 = 0 ∧ xi x 0 2 = 0 ∧ xi x 2 0 = 0)
    (hM : MaxwellEO eO xi mu E H Je Jm) :
    TESystem (restr eO) (restr xi) (restr mu) (restr E) (restr H) (restr Je) (restr Jm) ∧
    TMSystem (restr eO) (restr xi) (restr mu) (restr E) (restr H) (restr Je) (restr Jm) := by
  have key : ∀ y t, _ := fun y t => hM (emb y) t
  constructor
  · intro y t
    obtain ⟨h1, h2⟩ := key y t
    have a := h1 1
    have b := h2 0
    have c := h2 2
    simp only [Fin.sum_univ_three, levi] at a b c
    simp (config := { decide := true }) only [if_true, if_false, true_and, and_true, false_and,
      and_false, or_false, false_or, true_or, or_true, one_mul, neg_mul, zero_mul, add_zero,
      zero_add, sub_eq_add_neg] at a b c
    simp only [zF hiE, zF hiH, aF, bF] at a b c
    obtain ⟨x1, x2⟩ := heO0 (emb y)
    obtain ⟨m1, m2⟩ := hmu0 (emb y)
    obtain ⟨k1, k2, k3, k4, k5⟩ := hxi0 (emb y)
    rw [hmusym (emb y) 0 1, m1, hmusym (emb y) 0 2] at b
    rw [hmusym (emb y) 2 1, m2] at c
    simp only [x1, x2, m1, m2, k1, k2, k3, k4, k5, zero_mul, add_zero, zero_add] at a b c
    refine ⟨?_, ?_, ?_⟩
    all_goals
      simp only [restr, pdt, Arxiv1810_02867.cmp] at a b c ⊢
      linarith
  · intro y t
    obtain ⟨h1, h2⟩ := key y t
    have a := h2 1
    have b := h1 0
    have c := h1 2
    simp only [Fin.sum_univ_three, levi] at a b c
    simp (config := { decide := true }) only [if_true, if_false, true_and, and_true, false_and,
      and_false, or_false, false_or, true_or, or_true, one_mul, neg_mul, zero_mul, add_zero,
      zero_add, sub_eq_add_neg] at a b c
    simp only [zF hiE, zF hiH, aF, bF] at a b c
    obtain ⟨x1, x2⟩ := heO0 (emb y)
    obtain ⟨m1, m2⟩ := hmu0 (emb y)
    obtain ⟨k1, k2, k3, k4, k5⟩ := hxi0 (emb y)
    rw [heOsym (emb y) 0 1, x1, heOsym (emb y) 0 2] at b
    rw [heOsym (emb y) 2 1, x2] at c
    simp only [x1, x2, m1, m2, k1, k2, k3, k4, k5, zero_mul, add_zero, zero_add] at a b c
    refine ⟨?_, ?_, ?_⟩
    all_goals
      simp only [restr, pdt, Arxiv1810_02867.cmp] at a b c ⊢
      linarith
