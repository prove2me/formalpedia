-- Prove2me | solution 2 for AhlforsComplexAnalysis.Polygon.polyInt_reverse
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T12:38:57.825253+00:00
-- url     : https://prove2.me/submissions/e77fca09-6344-4647-a132-6a31c54cd987

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Polygon

set_option autoImplicit false

open Set Complex Topology Filter

namespace AhlforsComplexAnalysis.Polygon

lemma pk_segInt_swap (g : ℂ → ℂ) (a b : ℂ) : segInt g b a = - segInt g a b := by
  unfold segInt
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
    (fun t : ℝ => g (a + (t : ℂ) * (b - a)) * (b - a)) 1
  simp only [sub_self, sub_zero] at h
  have e : ∀ t : ℝ, g (b + (t : ℂ) * (a - b)) * (a - b)
      = -(g (a + ((1 - t : ℝ) : ℂ) * (b - a)) * (b - a)) := by
    intro t
    have : a + ((1 - t : ℝ) : ℂ) * (b - a) = b + (t : ℂ) * (a - b) := by
      push_cast; ring
    rw [this]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_neg, h]

lemma pk_polyInt_append_aux (g : ℂ → ℂ) (x : ℂ) (l : List ℂ) (a : ℂ) (m : List ℂ)
    (h : (x :: l).getLast? = some a) :
    polyInt g ((x :: l) ++ m) = polyInt g (x :: l) + polyInt g (a :: m) := by
  induction l generalizing x with
  | nil =>
    have hx : x = a := by simpa using h
    subst hx
    simp
  | cons y l ih =>
    have h' : (y :: l).getLast? = some a := by
      simpa [List.getLast?_cons_cons] using h
    have e1 : (x :: y :: l) ++ m = x :: y :: (l ++ m) := rfl
    have e2 : (y :: l) ++ m = y :: (l ++ m) := rfl
    have := ih y h'
    rw [e2] at this
    rw [e1, polyInt_cons_cons, polyInt_cons_cons g x y l, this]
    ring

lemma pk_polyInt_append' (g : ℂ → ℂ) {l : List ℂ} {a : ℂ} (m : List ℂ)
    (h : l.getLast? = some a) :
    polyInt g (l ++ m) = polyInt g l + polyInt g (a :: m) := by
  cases l with
  | nil => simp at h
  | cons x l => exact pk_polyInt_append_aux g x l a m h

end AhlforsComplexAnalysis.Polygon

open AhlforsComplexAnalysis.Polygon

theorem solution (g : ℂ → ℂ) (l : List ℂ) : polyInt g l.reverse = - polyInt g l := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b rest =>
      have hlast : (b :: rest).reverse.getLast? = some b := by simp
      rw [List.reverse_cons, pk_polyInt_append' g [a] hlast, ih, polyInt_cons_cons g b a [],
        polyInt_cons_cons g a b rest, pk_segInt_swap g a b]
      simp

#print axioms solution
