-- Prove2me | solution 1 for AhlforsComplexAnalysis.Polygon.polyInt_append
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T12:35:24.31398+00:00
-- url     : https://prove2.me/submissions/84465dc4-cfea-424f-bcc2-23bf2277e122

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Polygon

set_option autoImplicit false

open Set Complex Topology Filter

namespace AhlforsComplexAnalysis.Polygon

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

theorem solution (g : ℂ → ℂ) {l m : List ℂ} (hl : l ≠ []) (hm : m ≠ [])
    (h : l.getLast? = m.head?) : polyInt g (l ++ m.tail) = polyInt g l + polyInt g m := by
  cases m with
  | nil => exact absurd rfl hm
  | cons a m' =>
    simp only [List.head?_cons] at h
    simpa using pk_polyInt_append' g m' h

#print axioms solution
