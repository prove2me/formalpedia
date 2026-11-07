-- Prove2me | solution 1 for AaronsonAmbainis.Row.neg_derivative_eval_zero_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:42:14.363196+00:00
-- url     : https://prove2.me/submissions/75f769c3-a4a3-49dd-b8c0-2d748cf8f467

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Row_Markov

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Polynomial
namespace AaronsonAmbainis.Row
theorem _root_.solution (D : ℕ) (p : ℝ[X]) (hdeg : p.natDegree ≤ D)
    (hbnd : ∀ s : ℝ, 0 ≤ s → s ≤ 2 → |p.eval s| ≤ 1) :
    -(p.derivative.eval 0) ≤ (D : ℝ) ^ 2 := by
  have h1X : (1 - X : ℝ[X]).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (by simp)
  have hnat : (p.comp (1 - X)).natDegree ≤ D :=
    calc (p.comp (1 - X)).natDegree ≤ p.natDegree * (1 - X : ℝ[X]).natDegree := natDegree_comp_le
      _ ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ h1X
      _ ≤ D := by simpa using hdeg
  have hP : (p.comp (1 - X)).degree ≤ (D : WithBot ℕ) := degree_le_of_natDegree_le hnat
  have hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |(p.comp (1 - X)).eval x| ≤ 1 := by
    intro x hx
    rw [eval_comp]
    simp only [eval_sub, eval_one, eval_X]
    exact hbnd (1 - x) (by linarith [hx.2]) (by linarith [hx.1])
  have h := Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one (k := 1) (x := 1)
    le_rfl hP hb
  simp only [Function.iterate_one] at h
  rw [derivative_comp_one_sub_X, Chebyshev.derivative_T_eval_one] at h
  simpa using h
end AaronsonAmbainis.Row
