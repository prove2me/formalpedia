-- Prove2me | solution 1 for Algo2Lean.Fibonacci.degree_logarithmic
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:52:44.543648+00:00
-- url     : https://prove2.me/submissions/8db3dcb3-e1b3-416e-a166-d1cd1b178702

import Definitions.Def_Algo2LeanLib_Fibonacci


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Mathematical building blocks for Fibonacci heaps.

The tree lemmas use children in reverse link order (newest first). The rank
invariant records the consequence of equal-degree links and cutting a nonroot
when it loses its second child. The accounting relations describe actual
root/mark changes; they do not assume their amortized bounds.

This module is independent of any generated program. A compiled implementation
must separately establish the rank invariant and realize the accounting steps.
References: Fredman and Tarjan, JACM 34(3), 1987; David Karger's MIT 6.854 notes,
https://courses.csail.mit.edu/6.854/21/Notes/n01-fibonacci.html.
-/

namespace Algo2Lean.Fibonacci






theorem minimumNodes_step (degree : Nat) :
    minimumNodes (degree + 1) = minimumNodes degree + minimumNodes (degree - 1) := by
  cases degree with
  | zero => rfl
  | succ degree => simp only [Nat.add_sub_cancel, minimumNodes]

theorem minimumNodes_mono_step (degree : Nat) : minimumNodes degree ≤ minimumNodes (degree + 1) := by
  rw [minimumNodes_step]
  omega



/-- Two rank increases at least double the minimum subtree size. -/
theorem minimumNodes_exponential (degree : Nat) : 2 ^ (degree / 2) ≤ minimumNodes degree := by
  induction degree using Nat.strongRecOn with
  | ind degree ih =>
    cases degree with
    | zero => decide
    | succ degree =>
      cases degree with
      | zero => decide
      | succ degree =>
        have smaller := ih degree (by omega)
        have monotone := minimumNodes_mono_step degree
        have half : (degree + 1 + 1) / 2 = degree / 2 + 1 := by omega
        simp only [half, Nat.pow_succ, minimumNodes]
        omega

/-- An exponential subtree bound gives a binary-logarithmic degree bound,
    avoiding real numbers or an approximation to the golden ratio. -/
theorem degree_logarithmic {degree nodes : Nat} (subtreeBound : minimumNodes degree ≤ nodes) :
    degree ≤ 2 * nodes.log2 + 1 := by
  have exponential := Nat.le_trans (minimumNodes_exponential degree) subtreeBound
  have positive : nodes ≠ 0 := by
    have powerPositive : 0 < (2 : Nat) ^ (degree / 2) := Nat.pow_pos (by decide)
    omega
  have half := (Nat.le_log2 positive).mpr exponential
  omega

















































































end Algo2Lean.Fibonacci

end

set_option autoImplicit false
theorem solution :
    ∀ {degree nodes : Nat},
      LE.le.{0} (Algo2Lean.Fibonacci.minimumNodes degree) nodes →
        LE.le.{0} degree (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) nodes.log2) (1 : Nat)) :=
  Algo2Lean.Fibonacci.degree_logarithmic
