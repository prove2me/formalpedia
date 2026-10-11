-- Prove2me | solution 1 for Algo2Lean.Fibonacci.Run.amortized
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:53:35.624548+00:00
-- url     : https://prove2.me/submissions/05658fae-d916-4118-a3f3-636564f96cdf

import Definitions.Def_Algo2LeanLib_Fibonacci
import Theorems.Thm_Algo2Lean_Fibonacci_Decrease_amortized


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
































































/-- Four units per cut allow comparisons and pointer-work event counters to
    share one potential. The resulting decrease-key charge is constant. -/
theorem Decrease.work_bound {before after : Counts} {cuts work : Nat}
    (decrease : Decrease before after cuts) (events : work ≤ 4 * cuts + 4) :
    work + scaledPotential after ≤ scaledPotential before + 20 := by
  have accounting := decrease.amortized
  simp only [scaledPotential]
  omega

/-- Inserting an unmarked singleton costs at most two events and deposits
    enough root credit to pay for its eventual consolidation. -/
theorem insertion_work_bound (roots marks work : Nat) (events : work ≤ 2) :
    work + scaledPotential ⟨roots + 1, marks⟩ ≤ scaledPotential ⟨roots, marks⟩ + 6 := by
  simp only [scaledPotential, potential]
  omega



theorem Consolidation.roots_accounted {before after : Counts} {links : Nat}
    (consolidation : Consolidation before after links) : links + after.roots = before.roots := by
  induction consolidation with
  | done => simp
  | link positive rest ih => simp only at *; omega

theorem Consolidation.marks_unchanged {before after : Counts} {links : Nat}
    (consolidation : Consolidation before after links) : after.marks = before.marks := by
  induction consolidation with
  | done => rfl
  | link positive rest ih => exact ih





/-- Consolidation pays for its links using old root credit. Only logarithmically
    many promoted children and surviving degree buckets remain to be charged. -/
theorem extraction_work_bound (before promoted after : Counts) (degree maximumDegree : Nat)
    (events : ExtractEvents)
    (promotedRoots : promoted.roots + 1 = before.roots + degree)
    (clearedMarks : promoted.marks ≤ before.marks)
    (consolidation : Consolidation promoted after events.links)
    (degreeBound : degree ≤ maximumDegree) (finalRoots : after.roots ≤ maximumDegree + 1)
    (scanBound : events.rootScans ≤ promoted.roots)
    (promotionCount : events.promotions = degree)
    (tableBound : events.degreeScans ≤ maximumDegree + 1)
    (comparisonBound : events.comparisons ≤ degree + events.links + after.roots) :
    events.work + scaledPotential after ≤ scaledPotential before + 12 * (maximumDegree + 1) := by
  have roots := consolidation.roots_accounted
  have marks := consolidation.marks_unchanged
  simp only [ExtractEvents.work, scaledPotential, potential]
  omega







theorem Operation.amortized {maximumDegree work updates extractions : Nat} {before after : Counts}
    (operation : Operation maximumDegree before after work updates extractions) :
    work + scaledPotential after ≤
      scaledPotential before + 20 * updates + 12 * (maximumDegree + 1) * extractions := by
  cases operation with
  | insert roots marks work events =>
    have bound := insertion_work_bound roots marks work events
    simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero]
    omega
  | decrease cascade events => simpa using cascade.work_bound events
  | extract before promoted after degree events roots marks consolidation degreeBound finalRoots
      scans promotions table comparisons =>
    simpa using extraction_work_bound before promoted after degree maximumDegree events
      roots marks consolidation degreeBound finalRoots scans promotions table comparisons



/-- Potential telescopes across an arbitrary mix of operations. No worst-case
    bound on an individual cascade or a single root scan is assumed. -/
theorem Run.amortized {maximumDegree work updates extractions : Nat} {before after : Counts}
    (run : Run maximumDegree before after work updates extractions) :
    work + scaledPotential after ≤
      scaledPotential before + 20 * updates + 12 * (maximumDegree + 1) * extractions := by
  induction run with
  | empty => simp
  | @step before middle after work updates extractions tailWork tailUpdates tailExtractions operation rest ih =>
    have localBound := operation.amortized
    simp only [Nat.mul_add] at *
    omega





end Algo2Lean.Fibonacci

end

set_option autoImplicit false
theorem solution :
    ∀ {maximumDegree work updates extractions : Nat} {before after : Algo2Lean.Fibonacci.Counts},
      Algo2Lean.Fibonacci.Run maximumDegree before after work updates extractions →
        LE.le.{0} (HAdd.hAdd.{0, 0, 0} work (Algo2Lean.Fibonacci.scaledPotential after))
          (HAdd.hAdd.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0} (Algo2Lean.Fibonacci.scaledPotential before)
              (HMul.hMul.{0, 0, 0} (20 : Nat) updates))
            (HMul.hMul.{0, 0, 0}
              (HMul.hMul.{0, 0, 0} (12 : Nat) (HAdd.hAdd.{0, 0, 0} maximumDegree (1 : Nat)))
              extractions)) :=
  Algo2Lean.Fibonacci.Run.amortized
