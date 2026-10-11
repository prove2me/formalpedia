-- Prove2me | solution 1 for Algo2Lean.Fibonacci.Decrease.amortized
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:52:35.933655+00:00
-- url     : https://prove2.me/submissions/60b960c6-11c7-419c-9b95-3bcc5a81df5b

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


























































/-- Every additional cascading cut pays for itself by clearing its mark. -/
theorem Cascade.amortized {before after : Counts} {cuts : Nat}
    (cascade : Cascade before after cuts) : cuts + potential after ≤ potential before + 2 := by
  induction cascade with
  | root => simp [potential]
  | mark => simp [potential]; omega
  | cut cascade ih => simp only [potential] at *; omega



theorem Decrease.amortized {before after : Counts} {cuts : Nat}
    (decrease : Decrease before after cuts) : cuts + potential after ≤ potential before + 4 := by
  cases decrease with
  | unchanged => simp [potential]
  | unmarked cascade => have bound := cascade.amortized; simp only [potential] at *; omega
  | marked cascade => have bound := cascade.amortized; simp only [potential] at *; omega

































end Algo2Lean.Fibonacci

end

set_option autoImplicit false
theorem solution :
    ∀ {before after : Algo2Lean.Fibonacci.Counts} {cuts : Nat},
      Algo2Lean.Fibonacci.Decrease before after cuts →
        LE.le.{0} (HAdd.hAdd.{0, 0, 0} cuts (Algo2Lean.Fibonacci.potential after))
          (HAdd.hAdd.{0, 0, 0} (Algo2Lean.Fibonacci.potential before) (4 : Nat)) :=
  Algo2Lean.Fibonacci.Decrease.amortized
