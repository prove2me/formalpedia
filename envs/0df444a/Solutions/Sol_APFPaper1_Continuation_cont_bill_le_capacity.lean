-- Prove2me | solution 1 for APFPaper1.Continuation.cont_bill_le_capacity
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:30:44.419018+00:00
-- url     : https://prove2.me/submissions/c8bec9b5-d682-4de0-a398-f14c166fd710

/-
APF Foundation Ledger — theorem node. DRAFT for author and cold review. Not gated, not released, not uploaded.
name: APFPaper1.Continuation.cont_bill_le_capacity
title: A continuation in the whole-word class has calibrated whole resource at most the capacity (T)
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:1224-1235, 1860-1869. Author direction 4c of 2026-10-04; author ruling of 2026-11-12.
consumes: no declared input.
statement: If w is in Cont g x then the calibrated resource of w is at most C g; and w executes from x to some raw possibility.
label: BY DEFINITION OF Cont. Both statements are conjuncts of the definition. Not a derived physical result.
-/
import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
namespace APFPaper1.Continuation

universe uC uF uX uR
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}

/-- T. A word in `Cont g x` has calibrated whole resource at most the capacity of `g`.
This is the second conjunct of the definition of `Cont`; it is not a derived physical result. -/
theorem cont_bill_le_capacity (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (g : Context) (x : Raw g) (w : WordFrom Frag g)
    (hw : Cont step resource calibration C g x w) : calibration g (resource g w) ≤ C g :=
  hw.2

/-- A word in `Cont g x` executes from `x` to some raw possibility of its end context.
The first conjunct of the definition of `Cont`. -/
theorem cont_executes (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (g : Context) (x : Raw g) (w : WordFrom Frag g)
    (hw : Cont step resource calibration C g x w) : ∃ y : Raw w.1, Executes step w.2 x y :=
  hw.1

end APFPaper1.Continuation


universe uC uF uX uR
theorem solution :
∀ {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX} {R : Context → Type uR}
  (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → APFPaper1.Continuation.WordFrom.{uC, uF} Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal) (g : Context) (x : Raw g)
  (w : APFPaper1.Continuation.WordFrom.{uC, uF} Frag g),
  APFPaper1.Continuation.Cont.{uC, uF, uX, uR} step resource calibration C g x w →
    LE.le.{0} (calibration g (resource g w)) (C g) := by
  exact @APFPaper1.Continuation.cont_bill_le_capacity
