-- Prove2me | solution 1 for APFPaper1.Continuation.cont_concat_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:34:45.862936+00:00
-- url     : https://prove2.me/submissions/28ebdf85-5996-4ff7-8087-3023427cf70d

/-
APF Foundation Ledger — theorem node. DRAFT for author and cold review. Not gated, not released, not uploaded.
name: APFPaper1.Continuation.cont_concat
title: Concatenation of executing words is a continuation when the whole concatenation is inside the budget (C2)
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:1229 (C2), 1240 (reach remark: the combined load is the load of the concatenation), 3211, 3221-3226.
consumes: no declared input. Named hypothesis: the calibrated resource of the whole concatenation is at most the capacity of the starting context.
statement: If w executes from x to y and u executes from y to z, and the budget hypothesis holds, then w followed by u is in Cont g x.
label: theorem with one named hypothesis (hbudget). Author ruling 2026-11-12, item 2: the budget is that of the starting context.
-/
import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
namespace APFPaper1.Continuation

universe uC uF uX uR
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}

/-- C2. If `w` executes from `x` to `y`, `u` executes from `y` to `z`, and the calibrated resource of the
whole concatenation is at most the capacity of the starting context, then the concatenation belongs to
`Cont g x`. The budget hypothesis is on the concatenation, not on a sum of the two bills
(Supplement 1240). -/
theorem cont_concat (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    {g h k : Context} (w : Word Frag g h) (u : Word Frag h k) (x : Raw g) (y : Raw h) (z : Raw k)
    (hw : Executes step w x y) (hu : Executes step u y z)
    (hbudget : calibration g (resource g ⟨k, w.append u⟩) ≤ C g) :
    Cont step resource calibration C g x ⟨k, w.append u⟩ :=
  ⟨⟨z, (executes_append step w u x z).mpr ⟨y, hw, hu⟩⟩, hbudget⟩

/-- C2 in the Supplement's shape: `u` is a continuation available from the raw possibility `y` that `w`
reaches. Membership of `u` in `Cont h y` is used only for its execution; its own budget, which is tested
against the capacity of `h`, is not used. -/
theorem cont_concat_of_mem (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    {g h k : Context} (w : Word Frag g h) (u : Word Frag h k) (x : Raw g) (y : Raw h)
    (hw : Executes step w x y) (hu : Cont step resource calibration C h y ⟨k, u⟩)
    (hbudget : calibration g (resource g ⟨k, w.append u⟩) ≤ C g) :
    Cont step resource calibration C g x ⟨k, w.append u⟩ := by
  obtain ⟨z, hz⟩ := hu.1
  exact cont_concat step resource calibration C w u x y z hw hz hbudget

end APFPaper1.Continuation


universe uC uF uX uR
theorem solution :
∀ {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX} {R : Context → Type uR}
  (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → APFPaper1.Continuation.WordFrom.{uC, uF} Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal) {g h k : Context}
  (w : APFPaper1.Continuation.Word.{uC, uF} Frag g h) (u : APFPaper1.Continuation.Word.{uC, uF} Frag h k) (x : Raw g)
  (y : Raw h),
  APFPaper1.Continuation.Executes.{uC, uF, uX} step w x y →
    APFPaper1.Continuation.Cont.{uC, uF, uX, uR} step resource calibration C h y (Sigma.mk.{uC, max uC uF} k u) →
      LE.le.{0}
          (calibration g (resource g (Sigma.mk.{uC, max uC uF} k (APFPaper1.Continuation.Word.append.{uC, uF} w u))))
          (C g) →
        APFPaper1.Continuation.Cont.{uC, uF, uX, uR} step resource calibration C g x
          (Sigma.mk.{uC, max uC uF} k (APFPaper1.Continuation.Word.append.{uC, uF} w u)) := by
  exact @APFPaper1.Continuation.cont_concat_of_mem
