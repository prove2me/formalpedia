-- Prove2me | solution 1 for APFPaper1.Continuation.not_cont_of_window
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:52:16.688209+00:00
-- url     : https://prove2.me/submissions/9d753667-e0fa-418f-9fcf-3464a3465b26

/-
APF Foundation Ledger — support corollary of T. DRAFT. Not gated, not released, not uploaded. Not proposed as a node:
both statements are the contrapositive of the bill bound and belong in its proof file if they are wanted at all.
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
consumes: no declared input.
statement:
  (1) A word whose calibrated whole resource exceeds the capacity of its starting context is not in Cont.
  (2) Window form. If a word f costs at least eps more than a word h, and the capacity is less than the bill of h
      plus eps, then f is not in Cont. Nothing is assumed about why f costs more; that is the hypothesis hgap.
-/
import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
namespace APFPaper1.Continuation

universe uC uF uX uR
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}

/-- (1) Over budget, not a continuation. Contrapositive of T. -/
theorem not_cont_of_capacity_lt_bill (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (g : Context) (x : Raw g) (w : WordFrom Frag g)
    (hover : C g < calibration g (resource g w)) :
    ¬ Cont step resource calibration C g x w :=
  fun hw => absurd hw.2 (not_le.mpr hover)

/-- (2) Window form: room for `h`, not for one `eps` more. -/
theorem not_cont_of_window (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (g : Context) (x : Raw g) (h f : WordFrom Frag g) (eps : NNReal)
    (hgap : calibration g (resource g h) + eps ≤ calibration g (resource g f))
    (hwin : C g < calibration g (resource g h) + eps) :
    ¬ Cont step resource calibration C g x f :=
  not_cont_of_capacity_lt_bill step resource calibration C g x f (lt_of_lt_of_le hwin hgap)

end APFPaper1.Continuation


universe uC uF uX uR
theorem solution :
∀ {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX} {R : Context → Type uR}
  (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → APFPaper1.Continuation.WordFrom.{uC, uF} Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal) (g : Context) (x : Raw g)
  (h f : APFPaper1.Continuation.WordFrom.{uC, uF} Frag g) (eps : NNReal),
  LE.le.{0} (HAdd.hAdd.{0, 0, 0} (calibration g (resource g h)) eps) (calibration g (resource g f)) →
    LT.lt.{0} (C g) (HAdd.hAdd.{0, 0, 0} (calibration g (resource g h)) eps) →
      ¬APFPaper1.Continuation.Cont.{uC, uF, uX, uR} step resource calibration C g x f := by
  exact @APFPaper1.Continuation.not_cont_of_window
