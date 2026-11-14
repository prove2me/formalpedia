-- Prove2me | Definitions.Def_APFPaper1_Regulation
-- name    : APFPaper1_Regulation
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:07:29.165508+00:00
-- url     : https://prove2.me/theorems/bf4835b2-0dea-4ce0-a7af-95aceb9bcdab
-- title:
--   Existential saving/co-saving responses in a budgeted word model
-- statement:
--   Existential saving/co-saving responses in a budgeted word model; individual holdability with failure of joint holdability. Premises: Supplied reads on Raw, not B01 quotient-valued distinctions. Scope: Correct existential reach semantics; one successful run is enough. IrreduciblyJointAt names a regulation obstruction, not the actual-held novel relation in B06.
--
--   **Representation and scope.** Correct existential reach semantics; one successful run is enough. IrreduciblyJointAt names a regulation obstruction, not the actual-held novel relation in B06.
--
--   **Supplied data or hypotheses.** Supplied reads on Raw, not B01 quotient-valued distinctions.
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper1_Regulation.lean; Sib v15, SHA-256 68f4dff53f44e858e1d865c50e89237e42f61da0255ceb61bc853090b985a853. ['33-74: five definitions', '13-14: owed B01 reads binding', 'RULING_eight_decisions items1-2']

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper1_Regulation
title: Regulation on the word vocabulary: disturbances, budgeted responses, held marks
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Author direction 2026-11-12 (substitute Ashby's setting for the perturbation data). W. R. Ashby, An
 Introduction to Cybernetics, regulation table (disturbance, response, outcome, acceptable set), as read in
 the archive modules AshbyCybernetics_Regulation and APFReachKernel_Ashby. Paper 1 Supplement v9.28:1224-1235
 (Cont), as corrected in Def_APFPaper1_ContinuationWords.
replaces: Def_APFPaper1_Perturbation (same session). The relations `breaks`, `breaksPair` and the function
 `strength` supplied there are not used here.
supplied_data: `reads`, the Boolean reading of a mark at a reached raw state. On the ledger a distinction is a
 Boolean function on the B01 quotient; re-pointing `reads` to that quotient is owed (check 13).
statement: The disturbance is the raw input x. The response is a word w from x's context. Saves says w is
 inside the context budget and some run of w from x ends where the mark reads true. SavesBoth asks one run
 to end where both marks read true. Holdable and JointlyHoldable say some response does so. IrreduciblyJointAt
 says each mark is holdable against x and the pair is not.
-/
import Definitions.Def_APFPaper1_ContinuationWords
import Mathlib.Data.NNReal.Basic

set_option autoImplicit false
namespace APFPaper1.Regulation

open APFPaper1.Continuation

universe uC uF uX uR uM
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR} {M : Type uM}

/-- Response `w`, inside the budget, has a run from disturbance `x` ending where `m` reads true. -/
def Saves (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (reads : (h : Context) → Raw h → M → Bool)
    (g : Context) (x : Raw g) (w : WordFrom Frag g) (m : M) : Prop :=
  calibration g (resource g w) ≤ C g ∧
    ∃ y : Raw w.1, Executes step w.2 x y ∧ reads w.1 y m = true

/-- One run of the response ends where both marks read true. -/
def SavesBoth (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (reads : (h : Context) → Raw h → M → Bool)
    (g : Context) (x : Raw g) (w : WordFrom Frag g) (m1 m2 : M) : Prop :=
  calibration g (resource g w) ≤ C g ∧
    ∃ y : Raw w.1, Executes step w.2 x y ∧ reads w.1 y m1 = true ∧ reads w.1 y m2 = true

/-- Some budgeted response saves the mark against `x`. -/
def Holdable (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (reads : (h : Context) → Raw h → M → Bool)
    (g : Context) (x : Raw g) (m : M) : Prop :=
  ∃ w : WordFrom Frag g, Saves step resource calibration C reads g x w m

/-- Some single budgeted response saves both marks against `x`. -/
def JointlyHoldable (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (reads : (h : Context) → Raw h → M → Bool)
    (g : Context) (x : Raw g) (m1 m2 : M) : Prop :=
  ∃ w : WordFrom Frag g, SavesBoth step resource calibration C reads g x w m1 m2

/-- Each mark can be saved against `x`, but no single budgeted response saves both. -/
def IrreduciblyJointAt (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (reads : (h : Context) → Raw h → M → Bool)
    (g : Context) (x : Raw g) (m1 m2 : M) : Prop :=
  Holdable step resource calibration C reads g x m1 ∧
    Holdable step resource calibration C reads g x m2 ∧
    ¬ JointlyHoldable step resource calibration C reads g x m1 m2

end APFPaper1.Regulation


