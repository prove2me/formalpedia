-- Prove2me | Definitions.Def_APFPaper1_RegulationCounts
-- name    : APFPaper1_RegulationCounts
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:08:20.674447+00:00
-- url     : https://prove2.me/theorems/b633b5e8-3d3b-496f-8675-c24209aa0091
-- title:
--   List counts of individually and jointly holdable pairs
-- statement:
--   List counts of individually and jointly holdable pairs. Premises: Classical decisions of supplied existential predicates; repeated list elements count repeatedly. Scope: Counts exact occurrences in supplied list, not distinct disturbances or a probability distribution.
--
--   **Representation and scope.** Counts exact occurrences in supplied list, not distinct disturbances or a probability distribution.
--
--   **Supplied data or hypotheses.** Classical decisions of supplied existential predicates; repeated list elements count repeatedly.
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper1_RegulationCounts.lean; Sib v15, SHA-256 c2bbac95df1efdc3847f40ce2565a74d63b88ac66638e21c2830e633ecf5a375. ['27-33: eachCount and bothCount', 'Def_Regulation:13-14 binding exposure']

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper1_RegulationCounts
title: Counts of disturbances at which each mark, or both by one response, can be saved
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
statement: eachCount and bothCount count, over a finite list of disturbances, those at which each of two marks is holdable and those at which the pair is jointly holdable. Moved out of a theorem file on 2026-11-12.
-/
import Definitions.Def_APFPaper1_Regulation
import Mathlib.Data.NNReal.Basic

set_option autoImplicit false
namespace APFPaper1.Regulation

open APFPaper1.Continuation
open Classical

universe uC uF uX uR uM
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR} {M : Type uM}
  (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → WordFrom Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
  (reads : (h : Context) → Raw h → M → Bool)

/-- Number of listed disturbances against which each mark can be saved. -/
noncomputable def eachCount (g : Context) (xs : List (Raw g)) (m1 m2 : M) : Nat :=
  xs.countP (fun x => decide (Holdable step resource calibration C reads g x m1 ∧
    Holdable step resource calibration C reads g x m2))

/-- Number of listed disturbances against which one response saves both marks. -/
noncomputable def bothCount (g : Context) (xs : List (Raw g)) (m1 m2 : M) : Nat :=
  xs.countP (fun x => decide (JointlyHoldable step resource calibration C reads g x m1 m2))

end APFPaper1.Regulation


