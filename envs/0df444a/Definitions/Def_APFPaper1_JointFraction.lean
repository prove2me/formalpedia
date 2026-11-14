-- Prove2me | Definitions.Def_APFPaper1_JointFraction
-- name    : APFPaper1_JointFraction
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:09:26.623677+00:00
-- url     : https://prove2.me/theorems/990cd39a-e15a-4af7-8779-d5ab012a53c9
-- title:
--   List-relative count ratio for co-holdability
-- statement:
--   List-relative count ratio for co-holdability; denominator zero gives zero. Premises: Supplied list, raw reads and word data; no probability measure or pair-number identification. Scope: Definition matches its arithmetic description. Candidate-turn-number wording at10-12 is superseded by later author ruling; ratio remains co-holdability measure.
--
--   **Representation and scope.** Definition matches its arithmetic description. Candidate-turn-number wording at10-12 is superseded by later author ruling; ratio remains co-holdability measure.
--
--   **Supplied data or hypotheses.** Supplied list, raw reads and word data; no probability measure or pair-number identification.
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper1_JointFraction.lean; Sib v15, SHA-256 497e47e281a8e0cd7e9cd96d7e665c484ef9c287c3deefe72d07b3d7688b1a4e. ['34-36: ratio', '10-13: stale candidate text', 'RULING_cross_term_and_preservation item1']

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper1_JointFraction
title: The joint fraction of two marks: of the listed disturbances against which each can be saved, the share against which one response saves both
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Def_APFPaper1_Regulation and Def_APFPaper1_RegulationCounts (Ashby's regulation setting on ledger
 words). Author's remarks of 2026-11-12: "Numbers are a count of distinctions"; "The true void that separates
 them is where the perturbations are".
standing: a DEFINITION, and a CANDIDATE for the number between two marks off the record-book side. The list of
 disturbances is supplied. That this fraction is the pair number of an algebra of marks has not been shown,
 and the author has not ruled on it. If no listed disturbance lets each mark be saved, the fraction is 0 by
 the convention for division by zero.
statement: jointFraction is bothCount divided by eachCount, as real numbers.
-/
import Definitions.Def_APFPaper1_RegulationCounts
import Mathlib.Data.Real.Basic

set_option autoImplicit false
namespace APFPaper1.Regulation

open APFPaper1.Continuation

universe uC uF uX uR uM
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR} {M : Type uM}
  (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → WordFrom Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
  (reads : (h : Context) → Raw h → M → Bool)

/-- The share of listed disturbances, among those against which each mark can be saved, against which one
response saves both. -/
noncomputable def jointFraction (g : Context) (xs : List (Raw g)) (m1 m2 : M) : ℝ :=
  (bothCount step resource calibration C reads g xs m1 m2 : ℝ) /
    (eachCount step resource calibration C reads g xs m1 m2 : ℝ)

end APFPaper1.Regulation


