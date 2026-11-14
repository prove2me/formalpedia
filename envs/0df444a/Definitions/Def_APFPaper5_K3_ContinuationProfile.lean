-- Prove2me | Definitions.Def_APFPaper5_K3_ContinuationProfile
-- name    : APFPaper5_K3_ContinuationProfile
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:12:13.711078+00:00
-- url     : https://prove2.me/theorems/98e85250-9476-41cf-bd71-36a406eb7aae
-- title:
--   Model continuation profile from plain records after unit-pair relative turns
-- statement:
--   Defines plainAfterTurn as the indexed graph of three chosen records after every unit-pair turn of component B.
--
--   **Representation and scope.** Faithful to its exact supplied mathematical definitions under the stated exposure; original physical-object correspondence is not established.
--
--   **Claim boundaries.** K3-03
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper5_K3_ContinuationProfile.lean; Sib v15, SHA-256 1cf4b72a72144274f835143aca0122e152de798670c8f4821fd7cf4e1dad7845. P5:1809-1832;3049-3056

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_ContinuationProfile
title: The continuation profile of two held components: the plain records read after any turn of one component
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: FOUNDATION_INPUTS B01 (a physical object is its admissible continuation profile). The adopted continuity
 hypothesis (a turn that changes the number in a relation is admissible). Paper 5 Supplement v7.33:1824-1832
 ("relative orientation remains represented whenever it changes a later recombination record").
standing: part of the supplied MODEL. It takes as continuations the turns of one component by a unit pair, and
 as records the two component costs and the plain recombination. The quarter-turned recombination is NOT put
 in as a record.
statement: plainAfterTurn h (c, s, t) says that (c, s) is a unit pair and t is the triple of plain records of
 h after component B is turned by (c, s).
-/
import Definitions.Def_APFPaper5_K3_TwoComponents

set_option autoImplicit false
namespace APFPaper5.K3

/-- The plain records read after a turn of component B by a unit pair. -/
def plainAfterTurn (h : Held2) (x : ℝ × ℝ × (ℝ × ℝ × ℝ)) : Prop :=
  x.1 * x.1 + x.2.1 * x.2.1 = 1 ∧
    x.2.2 = (recA (relativeTurn x.1 x.2.1 h), recB (relativeTurn x.1 x.2.1 h),
      recSum (relativeTurn x.1 x.2.1 h))

end APFPaper5.K3


