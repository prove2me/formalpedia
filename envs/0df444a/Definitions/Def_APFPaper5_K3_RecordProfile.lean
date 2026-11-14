-- Prove2me | Definitions.Def_APFPaper5_K3_RecordProfile
-- name    : APFPaper5_K3_RecordProfile
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:12:26.157428+00:00
-- url     : https://prove2.me/theorems/58c64fbe-f9b4-4581-864a-a3efb7404b21
-- title:
--   Four-record profile of the supplied two-component model
-- statement:
--   Defines recordProfile as the graph of the tuple recA, recB, recSum, recQuarter.
--
--   **Representation and scope.** Faithful to its exact supplied mathematical definitions under the stated exposure; original physical-object correspondence is not established.
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper5_K3_RecordProfile.lean; Sib v15, SHA-256 c8cb340e82a3ab2a89d62884c110168aa5bfaba3c96027305bbf3250bfbb45ee. P5:1809-1832;P1:1054-1066

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_RecordProfile
title: The record profile of two held components: the four records taken together
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K3_TwoComponents; FOUNDATION_INPUTS B01 (a physical object is its admissible
 continuation profile).
standing: part of the supplied MODEL. It takes the continuation profile of a state to be its four records.
 That the records exhaust the profile is the model's choice, not a ledger fact.
statement: recordProfile h t says that t is the tuple (recA h, recB h, recSum h, recQuarter h).
-/
import Definitions.Def_APFPaper5_K3_TwoComponents

set_option autoImplicit false
namespace APFPaper5.K3

/-- The four records of a state, as a profile. -/
def recordProfile (h : Held2) (t : ℝ × ℝ × ℝ × ℝ) : Prop :=
  t = (recA h, recB h, recSum h, recQuarter h)

end APFPaper5.K3


