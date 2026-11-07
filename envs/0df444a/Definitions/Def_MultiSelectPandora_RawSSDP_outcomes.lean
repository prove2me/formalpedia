-- Prove2me | Definitions.Def_MultiSelectPandora_RawSSDP_outcomes
-- name    : MultiSelectPandora_RawSSDP_outcomes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:09:58.992029+00:00
-- url     : https://prove2.me/theorems/d8d76e36-e4e4-4ca9-b94c-824c2b90daac
-- title:
--   Outcomes of an action at a state
-- statement:
--   The list of outcomes (probability, reward, next state) of a given action at a given state, empty if out of range.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §3.1, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawSSDP

namespace MultiSelectPandora

/-- **The outcomes (probability, reward, next state) of action `a` at state `st`.** Auxiliary to §3.1, p.7 (PDF p.8) of the
Beyhaghi–Han–Luqman manuscript. Out of range, the list is empty. -/
def RawSSDP.outcomes (S : RawSSDP) (a st : ℕ) : List (ℚ × ℚ × ℕ) := ((S.actions.getD a (none, [])).2).getD st []

end MultiSelectPandora


