-- Prove2me | Definitions.Def_MultiSelectPandora_RawSSDP_avail
-- name    : MultiSelectPandora_RawSSDP_avail
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:10:15.068639+00:00
-- url     : https://prove2.me/theorems/55aaa9b0-ffdc-4f11-9c79-3b132f7a0e40
-- title:
--   Availability of an action
-- statement:
--   An action is available when it exists and its group has not been removed: the set $A_t\subseteq A$ of actions still available, in terms of the set $R$ of removed groups.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §3.1, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawSSDP

namespace MultiSelectPandora

/-- **Whether action `a` is still available**, given the set `R` of removed groups. Beyhaghi–Han–Luqman manuscript, §3.1, p.7 (PDF
p.8): "the set `A_t ⊆ A` of actions still available". -/
def RawSSDP.avail (S : RawSSDP) (R : Finset ℕ) (a : ℕ) : Bool :=
  decide (a < S.actions.length) &&
    match (S.actions.getD a (none, [])).1 with
    | none => true
    | some g => decide (g ∉ R)

end MultiSelectPandora


