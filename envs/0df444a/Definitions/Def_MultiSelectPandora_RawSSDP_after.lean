-- Prove2me | Definitions.Def_MultiSelectPandora_RawSSDP_after
-- name    : MultiSelectPandora_RawSSDP_after
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:10:32.505195+00:00
-- url     : https://prove2.me/theorems/d30fa277-d375-4664-bee2-885985ee1a43
-- title:
--   The removed groups after an action
-- statement:
--   Taking an action of group $g$ adds $g$ to the removed groups, which implements "taking either removes the other from the set of available actions". An action without a group changes nothing.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §3.1, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawSSDP

namespace MultiSelectPandora

/-- **The removed groups after taking action `a`.** Beyhaghi–Han–Luqman manuscript, §3.1, p.7 (PDF p.8): "taking either removes the
other from the set of available actions". -/
def RawSSDP.after (S : RawSSDP) (R : Finset ℕ) (a : ℕ) : Finset ℕ :=
  match (S.actions.getD a (none, [])).1 with
  | none => R
  | some g => insert g R

end MultiSelectPandora


