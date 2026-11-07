-- Prove2me | Definitions.Def_MultiSelectPandora_RawSSDP_C2
-- name    : MultiSelectPandora_RawSSDP_C2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:13:45.442561+00:00
-- url     : https://prove2.me/theorems/ab7ba9fa-2ad2-4ad9-b74f-7f0885886fe7
-- title:
--   Condition (C2)
-- statement:
--   Condition (C2): the transition is state-monotone, $f(I_t,a_t)\ge I_t$ almost surely. Every outcome of positive probability leads to a state at least the current one, in the order of the integers.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Definition 3.2, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawSSDP
import Definitions.Def_MultiSelectPandora_RawSSDP_outcomes

namespace MultiSelectPandora

/-- **Condition (C2): the transition is state-monotone**, `f(I_t, a_t) ≥ I_t` almost surely. Beyhaghi–Han–Luqman manuscript, Definition 3.2,
p.8 (PDF p.9). -/
def RawSSDP.C2 (S : RawSSDP) : Prop :=
  ∀ a < S.actions.length, ∀ st < S.L, ∀ o ∈ S.outcomes a st, 0 < o.1 → st ≤ o.2.2

end MultiSelectPandora


