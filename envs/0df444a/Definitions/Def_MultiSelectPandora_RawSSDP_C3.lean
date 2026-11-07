-- Prove2me | Definitions.Def_MultiSelectPandora_RawSSDP_C3
-- name    : MultiSelectPandora_RawSSDP_C3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:22:46.489611+00:00
-- url     : https://prove2.me/theorems/30c6c329-b788-4c77-b93e-c6a43b287e5c
-- title:
--   Condition (C3)
-- statement:
--   Condition (C3): the terminal reward is nonnegative, and there is an optimal policy along whose trajectory every action has nonnegative expected marginal reward, $E[g(I_t,a_t)]\ge0$.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Definition 3.2, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawSSDP
import Definitions.Def_MultiSelectPandora_RawSSDP_outcomes
import Definitions.Def_MultiSelectPandora_RawSSDP_terminal
import Definitions.Def_MultiSelectPandora_RawSSDP_OPT
import Definitions.Def_MultiSelectPandora_RawSSDP_value
import Definitions.Def_MultiSelectPandora_RawSSDP_Reach
import Definitions.Def_MultiSelectPandora_RawSSDP_Admissible
import Definitions.Def_MultiSelectPandora_SSDPPolicy

namespace MultiSelectPandora

/-- **Condition (C3).** Beyhaghi–Han–Luqman manuscript, Definition 3.2, p.8 (PDF p.9): "the terminal reward is nonnegative … and there is an
optimal policy along whose trajectory every action has nonnegative expected marginal reward, `E[g(I_t, a_t)] ≥ 0`". -/
def RawSSDP.C3 (S : RawSSDP) : Prop :=
  (∀ st < S.L, 0 ≤ S.terminal st) ∧
  ∃ π : SSDPPolicy, S.Admissible π ∧ S.value π = S.OPT ∧
    ∀ h st R, S.Reach π h st R → h.length < S.T →
      0 ≤ ((S.outcomes (π h) st).map fun o => (o.1 : ℝ) * (o.2.1 : ℝ)).sum

end MultiSelectPandora


