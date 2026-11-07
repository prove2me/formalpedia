-- Prove2me | Definitions.Def_MultiSelectPandora_RawSSDP_value
-- name    : MultiSelectPandora_RawSSDP_value
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:14:08.752787+00:00
-- url     : https://prove2.me/theorems/85d04118-1136-4761-a5f8-afafa2814d8f
-- title:
--   The expected total reward on a table
-- statement:
--   The expected total reward $E\big[\sum_{t=1}^Tg(I_t,a_t)+h(I_{T+1})\big]$ of a policy.
--
--   **Formalization Note** An unavailable action halts the process with no further reward.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §3.1, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawSSDP
import Definitions.Def_MultiSelectPandora_RawSSDP_outcomes
import Definitions.Def_MultiSelectPandora_RawSSDP_avail
import Definitions.Def_MultiSelectPandora_RawSSDP_after
import Definitions.Def_MultiSelectPandora_RawSSDP_terminal
import Definitions.Def_MultiSelectPandora_SSDPPolicy

namespace MultiSelectPandora

/-- **The expected total reward of a policy on a table**, `E[Σ_t g(I_t, a_t) + h(I_{T+1})]`. Beyhaghi–Han–Luqman manuscript, §3.1, p.7
(PDF p.8).

**Formalization Note.** An unavailable action halts the process with no further reward. -/
noncomputable def RawSSDP.value (S : RawSSDP) (π : SSDPPolicy) : ℝ := go S.T S.init ∅ []
where
  /-- the recursion on the steps left, with the state, the removed groups and the history -/
  go : ℕ → ℕ → Finset ℕ → List (ℕ × ℕ) → ℝ
    | 0, st, _, _ => S.terminal st
    | t + 1, st, R, h =>
      if S.avail R (π h) = true then
        ((S.outcomes (π h) st).zipIdx.map fun e =>
          (e.1.1 : ℝ) * ((e.1.2.1 : ℝ) + go t e.1.2.2 (S.after R (π h)) (h ++ [(π h, e.2)]))).sum
      else 0

end MultiSelectPandora


