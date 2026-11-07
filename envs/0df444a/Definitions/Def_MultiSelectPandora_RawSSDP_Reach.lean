-- Prove2me | Definitions.Def_MultiSelectPandora_RawSSDP_Reach
-- name    : MultiSelectPandora_RawSSDP_Reach
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:13:37.057147+00:00
-- url     : https://prove2.me/theorems/90dcdb24-c3c7-455c-a891-bfc46e654969
-- title:
--   Reachable points of a table
-- statement:
--   The triples (history, state, removed groups) reachable under a policy, following available actions and outcomes of positive probability, within the horizon.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §3.1, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawSSDP
import Definitions.Def_MultiSelectPandora_RawSSDP_outcomes
import Definitions.Def_MultiSelectPandora_RawSSDP_avail
import Definitions.Def_MultiSelectPandora_RawSSDP_after
import Definitions.Def_MultiSelectPandora_SSDPPolicy

namespace MultiSelectPandora

/-- **The (history, state, removed groups) triples reachable under a policy.** Auxiliary to §3.1, p.7 (PDF p.8) of the
Beyhaghi–Han–Luqman manuscript. Only outcomes of positive probability are followed. -/
inductive RawSSDP.Reach (S : RawSSDP) (π : SSDPPolicy) : List (ℕ × ℕ) → ℕ → Finset ℕ → Prop
  /-- the start -/
  | init : RawSSDP.Reach S π [] S.init ∅
  /-- one step along an available action and an outcome of positive probability -/
  | step {h : List (ℕ × ℕ)} {st : ℕ} {R : Finset ℕ} {m : ℕ} {p r : ℚ} {nx : ℕ} :
      RawSSDP.Reach S π h st R → h.length < S.T → S.avail R (π h) = true →
      (S.outcomes (π h) st)[m]? = some (p, r, nx) → 0 < p →
      RawSSDP.Reach S π (h ++ [(π h, m)]) nx (S.after R (π h))

end MultiSelectPandora


