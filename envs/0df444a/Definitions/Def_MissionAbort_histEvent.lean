-- Prove2me | Definitions.Def_MissionAbort_histEvent
-- name    : MissionAbort_histEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:48:06.881719+00:00
-- url     : https://prove2.me/theorems/2b6173b6-fba4-4c25-91b5-c7456307789c
-- title:
--   The event $\{Y_{1:n}=y\}$
-- statement:
--   The event that the history up to $n$ equals $y$.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §3.3, p.10

import Mathlib

namespace MissionAbort

/-- The event `{Y_{1:n} = y}` (Sun, Hu & Ye, arXiv:2505.03225v1, §3.3, p.10). -/
def histEvent {K : ℕ} {Ω : Type*} (Y : ℕ → Ω → Fin (K + 1)) (n : ℕ) (y : Fin n → Fin (K + 1)) :
    Set Ω :=
  {ω | ∀ i : Fin n, Y (i.val + 1) ω = y i}

end MissionAbort


