-- Prove2me | Definitions.Def_MissionAbort_emit
-- name    : MissionAbort_emit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:49:05.255349+00:00
-- url     : https://prove2.me/theorems/cd6c92d8-cdc2-4020-9bef-92078b91c3ea
-- title:
--   Emission probabilities of the signals
-- statement:
--   The probability of emitting the signal value $y\in\{0,\dots,K\}$ from a state in a given cluster. From a healthy state it is $d_{1y}$ and from a defective state $d_{2y}$ for $y\in[K]$, and $0$ for $y=0$. From the failed state it is $1$ for $y=0$ and $0$ otherwise.
--
--   The same function drives the signals of the original system and of the surrogate system.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §3.2, p.10, and §4.1, p.14

import Mathlib
import Definitions.Def_MissionAbort_Cluster
import Definitions.Def_MissionAbort_Model

namespace MissionAbort

/-- The probability of emitting signal value `y ∈ {0, …, K}` from a state in cluster `c`
(Sun, Hu & Ye, arXiv:2505.03225v1, §3.2, p.10 and §4.1, p.14): `d_{1k}` and `d_{2k}` for `k ∈ [K]`
from the healthy and the defective state, `0` for `y = 0`; from the failed state `y = 0` with
probability one.

**Formalization Note.** `Fin.cases` splits `y` into `0` and `k.succ` with `k : Fin K`; the signal value
`k.succ` is the page's `k + 1 ∈ [K]`, read off row `D i k`. -/
def emit {K : ℕ} (M : Model K) : Cluster → Fin (K + 1) → ℝ
  | .healthy, y => Fin.cases 0 (fun k => M.D 0 k) y
  | .defective, y => Fin.cases 0 (fun k => M.D 1 k) y
  | .failed, y => if y = 0 then 1 else 0

end MissionAbort


