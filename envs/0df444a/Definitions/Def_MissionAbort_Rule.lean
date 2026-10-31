-- Prove2me | Definitions.Def_MissionAbort_Rule
-- name    : MissionAbort_Rule
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:48:04.890778+00:00
-- url     : https://prove2.me/theorems/ca45f1c0-ff87-4f72-9303-7c86293c618d
-- title:
--   Decision rules
-- statement:
--   A family of decision rules $a_n:\{0,\dots,K\}^n\to\{0,1\}$, where $a_n(y_{1:n})=1$ means aborting the mission at time $n\delta$. Only $n\in[N-1]$ is consulted.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §4, p.11

import Mathlib

namespace MissionAbort

/-- A family of decision rules (Sun, Hu & Ye, arXiv:2505.03225v1, §4, p.11): `aₙ : {0, …, K}ⁿ → {0, 1}`,
with `true` meaning abort at time `nδ`.

**Formalization Note.** `y : Fin n → Fin (K + 1)` is the history `y_{1:n}`, with `y i` the page's
`y_{i+1}`. Only `1 ≤ n ≤ N − 1` is consulted. -/
abbrev Rule (K : ℕ) : Type := (n : ℕ) → (Fin n → Fin (K + 1)) → Bool

end MissionAbort


