-- Prove2me | Definitions.Def_IPMJumpLB_mHat
-- name    : IPMJumpLB_mHat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:10.855084+00:00
-- url     : https://prove2.me/theorems/fc10552c-99df-401e-b4f7-80c4ef61ef74
-- title:
--   $\hat m_k = (2b-2)k^2 + k$
-- statement:
--   The number of arcs of the Section 4 instance,
--   $$
--   \hat m_k = (2b - 2)k^2 + k .
--   $$
--
--   **Formalization Note** Natural-number arithmetic; $2b - 2$ is the true difference for $b \ge 1$, and the paper's $b = \lceil 6/\alpha\rceil$ is at least $7$.
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), Section 4, p.11

import Mathlib

namespace IPMJumpLB

/-- `m̂_k = (2b − 2)k² + k`, the number of arcs of the Section 4 instance (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), §4, p.11).

**Formalization Note** Natural-number arithmetic; `2b − 2` is the true difference whenever
`b ≥ 1` (the paper's `b = ⌈6/α⌉ ≥ 7`). -/
def mHat (b k : ℕ) : ℕ := (2 * b - 2) * k ^ 2 + k

end IPMJumpLB


