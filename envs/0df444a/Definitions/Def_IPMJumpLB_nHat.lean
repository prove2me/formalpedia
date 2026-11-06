-- Prove2me | Definitions.Def_IPMJumpLB_nHat
-- name    : IPMJumpLB_nHat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:09.751931+00:00
-- url     : https://prove2.me/theorems/78fa373e-7909-46aa-a10f-2d0e44117369
-- title:
--   $\hat n_k = bk^2 + 1$
-- statement:
--   The number of vertices of the Section 4 instance,
--   $$
--   \hat n_k = bk^2 + 1 .
--   $$
--   Theorem 4.1 uses the centrality parameter $\eta = \alpha \hat n_k$.
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), Section 4, p.11

import Mathlib

namespace IPMJumpLB

/-- `n̂_k = bk² + 1`, the number of vertices of the Section 4 instance (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), §4, p.11). -/
def nHat (b k : ℕ) : ℕ := b * k ^ 2 + 1

end IPMJumpLB


