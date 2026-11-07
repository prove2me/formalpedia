-- Prove2me | Definitions.Def_NoPerfectRandComp_SeedIdx
-- name    : NoPerfectRandComp_SeedIdx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:07.089333+00:00
-- url     : https://prove2.me/theorems/73eee331-e4ff-41ae-8054-90d36428a489
-- title:
--   Coordinates of the approximate-index seed
-- statement:
--   The approximate-index seed on address length $k$ reads an address $a \in \{0,1\}^k$ and, for each table location $b \in \{0,1\}^k$, a presence bit $P_b$ and a value bit $V_b$. Its coordinate set therefore has
--   $$
--   k + 2^{k+1}
--   $$
--   elements, which is $u_q$ at $k = k_q$.
--
--   **Formalization Note** The coordinates are the disjoint union of the address positions $[k]$ (0-based) and the pairs $(b, \text{tag})$, with tag `false` for $P_b$ and `true` for $V_b$.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §4.1, p.12

import Mathlib

namespace NoPerfectRandComp

/-- The coordinates of the approximate-index seed (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §4.1, p.12): an address bit `a_i`
for each `i ∈ [k]` (`Sum.inl i`), and two table bits for each `b ∈ {0,1}^k`: the presence bit
`P_b` (`Sum.inr (b, false)`) and the value bit `V_b` (`Sum.inr (b, true)`).

**Formalization Note** `[k]` is `Fin k` (0-based). There are `k + 2^{k+1}` coordinates, which is
`u_q` at `k = k_q`. -/
abbrev SeedIdx (k : ℕ) : Type := Fin k ⊕ ((Fin k → Bool) × Bool)

end NoPerfectRandComp


