-- Prove2me | Definitions.Def_NondetConn_bConn
-- name    : NondetConn_bConn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:23:31.354021+00:00
-- url     : https://prove2.me/theorems/f5451114-3a6a-42f8-a85c-fc195540e49e
-- title:
--   Bipartite connectivity $\mathsf{bConn}_N$ on permutations of $[n]$
-- statement:
--   Let $N = 2n$. In **bipartite connectivity** $\mathsf{bConn}_N$, Alice and Bob each hold a perfect matching across a balanced bipartition of $N$ vertices ($n$ per side); equivalently Alice holds a permutation $a$ and Bob a permutation $b$ of $[n]$. The graph is connected iff $b^{-1}a$ is a single $n$-cycle:
--   $$
--   \mathsf{bConn}_N(a,b) = 1 \iff b^{-1}a \text{ is a single } n\text{-cycle}.
--   $$
--
--   This is the communication problem of the mission: its nondeterministic complexity is $\Theta(N\log N)$.
--
--   **Formalization Note** The function is indexed by $n = N/2$, $[n]$ is `Fin n` (0-based), $b^{-1}a$ is `b⁻¹ * a`, and "single $n$-cycle" is the predicate `conn` (so for $n = 1$ the only input is a 1-input).
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §1, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_NondetConn_conn

namespace NondetConn

/-- **Bipartite connectivity** `bConn_N` with `N = 2n` (Zhang, *Settling Nondeterministic Communication Complexity of Graph Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac),
§1, p.1): Alice holds a permutation `a` and Bob a permutation `b` of `[n]` (two perfect matchings
across a balanced bipartition with `n = N/2` vertices per side), and `bConn_N(a, b) = 1` iff
`b⁻¹a` is a single `n`-cycle.

**Formalization Note** `[n]` is `Fin n` (0-based), the parameter is `n = N/2` rather than
`N`, and `b⁻¹a` is `b⁻¹ * a` (apply `a` first), via `conn`. -/
def bConn (n : ℕ) (a b : Equiv.Perm (Fin n)) : Prop :=
  conn a b

instance (n : ℕ) (a b : Equiv.Perm (Fin n)) : Decidable (bConn n a b) := by
  unfold bConn; infer_instance

end NondetConn


