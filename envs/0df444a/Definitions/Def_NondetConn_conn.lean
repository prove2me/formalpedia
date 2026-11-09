-- Prove2me | Definitions.Def_NondetConn_conn
-- name    : NondetConn_conn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:19:45.357715+00:00
-- url     : https://prove2.me/theorems/f7eeb9db-2357-4a9c-90ba-ee31274ebd3e
-- title:
--   Single-cycle condition: $b^{-1}a$ is one cycle through every point
-- statement:
--   Let $X$ and $Y$ be finite sets and let $a, b : X \to Y$ be bijections. Viewed as two perfect matchings between the sides $X$ and $Y$ of a balanced bipartite graph, they span a connected graph exactly when the permutation $b^{-1}a$ of $X$ (first $a$, then $b^{-1}$) consists of a **single cycle** through every point of $X$. We write $\mathrm{conn}(a,b)$ for this condition:
--   $$
--   \mathrm{conn}(a,b) \iff \text{for all } x, x' \in X,\ x' = (b^{-1}a)^k(x) \text{ for some } k \in \mathbb Z .
--   $$
--
--   This is the predicate behind bipartite connectivity $\mathrm{bConn}_N$; it is stated for bijections between two possibly different finite sets so that the restricted pairs $(a_{(u,v)}, b_{(u,v)})$ on $[n]\setminus\{u\} \to [n]\setminus\{v\}$ can be tested without renaming.
--
--   **Formalization Note** The condition is "any two points lie in the same cycle" (`Equiv.Perm.SameCycle`), not Mathlib's `IsCycle`: the identity of a one-point set counts as a single 1-cycle, as in the paper ($|C_1| = 0! = 1$). For $|X| \ge 2$ the two notions agree for permutations with full support.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §1, p.1 (PDF p.3), and §3 "Permutations", p.8 (PDF p.10)

import Mathlib

namespace NondetConn

/-- **Connectivity of a pair of perfect matchings** (Zhang, *Settling Nondeterministic Communication Complexity of Graph Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac),
§1, p.1, and §3 "Permutations", p.8). Two bijections `a b : X ≃ Y` between finite sets are the
perfect matchings of a balanced bipartite graph with sides `X` and `Y`; the graph is connected
iff the permutation `b⁻¹a` of `X` (apply `a`, then `b⁻¹`) consists of a single cycle through
every point of `X`, i.e. any two points of `X` lie in the same cycle of `b⁻¹a`.

**Formalization Note** "Single cycle" is `∀ x x', SameCycle (b⁻¹a) x x'`, not Mathlib's
`IsCycle`: the identity of a one-point set counts as a single 1-cycle, as in the paper
(`|C₁| = 0! = 1`, `S₁ = log 1 = 0`, p.10). For `|X| ≥ 2` the two notions agree (with full
support). The permutation `b⁻¹a` is written `a.trans b.symm`. -/
def conn {X Y : Type*} (a b : X ≃ Y) : Prop :=
  ∀ x x' : X, Equiv.Perm.SameCycle (a.trans b.symm) x x'

instance {X Y : Type*} [Fintype X] [DecidableEq X] (a b : X ≃ Y) : Decidable (conn a b) := by
  unfold conn; infer_instance

end NondetConn


