-- Prove2me | Definitions.Def_NondetConn_cyclicOrder
-- name    : NondetConn_cyclicOrder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:21:27.52976+00:00
-- url     : https://prove2.me/theorems/aedd6544-1497-494c-8405-81edb361597d
-- title:
--   Cyclic order $(w\,x\,y)$ along a permutation
-- statement:
--   Let $\sigma$ be a permutation of $[n]$ and $w, x, y \in [n]$. The points **follow the cyclic order $(w\,x\,y)$ along $\sigma$** when, walking from $w$ along $\sigma$, the point $x$ is reached before $y$ is first reached: there are integers $0 < i < j$ with
--   $$
--   \sigma^i(w) = x, \qquad \sigma^j(w) = y, \qquad \sigma^k(w) \ne y \text{ for all } 0 \le k < j .
--   $$
--   For three distinct points on one cycle exactly one of $(w\,x\,y)$ and $(w\,y\,x)$ holds.
--
--   **Formalization Note** $j$ is the first time the walk from $w$ hits $y$, so the walk stays within one lap of the cycle; without this minimality every two other points of an $n$-cycle would be in both orders.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §4.1, p.11 (PDF p.13)

import Mathlib

namespace NondetConn

/-- **Cyclic order `(w x y)` along a permutation** (Zhang, *Settling Nondeterministic Communication Complexity of Graph Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac),
§4.1, p.11): the points `w, x, y` follow the cyclic order `(w x y)` along `σ` when, walking from
`w` along `σ`, the point `x` is reached strictly before the point `y` is first reached:
there are `0 < i < j` with `σ^i(w) = x`, `σ^j(w) = y` and `σ^k(w) ≠ y` for all `k < j`.

**Formalization Note** `j` is the least exponent with `σ^j(w) = y`, so the walk stays inside one
lap of the cycle of `w`; without this minimality, on an `n`-cycle any two other points would be
in both orders. For three distinct points of one `n`-cycle exactly one of `(w x y)` and
`(w y x)` holds. -/
def cyclicOrder {n : ℕ} (σ : Equiv.Perm (Fin n)) (w x y : Fin n) : Prop :=
  ∃ i j : ℕ, 0 < i ∧ i < j ∧ (σ ^ i) w = x ∧ (σ ^ j) w = y ∧ ∀ k < j, (σ ^ k) w ≠ y

end NondetConn


