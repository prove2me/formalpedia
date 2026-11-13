-- Prove2me | Definitions.Def_KnodelPrimeCordial_knodel
-- name    : KnodelPrimeCordial_knodel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T05:59:04.873242+00:00
-- url     : https://prove2.me/theorems/d8f0c0b2-aa00-462b-989b-e16279ff7680
-- title:
--   The Knödel graph $W_{\Delta,n}$
-- statement:
--   Let $n\ge 2$ be even and $1\le\Delta\le\lfloor\log_2 n\rfloor$. The **Knödel graph** $W_{\Delta,n}$ has the $n$ vertices $(i,j)$ with $i\in\{1,2\}$ and $0\le j\le n/2-1$. For every $j$ there is an edge between $(1,j)$ and each vertex
--
--   $$
--   \bigl(2,\ j+2^k-1 \bmod n/2\bigr),\qquad k=0,1,\dots,\Delta-1 .
--   $$
--
--   There are no other edges, so $W_{\Delta,n}$ is bipartite with sides $\{(1,j)\}$ and $\{(2,j)\}$. For $\Delta=3$ the offsets are $0,1,3$, and for even $n\ge 8$ they are distinct modulo $n/2$, so $W_{3,n}$ is $3$-regular with $3n/2$ edges.
--
--   Knödel graphs were introduced as the topology of a time-optimal gossiping scheme and are studied as interconnection networks. This definition is the object of the mission's main theorem.
--
--   **Formalization Note** The sides $1,2$ are the `Fin 2` values $0,1$ and $j$ ranges over `Fin (n / 2)`. The definition is written for all $\Delta,n$, but it is the paper's $W_{\Delta,n}$ only on the paper's domain ($n$ even, $1\le\Delta\le\lfloor\log_2 n\rfloor$); for $\Delta=3$ that is even $n\ge 8$, and every theorem of the mission restricts to it. A `DecidableRel` instance makes the edge set computable.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), §1, p.2 (PDF p.2), last paragraph (definition of W_{Δ,n}, after Cohen–Fraigniaud–Gavoille)

import Mathlib

namespace KnodelPrimeCordial

/-- **The Knödel graph `W_{Δ,n}`** (Haque, Khanam, Shahriar, *Prime cordial labeling of
Knödel graph*, manuscript (2026), §1, p.2, last paragraph): "The vertices of W∆,n are the cupels
(i, j) with i = 1, 2 and 0 ≤ j ≤ n/2 − 1. For every j, 0 ≤ j ≤ n/2 − 1, there is an edge
between vertex (1, j) and every vertex (2, j + 2^k − 1 mod n/2), for k = 0, 1, . . . , ∆ − 1."

Vertices are pairs `(i, j) : Fin 2 × Fin (n / 2)`; `(0, j)` and `(1, j')` are adjacent iff
`j' ≡ j + 2^k − 1 (mod n/2)` for some `k < Δ`.

**Formalization Note** The paper's sides `i = 1, 2` are the `Fin 2` values `0, 1`. The
definition is written for all `Δ, n`; it is the paper's `W_{Δ,n}` when `n` is even and
`1 ≤ Δ ≤ ⌊log₂ n⌋` (for `Δ = 3`: even `n ≥ 8`), and every statement of this development
restricts to that domain. `j + 2^k − 1` never truncates in `ℕ` since `2^k ≥ 1`. -/
def knodel (Δ n : ℕ) : SimpleGraph (Fin 2 × Fin (n / 2)) where
  Adj p q :=
    (p.1 = 0 ∧ q.1 = 1 ∧ ∃ k, k < Δ ∧ q.2.val = (p.2.val + 2 ^ k - 1) % (n / 2)) ∨
    (q.1 = 0 ∧ p.1 = 1 ∧ ∃ k, k < Δ ∧ p.2.val = (q.2.val + 2 ^ k - 1) % (n / 2))
  symm := ⟨fun p q h => by
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h⟩
  loopless := ⟨fun p h => by
    rcases h with ⟨h0, h1, -⟩ | ⟨h0, h1, -⟩ <;> rw [h0] at h1 <;> exact absurd h1 (by decide)⟩

instance (Δ n : ℕ) : DecidableRel (knodel Δ n).Adj := fun p q => by
  unfold knodel
  infer_instance

end KnodelPrimeCordial


