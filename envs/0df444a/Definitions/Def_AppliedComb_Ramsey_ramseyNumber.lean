-- Prove2me | Definitions.Def_AppliedComb_Ramsey_ramseyNumber
-- name    : AppliedComb_Ramsey_ramseyNumber
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:17:34.515974+00:00
-- url     : https://prove2.me/theorems/c3f6b527-f02a-40f0-a033-ebf6ab454a5f
-- title:
--   The Ramsey number R(m, n) (Theorem 11.2)
-- statement:
--   Let $m, n, N$ be non-negative integers. We say that $N$ is a **Ramsey bound** for $(m, n)$ if every finite simple graph $G$ with **at least** $N$ vertices contains a complete subgraph on $m$ vertices (a set of $m$ pairwise adjacent vertices, an $m$-clique) or an independent set of size $n$ (a set of $n$ pairwise non-adjacent vertices). This property is upward closed in $N$: a Ramsey bound remains one when it is increased.
--
--   The **Ramsey number** $R(m, n)$ is the least positive Ramsey bound:
--   $$R(m, n) = \min\{N \ge 1 : \text{every graph with at least } N \text{ vertices has an } m\text{-clique or an independent set of size } n\}.$$
--   Ramsey's Theorem for Graphs (Theorem 11.2) is exactly the statement that this set is nonempty for all positive integers $m, n$, so the minimum exists.
--
--   The Ramsey number is the central quantity of the chapter: Theorem 11.2 shows it is finite, its proof bounds it by $\binom{m+n-2}{m-1}$, and Erdős's Theorem 11.4 bounds $R(n, n)$ from below by an exponential in $n$.
--
--   **Formalization Note.** `IsRamseyBound m n N` quantifies over every finite vertex type `V : Type` with `N ≤ Fintype.card V` and every `G : SimpleGraph V` (so graphs are simple: no loops, no multiple edges), and asks for Mathlib's `G.IsNClique m s` or `G.IsNIndepSet n s` for some `Finset` `s`. `ramseyNumber m n` is `sInf` of the set of positive Ramsey bounds. For $m, n \ge 1$ the set is nonempty (Theorem 11.2), so this is its least element; `sInf ∅ = 0` is never reached there, and since the lower bound of Theorem 11.4 is positive, that theorem cannot be satisfied by a junk value.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 230, Theorem 11.2 (definition of R(m, n))

import Mathlib

namespace AppliedComb.Ramsey

/-- The Ramsey property of Theorem 11.2 (Keller & Trotter, *Applied Combinatorics*, 2017 Edition,
p. 230) for the threshold `N`: every simple graph `G` on a finite vertex type with **at least** `N`
vertices contains a complete subgraph on `m` vertices (an `m`-clique) or an independent set of
size `n`. The property is upward closed in `N` by construction. -/
def IsRamseyBound (m n N : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V], N ≤ Fintype.card V → ∀ G : SimpleGraph V,
    (∃ s : Finset V, G.IsNClique m s) ∨ (∃ s : Finset V, G.IsNIndepSet n s)

/-- The Ramsey number `R(m, n)` (Keller & Trotter, p. 230, Theorem 11.2): the least positive
integer `N` with `IsRamseyBound m n N`. It is `sInf` of that set of positive integers; Theorem 11.2
(`AppliedComb.Ramsey.ramsey_theorem`) states that the set is nonempty, so `ramseyNumber m n` is its
least element. (On an empty set `sInf` would be `0`, which is never the case for `m, n ≥ 1`.) -/
noncomputable def ramseyNumber (m n : ℕ) : ℕ :=
  sInf {N : ℕ | 0 < N ∧ IsRamseyBound m n N}

end AppliedComb.Ramsey


