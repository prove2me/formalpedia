-- Prove2me | Definitions.Def_ChvatalPolytopes_SeriesParallel_CircuitCover
-- name    : ChvatalPolytopes_SeriesParallel_CircuitCover
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:24:44.479553+00:00
-- url     : https://prove2.me/theorems/7a4890cc-fcdd-464b-a15e-9e8c110a72e9
-- title:
--   Components that are isolated vertices, isolated edges or odd circuits (proof of Theorem 7.1)
-- statement:
--   Let $F$ be a graph on $V$ and $W\subseteq V$ (in the intended use, the vertex set of a connected component of $F$). Then $W$ is an **isolated vertex, isolated edge or odd circuit** of $F$ if
--
--   1. $W=\{v\}$ for a vertex $v$; or
--   2. $W=\{v,w\}$ with $vw$ an edge of $F$; or
--   3. $F[W]$ is a cycle of length $2k+1$ for some $k\ge1$.
--
--   With a component on $n$ vertices we associate the number
--   $$
--   \operatorname{val}(n)=\begin{cases}1,& n\le 2,\\ (n-1)/2,& n\ge 3,\end{cases}
--   $$
--   so that, if $F$ has $a$ isolated vertices, $b$ isolated edges and $c_k$ circuits of length $2k+1$, the sum of $\operatorname{val}$ over the components of $F$ is $a+b+\sum_k k\,c_k$.
--
--   These are the objects of statements (i) and (ii) in the proof of Theorem 7.1, which are what the induction constructs.
--
--   **Formalization Note** `IsVertexEdgeOrOddCircuit F W` is the three-way disjunction, with the odd-circuit case given by `InducesOddCircuit` of the `OddCycleLP` definition file. `componentValue n` is computed in `ℕ`; its value at `n = 0` (never a component size) is irrelevant, and on $n=2k+1\ge3$ the truncated operations give exactly $k$.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 151, proof of Theorem 7.1, (i)–(ii)

import Mathlib
import Definitions.Def_ChvatalPolytopes_SeriesParallel_OddCycleLP

namespace ChvatalPolytopes.SeriesParallel

/-- A vertex set `W` (a connected component of the graph `F`) is an **isolated vertex**, an
**isolated edge** or an **odd circuit** of `F` (Chvátal 1975, p. 151, proof of Theorem 7.1, (i)):
`W = {v}`; or `W = {v, w}` with `v w` an edge of `F`; or `F[W]` is a cycle of length `2k + 1`,
`k ≥ 1`. -/
def IsVertexEdgeOrOddCircuit {V : Type*} (F : SimpleGraph V) (W : Set V) : Prop :=
  (∃ v : V, W = {v}) ∨ (∃ v w : V, F.Adj v w ∧ W = {v, w}) ∨ InducesOddCircuit F W

/-- The contribution of a component with `n` vertices to `a + b + ∑ k c_k`
(Chvátal 1975, p. 151, proof of Theorem 7.1, (ii)): `1` for an isolated vertex (`n = 1`) or an
isolated edge (`n = 2`), and `k = (n − 1)/2` for a circuit of length `n = 2k + 1 ≥ 3`. -/
def componentValue (n : ℕ) : ℕ :=
  if n ≤ 2 then 1 else (n - 1) / 2

end ChvatalPolytopes.SeriesParallel


