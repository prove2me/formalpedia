-- Prove2me | Definitions.Def_ZeroOneExpansion_edgeExpansion
-- name    : ZeroOneExpansion_edgeExpansion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:52.658195+00:00
-- url     : https://prove2.me/theorems/4743a6db-a40f-4072-8006-e339303db2a4
-- title:
--   Edge expansion (Cheeger constant) $h(G)$ of a graph and the edge boundary $\delta_G(S)$
-- statement:
--   Let $G=(V,E)$ be a graph. For $S\subseteq V$, the **edge boundary** $\delta_G(S)=\{uv\in E: u\in S,\ v\notin S\}$ is the set of edges with exactly one endpoint in $S$. The **edge expansion** (Cheeger constant) of $G$ is
--   $$h(G)=\min\Big\{\frac{|\delta_G(S)|}{|S|}\;:\; S\subseteq V,\ 1\le |S|\le \frac{|V|}{2}\Big\}.$$
--
--   Edge expansion measures the global connectivity of a graph; it is the quantity bounded in the Mihail–Vazirani conjecture and in Theorem 1.
--
--   **Formalization Note** The boundary is the set of ordered pairs $(u,v)$ with $u\in S$, $v\notin S$ and $u\sim v$, so each boundary edge is counted once. $h(G)$ takes values in the extended reals and is the infimum over the admissible sets ($1\le|S|$ and $2|S|\le|V|$, which avoids rounding $|V|/2$); for a finite graph this infimum is the minimum. If no set is admissible (one vertex, or an infinite vertex set) the value is $+\infty$, so an upper bound on $h$ is never satisfied vacuously.
-- source:
--   Yang, 0/1-Polytopes with Exponentially Small Edge Expansion, arXiv:2608.01870 (pdf sha256 53e57bdc2a5505f50b990dfb27d47df0f7d5e2feffc89b808f29d40cff38be53), §1, p.1, "edge expansion" and "boundary"

import Mathlib

set_option autoImplicit false

namespace ZeroOneExpansion

/-- The **edge boundary** `δ_G(S)` of a vertex set `S` (Yang, *0/1-Polytopes with Exponentially Small
Edge Expansion*, arXiv:2608.01870, §1, p.1: "δG(S) := {uv ∈ E : u ∈ S, v ∉ S} is the boundary of S,
the set of edges with exactly one endpoint in S").

**Formalization Note** An edge with exactly one endpoint in `S` is recorded once, as the ordered
pair `(u, v)` oriented out of `S` (`u ∈ S`, `v ∉ S`). So `(edgeBoundary G S).ncard` is the number of
boundary edges `|δ_G(S)|`. -/
def edgeBoundary {V : Type*} (G : SimpleGraph V) (S : Set V) : Set (V × V) :=
  {p | p.1 ∈ S ∧ p.2 ∉ S ∧ G.Adj p.1 p.2}

/-- The **edge expansion** (Cheeger constant) of a graph (arXiv:2608.01870, §1, p.1):
`h(G) := min { |δG(S)| / |S| : S ⊆ V, 1 ≤ |S| ≤ |V|/2 }`.

**Formalization Note** The value lies in `EReal` and is the infimum over the admissible sets `S`,
those with `1 ≤ |S|` and `2·|S| ≤ |V|` (this avoids truncating `|V|/2`). For a finite vertex type
the admissible family is finite, so the infimum is the paper's minimum whenever it is nonempty. When
no set is admissible (one vertex, or an infinite vertex type, where `Nat.card V = 0`) the value is
`⊤`, so an upper bound `edgeExpansion G ≤ x` with `x` real is never vacuous. Cardinalities are
`Set.ncard`/`Nat.card`; no `Fintype` instance is assumed. -/
noncomputable def edgeExpansion {V : Type*} (G : SimpleGraph V) : EReal :=
  ⨅ (S : Set V) (_ : 1 ≤ S.ncard ∧ 2 * S.ncard ≤ Nat.card V),
    ((((edgeBoundary G S).ncard : ℝ) / (S.ncard : ℝ) : ℝ) : EReal)

end ZeroOneExpansion


