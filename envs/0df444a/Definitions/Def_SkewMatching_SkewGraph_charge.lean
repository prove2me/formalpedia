-- Prove2me | Definitions.Def_SkewMatching_SkewGraph_charge
-- name    : SkewMatching_SkewGraph_charge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:31.252204+00:00
-- url     : https://prove2.me/theorems/d4bd7aa1-dadd-4af7-a518-7201edf56257
-- title:
--   Definition 12 — edge charges, and the heights of Lemma 20
-- statement:
--   For a barrier $(A,A',X_1,\dots,X_k,M)$ of $H$ with barrier edges $e_i$ and a parameter $K$, put $\phi(u)=\mathbb 1[u\in A']-\mathbb 1[u\in A]$. The **charge** of an edge $e=(u,v)$ is
--
--   $$
--   d_e=\phi(u)-\phi(v)+\sum_i\mathbb 1[e=e_i\vee e=e_i']-\sum_{X_i:|X_i|\le 2n/K}\mathbb 1[e\in\partial X_i\setminus\{e_i,e_i'\}],
--   $$
--
--   where $\partial X$ is the set of edges between $X$ and its complement, in both directions, and $n$ is the number of vertices.
--
--   The **heights** on the left and right copies of $u$ in the auxiliary graph $G_1$ are $h(u^L)=\phi(u)-\mathbb 1[u\in X_i,|X_i|\le 2n/K]$ and $h(u^R)=\phi(u)+\mathbb 1[u\in X_i,|X_i|\le 2n/K]$.
--
--   Charges drive the barrier toggle operation: a negatively charged edge bypasses the barrier, and sampling is by weight times $|d_e|$.
--
--   **Formalization Note** The barrier is on $H$ and the charges are on all edges of $G$, where the negative ones live. $|X_i|\le 2n/K$ is written $K|X_i|\le 2n$. The edge $e_i$ is identified by its description (the edge of $H$ from $A$ to $X_i$), which is unique on a barrier; the value is meaningful for a barrier of $H$.
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), Definition 12, p.6; Lemma 20, p.13

import Mathlib
import Definitions.Def_SkewMatching_Partition

namespace SkewMatching

namespace SkewGraph

open scoped Classical

variable {V E : Type*} (G : SkewGraph V E)

/-- The vertex potential `ϕ(u) = 1[u ∈ A′] − 1[u ∈ A]` (Definition 12, p.6). -/
noncomputable def phi (P : Partition V) (u : V) : ℤ :=
  (if u ∈ G.symm P.A then 1 else 0) - (if u ∈ P.A then 1 else 0)

/-- `e` is the barrier edge `e_i` from `A` to the fragment `X`, or its symmetric edge `e′_i`. In a barrier the edge
from `A` to `X` in `H` is unique, so this is `e = e_i ∨ e = e′_i`. -/
def IsBarrierEdgeAt (H : Finset E) (P : Partition V) (X : Finset V) (e : E) : Prop :=
  (e ∈ H ∧ G.tail e ∈ P.A ∧ G.head e ∈ X) ∨
    (G.σE e ∈ H ∧ G.tail (G.σE e) ∈ P.A ∧ G.head (G.σE e) ∈ X)

/-- `e ∈ ∂X`: "all edges between S and V \ S, including both directions for directed graphs" (§2.3, p.4). -/
def InBoundary (X : Finset V) (e : E) : Prop :=
  (G.tail e ∈ X ∧ G.head e ∉ X) ∨ (G.tail e ∉ X ∧ G.head e ∈ X)

/-- A fragment is **small** if `|X| ≤ 2n/K`, written without division as `K |X| ≤ 2n`, with `n` the vertex count. -/
def IsSmall [Fintype V] (K : ℕ) (X : Finset V) : Prop := K * X.card ≤ 2 * Fintype.card V

/-- **Definition 12**, p.6: the charge of the edge `e = (u, v)` for a barrier of `H` and a parameter `K`:

`d_e = ϕ(u) − ϕ(v) + Σ_i 1[e = e_i ∨ e = e′_i] − Σ_{X_i : |X_i| ≤ 2n/K} 1[e ∈ ∂X_i \ {e_i, e′_i}]`.

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript
sha256 3fc151f5…), Definition 12, p.6.

**Formalization Note.** The barrier is on `H` and the charges are on all edges of `G`, which is where the negative
ones live. The value is meaningful for a barrier of `H`, where `e_i` exists and is unique. -/
noncomputable def charge [Fintype V] (K : ℕ) (H : Finset E) (P : Partition V) (e : E) : ℤ :=
  G.phi P (G.tail e) - G.phi P (G.head e)
    + (P.frags.map fun X => if G.IsBarrierEdgeAt H P X e then (1 : ℤ) else 0).sum
    - ((P.frags.filter fun X => IsSmall K X).map fun X =>
        if G.InBoundary X e ∧ ¬ G.IsBarrierEdgeAt H P X e then (1 : ℤ) else 0).sum

/-- `1[u ∈ X_i, |X_i| ≤ 2n/K]`, the indicator of the small fragments (Lemma 20, p.13). -/
noncomputable def smallIndicator [Fintype V] (K : ℕ) (P : Partition V) (u : V) : ℤ :=
  if ∃ X ∈ P.frags, u ∈ X ∧ IsSmall K X then 1 else 0

/-- The height `h(u^L) = ϕ(u) − 1[u ∈ X_i, |X_i| ≤ 2n/K]` of the left copy of `u` in `G₁` (Lemma 20, p.13). -/
noncomputable def heightL [Fintype V] (K : ℕ) (P : Partition V) (u : V) : ℤ :=
  G.phi P u - smallIndicator K P u

/-- The height `h(u^R) = ϕ(u) + 1[u ∈ X_i, |X_i| ≤ 2n/K]` of the right copy of `u` in `G₁` (Lemma 20, p.13). -/
noncomputable def heightR [Fintype V] (K : ℕ) (P : Partition V) (u : V) : ℤ :=
  G.phi P u + smallIndicator K P u

end SkewGraph

end SkewMatching


