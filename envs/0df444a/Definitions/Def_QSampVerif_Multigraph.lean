-- Prove2me | Definitions.Def_QSampVerif_Multigraph
-- name    : QSampVerif_Multigraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:27:10.693203+00:00
-- url     : https://prove2.me/theorems/24fae282-beb4-45e2-aab0-d06c6c088b1c
-- title:
--   Undirected multigraphs, degrees, edge boundaries, edge expansion and label disagreements
-- statement:
--   An **undirected multigraph** $G=(V,E)$ is a finite vertex set with a multiset $E$ of unordered pairs $\{u,v\}$; parallel edges and loops are allowed. All edge counts include multiplicities.
--
--   1. The **degree** of $v$ counts the edges at $v$, a loop contributing two.
--   2. For $A\subseteq V$, $\partial A$ is the multiset of edges with exactly one endpoint in $A$.
--   3. $G$ has **edge expansion at least $\alpha$** when $|\partial A|\ge\alpha|A|$ whenever $|A|\le|V|/2$.
--   4. For $S\subseteq V$ and a labelling $s$ of the vertices, the **disagreement count** is $c=\#\{uv\in E:u,v\notin S,\ s_u\ne s_v\}$ (loops never count).
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), §3.8, p.21 (PDF 22); Lemma 3.16, p.22 (PDF 23)

import Mathlib

set_option autoImplicit false

namespace QSampVerif

/-- Chung, Cojocaru, Lee, Lin, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), §3.8,
p.21 (PDF 22): an undirected multigraph on the vertex type `V`, given by its multiset of edges;
an edge is an unordered pair `s(u, v)`, parallel edges and loops `s(v, v)` are allowed. -/
structure Multigraph (V : Type*) where
  /-- The edges, with multiplicity. -/
  edges : Multiset (Sym2 V)

namespace Multigraph

variable {V : Type*} [DecidableEq V]

/-- The degree of `v`, edge counts with multiplicity; "a loop contributes two to the degree of
its vertex" (p.21). -/
def degree (G : Multigraph V) (v : V) : ℕ :=
  (G.edges.map fun e => if e = s(v, v) then 2 else if v ∈ e then 1 else 0).sum

/-- `e` has exactly one endpoint in `A`. -/
def crosses (A : Finset V) (e : Sym2 V) : Bool :=
  Sym2.lift ⟨fun u w => xor (decide (u ∈ A)) (decide (w ∈ A)), fun _ _ => Bool.xor_comm _ _⟩ e

/-- `|∂A|`: the number of edges with exactly one endpoint in `A`, with multiplicity (p.21). -/
def boundary (G : Multigraph V) (A : Finset V) : ℕ :=
  Multiset.card (G.edges.filter fun e => crosses A e = true)

/-- Edge expansion at least `α` (p.21): `|∂A| ≥ α|A|` whenever `|A| ≤ |V|/2`. -/
def HasEdgeExpansion [Fintype V] (G : Multigraph V) (α : ℝ) : Prop :=
  ∀ A : Finset V, (A.card : ℝ) ≤ (Fintype.card V : ℝ) / 2 → α * A.card ≤ G.boundary A

/-- The number `c = #{uv ∈ E : u, v ∉ S, s_u ≠ s_v}` of edges (with multiplicity) joining two
vertices outside `S` with different labels (Lemma 3.16, p.22); loops never count. -/
def disagreements (G : Multigraph V) (S : Finset V) (s : V → Bool) : ℕ :=
  Multiset.card (G.edges.filter fun e =>
    Sym2.lift ⟨fun u w => decide (u ∉ S) && decide (w ∉ S) && (s u != s w), fun u w => by
      show (decide (u ∉ S) && decide (w ∉ S) && (s u != s w)) =
        (decide (w ∉ S) && decide (u ∉ S) && (s w != s u))
      rw [bne_comm]
      cases decide (u ∉ S) <;> cases decide (w ∉ S) <;> rfl⟩ e = true)

end Multigraph

end QSampVerif


