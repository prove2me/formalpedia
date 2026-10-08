-- Prove2me | Definitions.Def_CompOT_Vertices_Defs
-- name    : CompOT_Vertices_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:47.740032+00:00
-- url     : https://prove2.me/theorems/c1244c88-305d-41b4-b4a2-ed758fd8d101
-- title:
--   (2.10), §3.4, §3.4.1, pp. 370, 405–406 — couplings U(a, b), extremal points, the support graph G(P) and the nonzero entries of P
-- statement:
--   Fix integers $n, m \ge 0$. Index sets are $[\![n]\!] = \{1,\dots,n\}$ and $[\![m]\!]$.
--
--   1. **Couplings (2.10).** For $a \in \mathbb R^n$ and $b \in \mathbb R^m$, the transportation polytope is
--   $$U(a,b) = \{ P \in \mathbb R_+^{n\times m} : P\mathbb 1_m = a,\ P^\top \mathbb 1_n = b \},$$
--   the nonnegative $n\times m$ matrices with row sums $a_i$ and column sums $b_j$. The pairing $\langle C, P\rangle = \sum_{i,j} C_{ij}P_{ij}$ is the transport cost of $P$ for a cost matrix $C$.
--
--   2. **Extremal point (§3.4, p. 405).** A point $x$ of a set $S$ is extremal in $S$ if, whenever $y, z \in S$ satisfy $x = (y+z)/2$, necessarily $x = y = z$. The points $y, z$ range over $S$ itself.
--
--   3. **Support graph (§3.4.1, p. 406).** Take the node set $V \cup V'$ with $V = \{1,\dots,n\}$ and $V' = \{1',\dots,m'\}$. For a matrix $P$, let $S(P)$ be the set of pairs $(i, j')$ with $P_{ij} > 0$. The support graph is $G(P) = (V \cup V', S(P))$: the node $i$ is joined to $j'$ exactly when $P_{ij} > 0$, and no two nodes of $V$ (or of $V'$) are joined.
--
--   4. **Nonzero entries.** The set of index pairs $(i,j)$ with $P_{ij} \ne 0$.
--
--   These are the objects of Proposition 3.4: the support of a vertex of $U(a,b)$ is a forest of the complete bipartite graph between sources and targets.
--
--   **Formalization Note** Indices are `Fin n`, `Fin m` (0-based). The node set $V \cup V'$ is the sum type `Fin n ⊕ Fin m`, with `Sum.inl i` the node $i$ and `Sum.inr j` the node $j'$. The book calls the edges $(i, j')$ directed; the cycles in the proof of Proposition 3.4 alternate between $V$ and $V'$, so $G(P)$ is encoded as an undirected simple graph and "no cycles" is Mathlib's `SimpleGraph.IsAcyclic`. Extremality is the book's midpoint definition, relative to the given set (for convex sets it coincides with Mathlib's `Set.extremePoints`).
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), (2.10), p. 370; §3.4, p. 405 (extremal point); §3.4.1, p. 406 (bipartite graph, S(P), G(P))

import Mathlib
import Definitions.Def_CompOT_Assignment_Defs

namespace CompOT.Vertices

/-- Extremal point (vertex) of a set, in the midpoint form of §3.4, p. 405: `x ∈ s`, and
whenever `y, z ∈ s` satisfy `x = (y + z)/2`, then `x = y = z`. The points `y, z` range over
`s` itself, not over the whole space. (For a convex set this coincides with Mathlib's
`Set.extremePoints`, which uses open segments.) -/
def IsExtremal {E : Type*} [AddCommGroup E] [Module ℝ E] (s : Set E) (x : E) : Prop :=
  x ∈ s ∧ ∀ y ∈ s, ∀ z ∈ s, x = (1 / 2 : ℝ) • (y + z) → x = y ∧ x = z

/-- The relation underlying the support graph: a source node `i` (`Sum.inl i`) and a target
node `j′` (`Sum.inr j`) are related exactly when `P_{ij} > 0`; no other pairs are related. -/
def supportRel {n m : ℕ} (P : Matrix (Fin n) (Fin m) ℝ) :
    Fin n ⊕ Fin m → Fin n ⊕ Fin m → Prop
  | Sum.inl i, Sum.inr j => 0 < P i j
  | Sum.inr j, Sum.inl i => 0 < P i j
  | _, _ => False

/-- The support graph `G(P) = (V ∪ V′, S(P))` of §3.4.1, p. 406, as an undirected simple graph
on `V ∪ V′ = Fin n ⊕ Fin m` (`Sum.inl i` is the node `i`, `Sum.inr j` the node `j′`): the
edge `{i, j′}` is present iff `P_{ij} > 0`, and there are no edges inside `V` or inside `V′`.
The book's edges `(i, j′)` are directed, but the cycles of Proposition 3.4 alternate between
`V` and `V′`, i.e. they are cycles of this undirected bipartite graph. -/
def supportGraph {n m : ℕ} (P : Matrix (Fin n) (Fin m) ℝ) : SimpleGraph (Fin n ⊕ Fin m) where
  Adj := supportRel P
  symm := ⟨by
    intro u v h
    cases u <;> cases v <;> simp_all [supportRel]⟩
  loopless := ⟨by
    intro u h
    cases u <;> simp_all [supportRel]⟩

/-- The set of index pairs `(i, j)` with `P_{ij} ≠ 0` (the nonzero entries of `P`). -/
noncomputable def nonzeroEntries {n m : ℕ} (P : Matrix (Fin n) (Fin m) ℝ) :
    Finset (Fin n × Fin m) := by
  classical
  exact Finset.univ.filter fun p => P p.1 p.2 ≠ 0

end CompOT.Vertices


