-- Prove2me | Definitions.Def_EdmondsMatching65_Polyhedron_MatchingPolyhedron
-- name    : EdmondsMatching65_Polyhedron_MatchingPolyhedron
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T14:24:10.133989+00:00
-- url     : https://prove2.me/theorems/7495beae-e87f-4d17-a80a-fd135453a80f
-- title:
--   The polyhedron C of inequalities (1)–(3), the matching vectors P, and the linear form W of (4)
-- statement:
--   Let $G$ be a finite graph with nodes $V$ and edges $E$, and consider real vectors $x=(x_e)_{e\in E}$, one variable per edge.
--
--   The polyhedron $C\subseteq\mathbb R^E$ is the set of $x$ satisfying
--
--   1. $x_e\ge 0$ for every edge $e$;
--   2. for every node $v$, $\displaystyle\sum_{e\text{ meets }v}x_e\le 1$;
--   3. for every set $S$ of $2r+1$ nodes, where $r$ is a strictly positive integer, $\displaystyle\sum_{e\text{ has both ends in }S}x_e\le r$.
--
--   The set $P$ of **matching vectors** is the set of $x$ whose components are all $0$ or $1$ (condition (I)) and which satisfy (2); these are exactly the incidence vectors of matchings of $G$.
--
--   For a weight vector $c\in\mathbb R^E$ the linear form (4) is
--   $$W(c,x)=\sum_{e\in E}c_e\,x_e .$$
--
--   Maximizing $W$ over $P$ is the maximum-weight matching problem; Edmonds' Theorem (P) says that $P$ is exactly the vertex set of $C$, so this problem is the linear program of maximizing $W$ over $C$.
--
--   **Formalization Note** Odd sets are encoded by an explicit natural number $r\ge 1$ with $|S|=2r+1$; sets of even size and singletons carry no inequality (3). The graph is given by a finite node type $V$, a finite edge type $E$ and, for each edge, the unordered pair of its ends (no loops). Parallel edges are allowed, which covers the contracted graphs of Theorem (M); a simple graph is the special case of an injective end map. Vectors $x$ have one real coordinate per edge.
-- source:
--   Edmonds, Maximum Matching and a Polyhedron With 0,1-Vertices, J. Res. NBS 69B (1965), pp. 125–126, §2, inequalities (1)–(3), condition (I), the definition of P, and (4)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph

namespace EdmondsMatching65.Polyhedron

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The left side of inequality (2) at node `v` (§2, p. 126): the sum of `x e` over the edges `e`
of `G` which meet `v`. -/
def degSum (G : Graph V E) (x : E → ℝ) (v : V) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e => v ∈ G.ends e), x e

/-- The left side of inequality (3) for a node set `S` (§2, p. 126): the sum of `x e` over the
edges `e` of `G` with both ends in `S`. -/
def insideSum (G : Graph V E) (x : E → ℝ) (S : Finset V) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e => G.ends e ∈ S.sym2), x e

/-- The polyhedron `C` (§2, pp. 125–126): the vectors `x`, one real coordinate per edge, with
(1) `x e ≥ 0` for every edge;
(2) `∑_{e meets v} x e ≤ 1` for every node `v`;
(3) `∑_{e ⊆ S} x e ≤ r` for every set `S` of `2r + 1` nodes, `r` a strictly positive integer. -/
def matchingPolyhedron (G : Graph V E) : Set (E → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ (∀ v : V, degSum G x v ≤ 1) ∧
    ∀ (S : Finset V) (r : ℕ), 1 ≤ r → S.card = 2 * r + 1 → insideSum G x S ≤ (r : ℝ)}

/-- The set `P` of matching vectors (§2, p. 126): the vectors satisfying condition (I) (every
component is zero or one) and inequality (2). -/
def matchingVectors (G : Graph V E) : Set (E → ℝ) :=
  {x | (∀ e, x e = 0 ∨ x e = 1) ∧ ∀ v : V, degSum G x v ≤ 1}

/-- The linear form (4) (§2, p. 126): `W = ∑_e c e * x e`. -/
def W (c x : E → ℝ) : ℝ :=
  ∑ e, c e * x e

end EdmondsMatching65.Polyhedron


