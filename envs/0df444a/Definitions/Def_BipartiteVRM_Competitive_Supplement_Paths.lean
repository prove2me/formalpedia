-- Prove2me | Definitions.Def_BipartiteVRM_Competitive_Supplement_Paths
-- name    : BipartiteVRM_Competitive_Supplement_Paths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:27:50.032861+00:00
-- url     : https://prove2.me/theorems/6174680c-f4b2-44f7-a3a1-3f974b671d0d
-- title:
--   Matchings, alternating paths and cycles, γ-net-cost, the graphs $G_{uv}$
-- statement:
--   Requests are natural labels and an edge is an unordered pair $\{u,v\}$ of distinct labels, stored as $(\min,\max)$. A **matching** is a set of such edges with pairwise disjoint endpoints; a vertex is **saturated** by $M$ if some edge of $M$ contains it. For an edge-length function $D$, a real $\gamma$, a matching $M$ and an edge set $F$, the **γ-net-cost** is
--
--   $$\varphi_M(F)=\gamma D(F\setminus M)-D(F\cap M),$$
--
--   a signed real, and the **switching cost** of an edge is $c_L(e)=-D(e)$ if $e\in L$ and $c_L(e)=\gamma D(e)$ otherwise. For distinct $M$-unsaturated $u,v$, $G_{uv}$ is the complete graph on $U\cup\{u,v\}$, $U$ the set saturated by $M$, with weights $w_M(e)=D(e)$ for $e\in M$ and $w_M(e)=\gamma D(e)$ otherwise; its perfect matchings and its minimum-weight perfect matchings are enumerated exactly (a finite set).
--
--   An **$M$-augmenting path** from $u$ to $v$ on a vertex set $A$ is a list of distinct vertices of $A$, from $u$ to $v\ne u$, both unsaturated, whose consecutive edges alternate, the first outside $M$. A **simple $M$-alternating even cycle** is a list of at least four distinct vertices, of even length, whose closed walk has consecutive edges alternating between $M$ and its complement. The **component** of an edge set $F$ containing $u$ is the set of edges of $F$ reachable from $u$.
--
--   These objects carry no minimality, no cycle-sign and no matching invariant: those are theorems.
--
--   **Formalization Note** Edges, endpoints and complete-graph edge sets are those of the published `MatchingDelays_Linear_Instance`. The component is computed by $|F|+1$ breadth-first rounds, which reach the whole component.
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), pp. 14–16, §5.1 (definition of φ_M), §5.2 (G_uv, w_M, Steps 1–2), p. 16 (c_L)

import Definitions.Def_MatchingDelays_Linear_Instance

set_option autoImplicit false

namespace BipartiteVRM.Competitive.Supplement

open Classical
open MatchingDelays.Linear (Edge edge endpoints allPairs)

/-! Kuo, STOC 2027 submission #528 (October 2026), §5.1–§5.2, pp. 14–16.
Requests are natural labels; an unordered edge is the normalized pair `edge u v`.
Paths and cycles are ordered vertex lists; their edge sets forget orientation.
No nonnegativity of cycles, no minimality and no matching invariant is bundled here. -/

abbrev Matching := Finset Edge

/-- The vertices covered by an edge set. -/
def covered (M : Matching) : Finset ℕ := M.biUnion endpoints

def saturated (M : Matching) (v : ℕ) : Prop := v ∈ covered M

/-- A matching of the complete graph on the labels: normalized edges between distinct
labels with pairwise disjoint endpoints. -/
def IsMatching (M : Matching) : Prop :=
  (∀ e ∈ M, e.1 < e.2) ∧ ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint (endpoints e) (endpoints f)

/-- `N` is a perfect matching of the complete graph on the vertex set `V`. -/
def IsPerfectOn (V : Finset ℕ) (N : Matching) : Prop :=
  N ⊆ allPairs V ∧ ∀ x ∈ V, ∃! e, e ∈ N ∧ x ∈ endpoints e

/-- Symmetric difference `A △ B`. -/
def symmD (A B : Matching) : Matching := (A \ B) ∪ (B \ A)

/-- The γ-net-cost φ_M(F) = γ D(F \ M) − D(F ∩ M) of an edge set `F`; a signed real. -/
noncomputable def netCost (D : Edge → ℝ) (γ : ℝ) (M F : Matching) : ℝ :=
  γ * (∑ e ∈ F \ M, D e) - ∑ e ∈ F ∩ M, D e

/-- The edge switching cost c_L(e): −D(e) if e ∈ L, γ D(e) otherwise (p. 16). -/
noncomputable def switchCost (D : Edge → ℝ) (γ : ℝ) (L : Matching) (e : Edge) : ℝ :=
  if e ∈ L then -D e else γ * D e

/-- The weight w_M(N) of an edge set: D(e) on edges of M, γ D(e) on other edges (p. 15). -/
noncomputable def weight (D : Edge → ℝ) (γ : ℝ) (M N : Matching) : ℝ :=
  ∑ e ∈ N, if e ∈ M then D e else γ * D e

/-- The vertex set U ∪ {u, v} of G_uv, where U is the set saturated by M. -/
def pairVertices (M : Matching) (u v : ℕ) : Finset ℕ := insert u (insert v (covered M))

/-- All perfect matchings of the complete graph on V (a finite set). -/
noncomputable def perfectMatchings (V : Finset ℕ) : Finset Matching :=
  (allPairs V).powerset.filter (IsPerfectOn V)

/-- All minimum-weight perfect matchings of G_uv under w_M. -/
noncomputable def minWeightPerfect (D : Edge → ℝ) (γ : ℝ) (M : Matching) (u v : ℕ) :
    Finset Matching :=
  let ps := perfectMatchings (pairVertices M u v)
  ps.filter (fun N => ∀ N' ∈ ps, weight D γ M N ≤ weight D γ M N')

def IsMinWeightPerfect (D : Edge → ℝ) (γ : ℝ) (M : Matching) (u v : ℕ) (N : Matching) :
    Prop :=
  IsPerfectOn (pairVertices M u v) N ∧
    ∀ N', IsPerfectOn (pairVertices M u v) N' → weight D γ M N ≤ weight D γ M N'

/-- One breadth-first step: add every endpoint of an edge of F touching S. -/
noncomputable def reachStep (F : Matching) (S : Finset ℕ) : Finset ℕ :=
  S ∪ (F.filter (fun e => ∃ x ∈ endpoints e, x ∈ S)).biUnion endpoints

noncomputable def reach (F : Matching) (u : ℕ) : ℕ → Finset ℕ
  | 0 => {u}
  | k + 1 => reachStep F (reach F u k)

/-- The edges of the connected component of the edge set F containing u. F.card + 1
breadth-first rounds reach the whole component, so the bound does not truncate it. -/
noncomputable def component (F : Matching) (u : ℕ) : Matching :=
  F.filter (fun e => ∃ x ∈ endpoints e, x ∈ reach F u (F.card + 1))

/-- The (unordered) edges of a vertex list. -/
def pathEdges (P : List ℕ) : Matching :=
  ((P.zip P.tail).map (fun uv => edge uv.1 uv.2)).toFinset

/-- Consecutive edges alternate, the first edge (index 0) lying outside M. -/
def Alternating (M : Matching) (P : List ℕ) : Prop :=
  ∀ i (h : i + 1 < P.length),
    (edge (P[i]'(Nat.lt_of_succ_lt h)) (P[i + 1]'h) ∈ M ↔ i % 2 = 1)

/-- A simple M-augmenting path from u to v on the vertex set A: a simple alternating
path between two distinct M-unsaturated vertices of A. -/
def IsAugmenting (A : Finset ℕ) (M : Matching) (u v : ℕ) (P : List ℕ) : Prop :=
  P.Nodup ∧ 2 ≤ P.length ∧ P.head? = some u ∧ P.getLast? = some v ∧
    (∀ x ∈ P, x ∈ A) ∧ ¬ saturated M u ∧ ¬ saturated M v ∧ Alternating M P

/-- The edge set of the closed walk through the vertices of C in order. -/
def cycleEdges (C : List ℕ) : Matching := pathEdges (C ++ C.take 1)

/-- A simple M-alternating even cycle: at least four distinct vertices, an even number of
them, and consecutive edges of the closed walk alternate between M and its complement. -/
def AlternatingEvenCycle (M : Matching) (C : List ℕ) : Prop :=
  C.Nodup ∧ 4 ≤ C.length ∧ Even C.length ∧
    let L := C ++ C.take 1
    ∀ i (h : i + 2 < L.length),
      (edge (L[i]'(by omega)) (L[i + 1]'(by omega)) ∈ M ↔
        edge (L[i + 1]'(by omega)) (L[i + 2]'h) ∉ M)

end BipartiteVRM.Competitive.Supplement


