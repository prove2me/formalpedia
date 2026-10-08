-- Prove2me | Definitions.Def_SingleMachinePrec_Framework_VertexCoverGraph
-- name    : SingleMachinePrec_Framework_VertexCoverGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T14:06:50.620307+00:00
-- url     : https://prove2.me/theorems/9fed163d-4438-4c8d-9b78-c0d8e44c2738
-- title:
--   §1, §2.2: instances of 1|prec|∑w_jC_j, the vertex cover graph G^S_P, node weights p_i w_j, and OPT
-- statement:
--   An **instance** $S$ of $1|\mathrm{prec}|\sum w_j C_j$ consists of a set $N$ of jobs, a partial order $P$ on $N$ (reflexive, antisymmetric, transitive; $(i,j) \in P$ with $i \ne j$ means that job $i$ must be completed before job $j$ starts), and for each job $j$ a processing time $p_j \ge 0$ and a weight $w_j \ge 0$.
--
--   The **vertex cover graph** $G^S_P$ of Correa and Schulz has one node for each incomparable pair $(i,j)$ of jobs. As printed, two nodes $(i,j)$ and $(k,\ell)$ are adjacent if
--   1. $j = k$ and $i = \ell$, or
--   2. $j = k$ and $(i,\ell) \in P$, or
--   3. $(i,\ell) \in P$ and $(k,j) \in P$.
--
--   These three cases are exactly the constraints (1)–(3) of the integer program [CS-IP]. Since the rule is not symmetric as printed, adjacency is its symmetric closure: two distinct nodes $u, v$ are adjacent when the rule holds for $(u,v)$ or for $(v,u)$. The node $(i,j)$ carries the weight
--   $$w_{(i,j)} = p_i \cdot w_j,$$
--   the processing time of the first job times the weight of the second. The weight of a set $C$ of nodes is $w(C) = \sum_{u \in C} w_u$, and
--   $$\mathrm{OPT} = \min\{w(C) : C \text{ is a vertex cover of } G^S_P\}$$
--   is the minimum weight of a vertex cover (a set of nodes meeting every edge).
--
--   By the results of Correa–Schulz and Ambühl–Mastrolilli (Theorem 2.1 of the paper) $1|\mathrm{prec}|\sum w_jC_j$ is a special case of weighted vertex cover in $G^S_P$; this file fixes that graph.
--
--   **Formalization Note** The graph depends only on $P$ (`vertexCoverGraph P`); weights come from the instance. Processing times and weights are real numbers (the paper says nonnegative integers in §1 but uses rational values later). `OPT` is the minimum of $w$ over the finite, nonempty family of vertex covers that are `Finset`s of nodes (the set of all nodes belongs to it). Mathlib's `SimpleGraph.IsVertexCover` is used for covers.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 653, §1 (the problem); p. 656, §2.2 ([CS-IP] constraints (1)–(3) and the graph G^S_P)

import Mathlib
import Definitions.Def_SingleMachinePrec_Framework_Poset

namespace SingleMachinePrec.Framework

/-- An instance of `1|prec|∑ w_j C_j` (p. 653): a set `N` of jobs (finite wherever it is used),
a partial order `P` on `N` (reflexive, antisymmetric, transitive) giving the precedence
constraints, and nonnegative processing times `p_j` and weights `w_j`. -/
structure Instance (N : Type*) where
  /-- The precedence constraints: `P i j` with `i ≠ j` means job `i` must finish before `j`. -/
  P : N → N → Prop
  isPartialOrder : IsPartialOrder N P
  /-- Processing times. -/
  p : N → ℝ
  /-- Weights. -/
  w : N → ℝ
  p_nonneg : ∀ j, 0 ≤ p j
  w_nonneg : ∀ j, 0 ≤ w j

variable {N : Type*}

/-- The adjacency rule of the vertex cover graph `G^S_P` as printed on p. 656: nodes `(i, j)`
and `(k, ℓ)` are adjacent if `j = k` and `i = ℓ`, or `j = k` and `(i, ℓ) ∈ P`, or
`(i, ℓ) ∈ P` and `(k, j) ∈ P`. (The rule is not symmetric as printed; `vertexCoverGraph` takes
its symmetric closure.) -/
def csRule (P : N → N → Prop) (u v : IncPair P) : Prop :=
  (u.1.2 = v.1.1 ∧ u.1.1 = v.1.2) ∨ (u.1.2 = v.1.1 ∧ P u.1.1 v.1.2) ∨
    (P u.1.1 v.1.2 ∧ P v.1.1 u.1.2)

/-- The vertex cover graph `G^S_P` of Correa and Schulz (§2.2, p. 656): one node for each
incomparable pair `(i, j)`, and two distinct nodes are adjacent when the adjacency rule
`csRule` holds in one of the two orders. Its edges are exactly the constraints (1)–(3) of
[CS-IP]. It depends only on the precedence constraints `P`. -/
def vertexCoverGraph (P : N → N → Prop) : SimpleGraph (IncPair P) where
  Adj u v := u ≠ v ∧ (csRule P u v ∨ csRule P v u)
  symm := ⟨fun _u _v h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _u h => h.1 rfl⟩

/-- The weight `w_{(i,j)} = p_i · w_j` of the node `(i, j)` of `G^S_P` (p. 656): the processing
time of the *first* job times the weight of the *second*. -/
def vertexWeight (S : Instance N) (u : IncPair S.P) : ℝ :=
  S.p u.1.1 * S.w u.1.2

/-- The weight `w(C) = ∑_{u ∈ C} w_u` of a finite set of nodes of `G^S_P`. -/
def weight (S : Instance N) (C : Finset (IncPair S.P)) : ℝ :=
  ∑ u ∈ C, vertexWeight S u

open Classical in
/-- `OPT`: the minimum weight of a vertex cover of `G^S_P` (the minimum is over the finitely many
vertex covers, a family that contains the set of all nodes). -/
noncomputable def OPT [Fintype N] (S : Instance N) : ℝ :=
  (Finset.univ.filter
      (fun C : Finset (IncPair S.P) => (vertexCoverGraph S.P).IsVertexCover (C : Set _))).inf'
    ⟨Finset.univ, by simp [SimpleGraph.isVertexCover_univ]⟩ (weight S)

end SingleMachinePrec.Framework


