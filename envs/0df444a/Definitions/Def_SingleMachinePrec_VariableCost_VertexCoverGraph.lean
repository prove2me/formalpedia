-- Prove2me | Definitions.Def_SingleMachinePrec_VariableCost_VertexCoverGraph
-- name    : SingleMachinePrec_VariableCost_VertexCoverGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T13:46:01.181377+00:00
-- url     : https://prove2.me/theorems/54896243-8a15-4e97-95e1-69ac63181899
-- title:
--   Instances of $1|\mathrm{prec}|\sum w_jC_j$, incomparable pairs, the vertex cover graph $G^S_{\mathbf P}$ and its weights
-- statement:
--   An instance $S$ of the single-machine scheduling problem $1|\mathrm{prec}|\sum w_jC_j$ consists of a finite set $N$ of jobs, a partial order $\mathbf P = (N, P)$ on $N$ (reflexive, antisymmetric and transitive; $(i,j) \in P$ with $i \neq j$ means that job $i$ must be processed before job $j$), and nonnegative processing times $p_j$ and weights $w_j$ for $j \in N$.
--
--   Two jobs $x, y$ are **incomparable**, written $x \parallel y$, when neither $(x,y) \in P$ nor $(y,x) \in P$. The set of incomparable pairs is
--   $$
--   \operatorname{inc}(\mathbf P) = \{(x,y) \in N \times N : x \parallel y\};
--   $$
--   its elements are *ordered* pairs, and $(x,y) \in \operatorname{inc}(\mathbf P)$ if and only if $(y,x) \in \operatorname{inc}(\mathbf P)$.
--
--   The **vertex cover graph** $G^S_{\mathbf P}$ of Correa and Schulz has one node for each incomparable pair $(i,j)$, with weight
--   $$
--   w_{(i,j)} = p_i\, w_j .
--   $$
--   Two distinct nodes $(i,j)$ and $(k,\ell)$ are adjacent when, in one of the two orders, either $j = k$ and $i = \ell$; or $j = k$ and $(i,\ell) \in P$; or $(i,\ell) \in P$ and $(k,j) \in P$. These three cases are exactly the constraints (1)–(3) of the integer program [CS-IP].
--
--   For a set $C$ of nodes, $w(C) = \sum_{u \in C} w_u$. When $C$ is a vertex cover of $G^S_{\mathbf P}$, $w(C)$ is the **variable cost** of the corresponding solution of [CS-IP]: the objective of [CS-IP] without its fixed part $\sum_{j} p_j w_j + \sum_{(i,j) \in P} p_i w_j$, which is the same for every feasible solution. Finally, $\tau_w(G^S_{\mathbf P})$ denotes the minimum of $w(C)$ over all vertex covers $C$ of $G^S_{\mathbf P}$, the optimal variable cost.
--
--   These objects carry every statement of the mission: the reduction of §8 is a statement about vertex covers of $G^S_{\mathbf P}$ and their weights.
--
--   **Formalization Note** The precedence constraints are an explicit relation `P : N → N → Prop` with `IsPartialOrder`, not a `PartialOrder` instance, because the instance of §8 builds its order from a graph. The printed adjacency rule is not symmetric, so the graph takes its symmetric closure and excludes loops. The minimum `minCoverWeight` is a minimum over the finitely many finite sets of nodes that are vertex covers (the set of all nodes is one), so it is attained.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 653 (§1, the problem), p. 655 (§2.1, inc(P)), p. 656 (§2.2, [CS-IP] and G^S_P)

import Mathlib

namespace SingleMachinePrec.VariableCost

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

/-- Two jobs `x, y` are incomparable in `P` (written `x ∥ y` on p. 655) when neither
`(x, y) ∈ P` nor `(y, x) ∈ P`. -/
def Incomparable (P : N → N → Prop) (x y : N) : Prop :=
  ¬ P x y ∧ ¬ P y x

/-- `inc(P)`: the set of *ordered* incomparable pairs `(x, y) ∈ N × N` with `x ∥ y` (p. 655),
as a type. These are the vertices of `G^S_P`. -/
def IncPair (P : N → N → Prop) : Type _ :=
  {u : N × N // Incomparable P u.1 u.2}

noncomputable instance IncPair.instFintype [Fintype N] (P : N → N → Prop) :
    Fintype (IncPair P) := by
  classical
  exact Subtype.fintype _

instance IncPair.instDecidableEq [DecidableEq N] (P : N → N → Prop) :
    DecidableEq (IncPair P) :=
  inferInstanceAs (DecidableEq {u : N × N // Incomparable P u.1 u.2})

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
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The weight `w_{(i,j)} = p_i · w_j` of the node `(i, j)` of `G^S_P` (p. 656): the processing
time of the *first* job times the weight of the *second*. -/
def vertexWeight (S : Instance N) (u : IncPair S.P) : ℝ :=
  S.p u.1.1 * S.w u.1.2

/-- The weight `w(C) = ∑_{u ∈ C} w_u` of a finite set of nodes of `G^S_P`. For a vertex cover
`C` of `G^S_P` this is the *variable cost* of the corresponding solution of [CS-IP] (the
objective of [CS-IP] without its fixed part `∑_j p_j w_j + ∑_{(i,j) ∈ P} p_i w_j`). -/
def weight (S : Instance N) (C : Finset (IncPair S.P)) : ℝ :=
  ∑ u ∈ C, vertexWeight S u

open Classical in
/-- The minimum weight of a vertex cover of `G^S_P`, i.e. the optimal variable cost of `S`
(the minimum is over the finitely many vertex covers, a family that contains the set of all
nodes, so it is attained). -/
noncomputable def minCoverWeight [Fintype N] (S : Instance N) : ℝ :=
  (Finset.univ.filter
      (fun C : Finset (IncPair S.P) => (vertexCoverGraph S.P).IsVertexCover (C : Set _))).inf'
    ⟨Finset.univ, by simp [SimpleGraph.isVertexCover_univ]⟩ (weight S)

end SingleMachinePrec.VariableCost


