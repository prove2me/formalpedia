-- Prove2me | Definitions.Def_VanderbeiLP_Networks_Network
-- name    : VanderbeiLP_Networks_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T18:31:12.591993+00:00
-- url     : https://prove2.me/theorems/ae6146ab-6195-4c3e-80e4-946ba2c87ffa
-- title:
--   Networks, incidence matrix, feasible flows, spanning trees and bases of Ã
-- statement:
--   This file fixes the vocabulary of Chapter 14.
--
--   A **network** $(N,A)$ consists of a finite set $N$ of $m$ nodes and a set of directed arcs
--   $$A\subseteq\{(i,j): i,j\in N,\ i\neq j\}.$$
--   Each node carries a supply $b_i$ (a negative supply is a demand). The **node–arc incidence matrix** $A$ has one row per node and one column per arc; the column of the arc $(i,j)$ has $+1$ in row $j$ (the head), $-1$ in row $i$ (the tail) and $0$ elsewhere. The network flow problem (14.1) is
--   $$\text{minimize } c^{T}x \quad\text{subject to}\quad Ax=-b,\ x\ge 0,$$
--   that is, $\sum_{i:(i,k)\in A}x_{ik}-\sum_{j:(k,j)\in A}x_{kj}=-b_k$ for every node $k$.
--
--   1. A **balanced flow** is any $x$ satisfying the flow-balance equations $Ax=-b$ (signs unrestricted); a **feasible flow** is a balanced flow with $x_{ij}\ge 0$ on every arc.
--   2. A **path** is a list of nodes in which consecutive nodes are joined by an arc in either direction; the network is **connected** if every two nodes are joined by a path.
--   3. An arc set $T\subseteq A$ is a **spanning tree** if, on the full node set $N$ and ignoring directions, it is connected and contains no cycle. In particular no two arcs of $T$ join the same pair of nodes.
--   4. Fix a **root node** $r$. The matrix $\tilde A$ is $A$ with the row of $r$ deleted. A set $T$ of arcs is a **basis** of $\tilde A$ if its columns form an invertible square submatrix of $\tilde A$: $|T|=m-1$ and the columns are linearly independent.
--   5. A **basic feasible solution** is a feasible flow that vanishes on every arc outside some basis $T\subseteq A$ of $\tilde A$.
--
--   These definitions carry Theorems 14.1 and 14.2.
--
--   **Formalization Note** Arcs are a `Finset (N × N)`, so parallel arcs are impossible, as in the book; `IsNetwork A` excludes loops. Flows are functions on all ordered pairs, and only their values on $A$ enter any definition. "Connected" is `Preconnected` of the undirected simple graph of the arcs. "Invertible square submatrix" is written as "$m-1$ linearly independent columns of the $(m-1)$-row matrix $\tilde A$", which is the same condition and does not depend on how the columns are ordered.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, pp. 199–205 (PDF 210–216): network and (14.1) p. 199–201, paths/connected/tree/spanning tree p. 202, balanced/feasible flow and tree solution p. 203, basis and Ã p. 204–205

import Mathlib

namespace VanderbeiLP.Networks

open Finset

/-- **Network** (Vanderbei, *Linear Programming*, 4th ed., p. 199). A network `(N, A)` has a
finite node set `N` and an arc set `A ⊆ {(i, j) : i, j ∈ N, i ≠ j}` of ordered pairs; this
predicate records that `A` contains no arc of the form `(i, i)`. -/
def IsNetwork {N : Type*} (A : Finset (N × N)) : Prop :=
  ∀ a ∈ A, a.1 ≠ a.2

/-- **Node–arc incidence matrix** (p. 201–202, problem (14.1)). The column of an arc `(i, j)` has
`+1` in the row of its head `j`, `-1` in the row of its tail `i`, and `0` elsewhere, so that
`(A x)_k = ∑_{(i,k) ∈ A} x_{ik} − ∑_{(k,j) ∈ A} x_{kj}` (inflow minus outflow). Columns are
indexed by all ordered pairs; a network uses the columns of its arcs. -/
def incidence {N : Type*} [DecidableEq N] : Matrix N (N × N) ℝ :=
  fun k a => if k = a.2 then 1 else if k = a.1 then -1 else 0

/-- **Balanced flow** (p. 203): flows `x_{ij}`, `(i, j) ∈ A`, satisfying the flow-balance
equations `Ax = -b` of (14.1) at every node, i.e.
`∑_{i:(i,k) ∈ A} x_{ik} - ∑_{j:(k,j) ∈ A} x_{kj} = -b_k` for all `k ∈ N`. Signs are not
restricted; values of `x` off `A` play no role. -/
def IsBalancedFlow {N : Type*} [DecidableEq N] (A : Finset (N × N)) (b : N → ℝ)
    (x : N × N → ℝ) : Prop :=
  ∀ k : N, ∑ a ∈ A, incidence k a * x a = -b k

/-- **Feasible flow** (p. 203): a balanced flow with `x_{ij} ≥ 0` on every arc. -/
def IsFeasibleFlow {N : Type*} [DecidableEq N] (A : Finset (N × N)) (b : N → ℝ)
    (x : N × N → ℝ) : Prop :=
  IsBalancedFlow A b x ∧ ∀ a ∈ A, 0 ≤ x a

/-- The undirected graph underlying a set of arcs: nodes `i ≠ j` are adjacent when `(i, j)` or
`(j, i)` is an arc. Paths in the network ignore arc directions (p. 202). -/
def arcGraph {N : Type*} (T : Finset (N × N)) : SimpleGraph N :=
  SimpleGraph.fromEdgeSet ((fun a : N × N => s(a.1, a.2)) '' (T : Set (N × N)))

/-- **Connected network** (p. 202): every pair of nodes is joined by a path, arcs being
traversed in either direction. -/
def IsConnectedNetwork {N : Type*} (A : Finset (N × N)) : Prop :=
  (arcGraph A).Preconnected

/-- **Spanning tree** (p. 202): an arc set `T ⊆ A` which, on the full node set `N`, is connected
and acyclic (arcs taken without direction). Acyclicity of the arc set also forbids two arcs
joining the same pair of nodes (`(i, j)` and `(j, i)` together form a cycle), which is the
injectivity clause. -/
def IsSpanningTree {N : Type*} (A T : Finset (N × N)) : Prop :=
  T ⊆ A ∧ (arcGraph T).IsTree ∧
    Set.InjOn (fun a : N × N => s(a.1, a.2)) (T : Set (N × N))

/-- **Truncated incidence matrix `Ã`** (p. 205): the incidence matrix with the row of the root
node `r` deleted. -/
def truncIncidence {N : Type*} [DecidableEq N] (r : N) :
    Matrix {k : N // k ≠ r} (N × N) ℝ :=
  fun k a => incidence k.1 a

/-- **Basis of `Ã`** (pp. 204–205): the columns of `Ã` for the arcs in `T` form an invertible
square submatrix, i.e. there are exactly as many of them as rows of `Ã` (`|T| = m - 1`) and they
are linearly independent. -/
def IsBasisArcs {N : Type*} [Fintype N] [DecidableEq N] (r : N) (T : Finset (N × N)) : Prop :=
  T.card = Fintype.card {k : N // k ≠ r} ∧
    LinearIndependent ℝ (fun a : T => fun k : {k : N // k ≠ r} => truncIncidence r k a.1)

/-- **Basic feasible solution** of the network flow problem (14.1) with root `r`
(pp. 203–205, 215–216): a feasible flow that vanishes on every arc outside some basis `T ⊆ A`
of `Ã`. -/
def IsBasicFeasibleFlow {N : Type*} [Fintype N] [DecidableEq N] (A : Finset (N × N))
    (b : N → ℝ) (r : N) (x : N × N → ℝ) : Prop :=
  IsFeasibleFlow A b x ∧
    ∃ T : Finset (N × N), T ⊆ A ∧ IsBasisArcs r T ∧ ∀ a ∈ A, a ∉ T → x a = 0

end VanderbeiLP.Networks


