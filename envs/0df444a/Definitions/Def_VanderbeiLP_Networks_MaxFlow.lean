-- Prove2me | Definitions.Def_VanderbeiLP_Networks_MaxFlow
-- name    : VanderbeiLP_Networks_MaxFlow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T18:42:35.344998+00:00
-- url     : https://prove2.me/theorems/c817b367-96e8-4c5b-9fba-7ce0638176ad
-- title:
--   Maximum-flow problem: feasible flows, cuts and cut capacity
-- statement:
--   Let $(N,A)$ be a network with a **source** node $s$, a **sink** node $t$ and finite upper bounds $u_{ij}$ on the arcs $(i,j)\in A$. The maximum-flow problem is written as an upper-bounded network flow problem: all costs on original arcs are $0$, all supplies $b_i=0$, and one extra arc $(t,s)$ is added with cost $c_{ts}=-1$ and infinite capacity.
--
--   1. A **feasible flow** is a choice of $x_{ij}$ for $(i,j)\in A$ and $x_{ts}$ on the extra arc with
--   $$0\le x_{ij}\le u_{ij}\quad((i,j)\in A),\qquad x_{ts}\ge 0,$$
--   and flow balance (inflow equals outflow) at every node, the extra arc leaving $t$ and entering $s$.
--   2. A **cut** is a set $C$ of nodes with $s\in C$ and $t\notin C$.
--   3. The **capacity** of a cut is
--   $$\kappa(C)=\sum_{\substack{(i,j)\in A\\ i\in C,\ j\notin C}}u_{ij},$$
--   the sum running over original arcs only.
--
--   These are the objects of the Max-Flow Min-Cut Theorem 15.1.
--
--   **Formalization Note** The extra arc $(t,s)$ is represented by a separate real variable `xts` rather than by an element of `A`, so it is never counted in $\kappa(C)$ and never clashes with an original arc $(t,s)$. The file imports the network definitions for `IsNetwork`.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 231 (PDF 242) upper bounds 0 ≤ x_ij ≤ u_ij; pp. 233–234 (PDF 244–245), setting of §15.5 and definition of κ(C)

import Mathlib
import Definitions.Def_VanderbeiLP_Networks_Network

namespace VanderbeiLP.Networks

open Finset

/-- **Feasible flow of the maximum-flow problem** (Vanderbei, p. 233). The network `(N, A)` with
source `s`, sink `t` and finite upper bounds `u_{ij}` is turned into an upper-bounded network flow
problem with all `b_i = 0` and one extra arc `(t, s)` of infinite capacity. A feasible flow is a
choice of `x_{ij}` on the original arcs and `x_{ts}` on the extra arc with
`0 ≤ x_{ij} ≤ u_{ij}`, `x_{ts} ≥ 0`, and flow balance (inflow = outflow) at every node, the
extra arc `(t, s)` leaving `t` and entering `s`. -/
def IsMaxFlowFeasible {N : Type*} [DecidableEq N] (A : Finset (N × N)) (u : N × N → ℝ) (s t : N)
    (x : N × N → ℝ) (xts : ℝ) : Prop :=
  (∀ a ∈ A, 0 ≤ x a ∧ x a ≤ u a) ∧ 0 ≤ xts ∧
    ∀ k : N,
      (∑ a ∈ A.filter (fun a => a.2 = k), x a) + (if k = s then xts else 0) -
        ((∑ a ∈ A.filter (fun a => a.1 = k), x a) + (if k = t then xts else 0)) = 0

/-- **Cut** (p. 233): a set `C` of nodes containing the source `s` but not the sink `t`. -/
def IsCut {N : Type*} (s t : N) (C : Finset N) : Prop :=
  s ∈ C ∧ t ∉ C

/-- **Capacity of a cut** (p. 234): `κ(C) = ∑_{i ∈ C, j ∉ C} u_{ij}`, the sum running over the
original arcs `(i, j) ∈ A` only (the extra arc `(t, s)` is excluded). -/
def cutCapacity {N : Type*} [DecidableEq N] (A : Finset (N × N)) (u : N × N → ℝ)
    (C : Finset N) : ℝ :=
  ∑ a ∈ A.filter (fun a => a.1 ∈ C ∧ a.2 ∉ C), u a

end VanderbeiLP.Networks


