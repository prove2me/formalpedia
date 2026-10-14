-- Prove2me | Definitions.Def_Micromobility_Transient_TransshipLP
-- name    : Micromobility_Transient_TransshipLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:08:03.662213+00:00
-- url     : https://prove2.me/theorems/38e8b4bd-1eea-4516-ad2b-b56000e3c6b6
-- title:
--   The uncapacitated transshipment LP on a complete digraph with free nodes (the flow component of (F.6))
-- statement:
--   This file defines a general linear program: the uncapacitated transshipment problem on the complete directed graph of a finite node set $I$.
--
--   Let $I$ be a finite set of nodes, with every ordered pair $(i, j)$, $i \ne j$, an arc of cost $\kappa_{i,j} \in \mathbb R$. A family of **balance nodes** $\nu(k)$, $k \in K$, carries required net outflows $b_k \in \mathbb R$; every node outside $\{\nu(k)\}$ is **free** and may absorb or supply any amount. A flow $y = (y^{i,j})_{i,j \in I}$ is **feasible** if
--
--   1. $y^{i,j} \ge 0$ for all $i, j \in I$, and
--   2. $\sum_{j \in I} \big(y^{\nu(k), j} - y^{j, \nu(k)}\big) = b_k$ for every $k \in K$.
--
--   Its cost is $\sum_{i \in I}\sum_{j \ne i} \kappa_{i,j}\, y^{i,j}$, and the optimal value of the LP is
--
--   $$\Phi(\kappa, \nu, b) = \inf\Big\{\sum_{i}\sum_{j \ne i} \kappa_{i,j}\, y^{i,j} \;:\; y \text{ feasible}\Big\}.$$
--
--   In the micromobility model the nodes are the warehouse, the charged types and the depleted stocks; the warehouse is the free node, and $\Phi$ is the min-cost-flow component of the rebalancing cost $\hat c_2$ in (F.6).
--
--   **Formalization Note.** The value is a real `sInf`. It is the LP's optimal value when the feasible set is nonempty and the objective is bounded below on it (for instance when $\kappa \ge 0$); on an empty or unbounded-below feasible set Lean returns $0$. Statements built on it supply those conditions (in this mission: a free node exists, so every imbalance can be routed through it, and the arc costs are nonnegative under the standing cost assumption).
-- source:
--   Akturk, Candogan, Gupta, Managing Resources for Shared Micromobility: Approximate Optimality in Large-Scale Systems, SSRN 4155841 (version of 2024-05-22), pp. A-24–A-25, (F.6) (the flow LP), written for a general node set

import Mathlib

namespace Micromobility.Transient

open Finset

/-! # The uncapacitated transshipment LP on a complete digraph

Nodes are a finite type `ι`; every ordered pair `(i, j)` with `i ≠ j` is an arc. A family of
*balance nodes* `node : κ → ι` carries required net outflows `b : κ → ℝ`; every other node is
free (it can absorb or supply any amount). -/

/-- `y` is a feasible flow: `y i j ≥ 0` for all `i, j`, and at every balance node `node k` the net
outflow `Σ_j (y (node k) j - y j (node k))` equals `b k`. Nodes outside the range of `node` carry
no constraint. -/
def TransshipFeasible {ι κ : Type*} [Fintype ι] (node : κ → ι) (b : κ → ℝ)
    (y : ι → ι → ℝ) : Prop :=
  (∀ i j, 0 ≤ y i j) ∧ ∀ k, ∑ j, (y (node k) j - y j (node k)) = b k

/-- The cost `Σ_i Σ_{j ≠ i} cost i j * y i j` of a flow (self-loops `i = i` carry no cost). -/
noncomputable def transshipCost {ι : Type*} [Fintype ι] [DecidableEq ι] (cost : ι → ι → ℝ)
    (y : ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ univ.erase i, cost i j * y i j

/-- The optimal value of the transshipment LP: the infimum of `transshipCost cost y` over the
feasible flows `y`. (A real `sInf`; it is the LP's optimal value whenever the feasible set is
nonempty and the costs make the objective bounded below, e.g. `cost ≥ 0`.) -/
noncomputable def transshipValue {ι κ : Type*} [Fintype ι] [DecidableEq ι] (cost : ι → ι → ℝ)
    (node : κ → ι) (b : κ → ℝ) : ℝ :=
  sInf {v : ℝ | ∃ y, TransshipFeasible node b y ∧ v = transshipCost cost y}

end Micromobility.Transient


