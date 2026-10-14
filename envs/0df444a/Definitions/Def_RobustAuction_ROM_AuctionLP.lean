-- Prove2me | Definitions.Def_RobustAuction_ROM_AuctionLP
-- name    : RobustAuction_ROM_AuctionLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T19:32:08.258189+00:00
-- url     : https://prove2.me/theorems/406e3d92-b8b1-4fe5-93f3-5c5b5395a8c5
-- title:
--   §2.2, p. 1017 — constraints (7)–(10) of the robust auction design LP (5): supply, incentive compatibility, budget feasibility, individual rationality
-- statement:
--   This module defines the constraints of the robust auction design problem (5) of Bandi and Bertsimas.
--
--   There are $n$ buyers $\mathcal N=\{1,\dots,n\}$, indexed by $i$, and $m$ items $\mathcal M=\{1,\dots,m\}$, indexed by $j$. A valuation (or bid) vector is an $n\times m$ real matrix $\mathbf v=(v_{ij})$, where $v_{ij}$ is buyer $i$'s value for item $j$. For a buyer $i$ and a row $\mathbf u_i\in\mathbb R^m$, $(\mathbf u_i,\mathbf v_{-i})$ is the matrix $\mathbf v$ with row $i$ replaced by $\mathbf u_i$. The **uncertainty set** $\mathcal U$ is a set of valuation matrices, and $B_1,\dots,B_n$ are the buyers' public budgets. A **mechanism** assigns to every bid vector $\mathbf v$ an allocation $x^{\mathbf v}\in\mathbb R^{n\times m}$ ($x^{\mathbf v}_{ij}$ is the fraction of item $j$ given to buyer $i$) and payments $p^{\mathbf v}\in\mathbb R^n$.
--
--   The module defines one predicate for each family of constraints of (5), each imposed only at bid vectors in $\mathcal U$:
--
--   1. **Supply** (7): $\sum_{i\in\mathcal N} x^{\mathbf v}_{ij}\le 1$ for all $j\in\mathcal M$ and $\mathbf v\in\mathcal U$.
--   2. **Nonnegativity**: $x^{\mathbf v}\ge 0$ for all $\mathbf v\in\mathcal U$.
--   3. **Incentive compatibility** (8): for all $i\in\mathcal N$, all $(\mathbf v_i,\mathbf v_{-i})\in\mathcal U$ and all $(\mathbf u_i,\mathbf v_{-i})\in\mathcal U$,
--   $$\sum_{j\in\mathcal M} v_{ij}\,x^{(\mathbf u_i,\mathbf v_{-i})}_{ij}-p^{(\mathbf u_i,\mathbf v_{-i})}_i-\sum_{j\in\mathcal M} v_{ij}\,x^{(\mathbf v_i,\mathbf v_{-i})}_{ij}+p^{(\mathbf v_i,\mathbf v_{-i})}_i\le 0 .$$
--   4. **Budget feasibility** (9): $p^{\mathbf v}_i\le B_i$ for all $i\in\mathcal N$ and $\mathbf v\in\mathcal U$.
--   5. **Individual rationality** (10): $p^{\mathbf v}_i\le\sum_{j\in\mathcal M} v_{ij}\,x^{\mathbf v}_{ij}$ for all $i\in\mathcal N$ and $\mathbf v\in\mathcal U$.
--
--   A mechanism is **feasible** for (5) when it satisfies all five. Payments may be negative: (5) has no constraint $p\ge 0$. The revenue objective (5)–(6), $\max W$ subject to $W\le\sum_i p^{\mathbf v}_i$ for all $\mathbf v\in\mathcal U$, is not part of this module.
--
--   These are the incentive-compatibility, budget and participation constraints under which the paper designs its robust mechanism, and the statements of the mission are phrased through them.
--
--   **Formalization Note** Buyers are `Fin n` and items `Fin m` (0-based). A valuation matrix is a function `Fin n → Fin m → ℝ`, the uncertainty set an arbitrary `Set` of such matrices, and $(\mathbf u_i,\mathbf v_{-i})$ is `Function.update v i u_i`. Constraint (8) quantifies over the true vector $\mathbf v\in\mathcal U$ and every report $\mathbf u_i$ with $(\mathbf u_i,\mathbf v_{-i})\in\mathcal U$, exactly as the page does. In both utilities the true value $v_{ij}$ multiplies the allocation.
-- source:
--   Bandi, Bertsimas, Optimal Design for Multi-Item Auctions: A Robust Optimization Approach, Math. Oper. Res. 39(4):1012–1038 (2014), p. 1017 (PDF p. 7), §2.2, LP (5), constraints (7)–(10) and x ≥ 0; notation of §1.3 and §2, p. 1015

import Mathlib

namespace RobustAuction.ROM

open Finset

/-!
Constraints (7)–(10) and `x ≥ 0` of the robust auction design LP (5) of Bandi and Bertsimas,
*Optimal Design for Multi-Item Auctions: A Robust Optimization Approach*,
Math. Oper. Res. 39(4) (2014), §2.2, p. 1017.

Buyers are `Fin n`, items are `Fin m`. A valuation (bid) vector is a matrix
`v : Fin n → Fin m → ℝ` with `v i j` the value of buyer `i` for item `j`. The uncertainty set is
`U : Set (Fin n → Fin m → ℝ)`, the (public) budgets are `B : Fin n → ℝ`. A mechanism is an
allocation rule `x : (Fin n → Fin m → ℝ) → Fin n → Fin m → ℝ` (`x v i j` = fraction of item `j`
given to buyer `i` at bid vector `v`) and a payment rule `p : (Fin n → Fin m → ℝ) → Fin n → ℝ`.
The bid vector `(u_i, v_{-i})` is `Function.update v i u_i`. Every constraint is imposed only at
bid vectors in `U`. The objective (5)–(6) is not part of this file.
-/

/-- Constraint (7): at every `v ∈ U`, at most one unit of each item is allocated. -/
def SupplyFeasible {n m : ℕ} (U : Set (Fin n → Fin m → ℝ))
    (x : (Fin n → Fin m → ℝ) → Fin n → Fin m → ℝ) : Prop :=
  ∀ v ∈ U, ∀ j : Fin m, ∑ i, x v i j ≤ 1

/-- Constraint `x^v ≥ 0` of (5), at every `v ∈ U`. -/
def AllocNonneg {n m : ℕ} (U : Set (Fin n → Fin m → ℝ))
    (x : (Fin n → Fin m → ℝ) → Fin n → Fin m → ℝ) : Prop :=
  ∀ v ∈ U, ∀ i j, 0 ≤ x v i j

/-- Constraint (8), incentive compatibility: for every buyer `i`, every `v ∈ U` (the true
valuations) and every report `u_i` of buyer `i` with `(u_i, v_{-i}) ∈ U`,
`∑_j v_ij x_ij^{(u_i,v_{-i})} - p_i^{(u_i,v_{-i})} - ∑_j v_ij x_ij^{v} + p_i^{v} ≤ 0`.
The true valuation `v i j` multiplies both allocations. -/
def IncentiveCompatible {n m : ℕ} (U : Set (Fin n → Fin m → ℝ))
    (x : (Fin n → Fin m → ℝ) → Fin n → Fin m → ℝ) (p : (Fin n → Fin m → ℝ) → Fin n → ℝ) :
    Prop :=
  ∀ v ∈ U, ∀ i : Fin n, ∀ ui : Fin m → ℝ, Function.update v i ui ∈ U →
    ∑ j, v i j * x (Function.update v i ui) i j - p (Function.update v i ui) i
      - ∑ j, v i j * x v i j + p v i ≤ 0

/-- Constraint (9), budget feasibility: `p_i^v ≤ B_i` for every buyer `i` and every `v ∈ U`. -/
def BudgetFeasible {n m : ℕ} (U : Set (Fin n → Fin m → ℝ)) (B : Fin n → ℝ)
    (p : (Fin n → Fin m → ℝ) → Fin n → ℝ) : Prop :=
  ∀ v ∈ U, ∀ i : Fin n, p v i ≤ B i

/-- Constraint (10), individual rationality: `p_i^v ≤ ∑_j v_ij x_ij^v` for every buyer `i` and
every `v ∈ U`. -/
def IndividuallyRational {n m : ℕ} (U : Set (Fin n → Fin m → ℝ))
    (x : (Fin n → Fin m → ℝ) → Fin n → Fin m → ℝ) (p : (Fin n → Fin m → ℝ) → Fin n → ℝ) :
    Prop :=
  ∀ v ∈ U, ∀ i : Fin n, p v i ≤ ∑ j, v i j * x v i j

/-- The pair `(x, p)` satisfies every constraint of the LP (5) other than the revenue
constraints (5)–(6): (7), `x ≥ 0`, (8), (9) and (10). Payments may be negative: (5) has no
constraint `p ≥ 0`. -/
def IsFeasibleMechanism {n m : ℕ} (U : Set (Fin n → Fin m → ℝ)) (B : Fin n → ℝ)
    (x : (Fin n → Fin m → ℝ) → Fin n → Fin m → ℝ) (p : (Fin n → Fin m → ℝ) → Fin n → ℝ) :
    Prop :=
  SupplyFeasible U x ∧ AllocNonneg U x ∧ IncentiveCompatible U x p ∧ BudgetFeasible U B p ∧
    IndividuallyRational U x p

end RobustAuction.ROM


