-- Prove2me | Definitions.Def_RobustInventory_SingleStation_Supplement_InventoryCap
-- name    : RobustInventory_SingleStation_Supplement_InventoryCap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:22:49.873361+00:00
-- url     : https://prove2.me/theorems/02536016-4721-4454-ba8a-7536cd010c27
-- title:
--   §3.2.2, (25)–(27): the robust and the modified nominal problems with inventory capacity
-- statement:
--   This file adds an inventory capacity to the published single-station problems. Stock can only be stored up to $\mathrm{Cap}$ (the paper's $C$ of §3.2.2).
--
--   1. The **capacitated robust problem** is formulation (14), with orders $u$, epigraph variables $y$ and dual variables $q,r$, plus constraint (26) on the same $q$ and $r$:
--   $$\bar x_{k+1}+q_k\Gamma_k+\sum_{i=0}^{k}r_{ik}\le\mathrm{Cap}\qquad(k<T),$$
--   where $\bar x_{k+1}=x_0+\sum_{i=0}^{k}(u_i-\bar w_i)$. Its objective is that of (14).
--   2. Let $A_k$ be the value of LP (13), $w'$ the modified demand (20) and $x'_{k+1}=x_0+\sum_{i=0}^{k}(u_i-w'_i)$. The **capacitated modified nominal problem** minimizes $\sum_{k<T}[C(u_k)+R(x'_{k+1})]$ over $u_k\ge0$ subject to
--   $$x_0\le\mathrm{Cap},\qquad x'_{k+1}\le\mathrm{Cap}-\frac{2p}{p+h}A_k\quad(k<T).$$
--
--   In both problems an optimal solution is a global minimizer over the feasible set. Theorem 3.5 identifies their optimal order sequences.
--
--   **Formalization Note** The capacity is called `Cap` because `Model.C` is the purchasing cost. The definitions do not assume that either problem is feasible.
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), p. 156 (PDF 7), §3.2.2, Eqs. (25)–(27)

import Definitions.Def_RobustInventory_SingleStation_Deviation
import Definitions.Def_RobustInventory_SingleStation_Robust

namespace RobustInventory.SingleStation.Supplement

open Finset

/-- Feasibility in (14) with the inventory capacity constraint (26):
`x̄_{k+1} + q_k Γ_k + ∑_{i=0}^{k} r_ik ≤ Cap` for `k < T`, on the same `q`, `r` as in (14).
`Cap` is the paper's capacity `C` of §3.2.2 (`Model.C` is the ordering cost). -/
def RobustCapFeasible (M : Model) (Cap : ℝ) (u y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ) : Prop :=
  M.RobustFeasible u y q r ∧
    ∀ k < M.T, M.xbar u k + q k * M.Γ k + ∑ i ∈ Finset.range (k + 1), r i k ≤ Cap

/-- A global minimizer of (14) with (26). -/
def IsRobustCapOptimal (M : Model) (Cap : ℝ) (u y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ) : Prop :=
  RobustCapFeasible M Cap u y q r ∧
    ∀ (u' y' q' : ℕ → ℝ) (r' : ℕ → ℕ → ℝ),
      RobustCapFeasible M Cap u' y' q' r' → M.robustObjective u y ≤ M.robustObjective u' y'

/-- The inventory capacity `Cap - (2p/(p + h)) A_k` at time `k + 1` of Theorem 3.5, as in (27). -/
noncomputable def modifiedCap (M : Model) (Cap : ℝ) (k : ℕ) : ℝ :=
  Cap - 2 * M.p / (M.p + M.h) * M.A k

/-- Feasibility in the nominal problem of Theorem 3.5: nonnegative orders, capacity `Cap` at
time `0`, and capacity `modifiedCap` at time `k + 1` on the modified stock `x'_{k+1}`. -/
def NominalCapFeasible (M : Model) (Cap : ℝ) (u : ℕ → ℝ) : Prop :=
  (∀ k < M.T, 0 ≤ u k) ∧ M.x0 ≤ Cap ∧
    ∀ k < M.T, M.stock M.wmod u k ≤ modifiedCap M Cap k

/-- A global minimizer of the nominal problem of Theorem 3.5, with the modified demand `w'`. -/
def IsNominalCapOptimal (M : Model) (Cap : ℝ) (u : ℕ → ℝ) : Prop :=
  NominalCapFeasible M Cap u ∧
    ∀ u', NominalCapFeasible M Cap u' → M.nominalCost M.wmod u ≤ M.nominalCost M.wmod u'

end RobustInventory.SingleStation.Supplement


