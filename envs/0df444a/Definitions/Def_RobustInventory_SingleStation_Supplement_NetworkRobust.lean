-- Prove2me | Definitions.Def_RobustInventory_SingleStation_Supplement_NetworkRobust
-- name    : RobustInventory_SingleStation_Supplement_NetworkRobust
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:24:34.428415+00:00
-- url     : https://prove2.me/theorems/4b754c76-0f42-494f-955a-acb34d2b2bb2
-- title:
--   §4.1, formulation (32): the robust problem on a tree network, and the extra cost of Theorem 4.2(b)
-- statement:
--   This file defines the robust formulation (32) of the tree network.
--
--   The variables are the orders $D_i(t)$, epigraph variables $Y_i(t)$ and, for each sink $s$ and period $t$, one pair $q_s(t)$, $(r_s(\tau,t))_{\tau\le t}$ shared by all echelons containing $s$. Write $P_i(t)=\sum_{s\in O(i)}(q_s(t)\Gamma_s(t)+\sum_{\tau\le t}r_s(\tau,t))$. The constraints are the order constraints ($D\ge0$ and the coupling constraint at every installation that is not a sink), $q,r\ge0$, $q_s(t)+r_s(\tau,t)\ge\hat W_s(\tau)$, and
--   $$Y_i(t)\ge h_i(\bar X_i(t+1)+P_i(t)),\qquad Y_i(t)\ge p_i(-\bar X_i(t+1)+P_i(t)).$$
--   The objective is $\sum_{t<T}\sum_{i=1}^{N}[C_i(D_i(t))+Y_i(t)]$, and an optimal solution is a global minimizer. The file also defines the extra cost
--   $$\sum_{k=1}^{N}\frac{2p_kh_k}{p_k+h_k}\sum_{t=0}^{T-1}\sum_{s\in O(k)}A_s(t).$$
--
--   **Formalization Note** The objective runs over all $N$ echelons, each with its supply link. The printed sum $\sum_k\sum_{i\in N(k)}$ leaves out the links from the outside plants, although every echelon has costs and a $Y_i$. The fixed cost is an indicator in place of binary variables and a big $M$.
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), p. 157 (PDF 8), formulation (32); p. 158 (PDF 9), Theorem 4.2(b)

import Definitions.Def_RobustInventory_SingleStation_Supplement_NetworkDynamics

namespace RobustInventory.SingleStation.Supplement.Network

open Finset

variable (G : Network)

/-- `∑_{s ∈ O(k)} (q_s(t) Γ_s(t) + ∑_{τ=0}^{t} r_s(τ, t))`, the protection term of echelon `k`
in (32) and (37). The variables `q s t` and `r s τ t` are shared by all echelons containing `s`. -/
noncomputable def protection (q : Fin G.N → ℕ → ℝ) (r : Fin G.N → ℕ → ℕ → ℝ)
    (k : Fin G.N) (t : ℕ) : ℝ :=
  ∑ s ∈ G.tree.sinksBelow k, (q s t * G.Γ s t + ∑ τ ∈ Finset.range (t + 1), r s τ t)

/-- Feasibility in the robust formulation (32). The binary variables and the big-`M` constraint
are replaced by the fixed-cost indicator in the objective. -/
def RobustFeasible (D Y q : Fin G.N → ℕ → ℝ) (r : Fin G.N → ℕ → ℕ → ℝ) : Prop :=
  G.OrdersFeasible D ∧
    (∀ s, G.tree.IsSink s → ∀ t < G.T,
      0 ≤ q s t ∧ ∀ τ ≤ t, 0 ≤ r s τ t ∧ G.What s τ ≤ q s t + r s τ t) ∧
    ∀ i, ∀ t < G.T,
      G.h i * (G.Xbar D i (t + 1) + G.protection q r i t) ≤ Y i t ∧
      G.p i * (-G.Xbar D i (t + 1) + G.protection q r i t) ≤ Y i t

/-- The objective of (32), `∑_t ∑_i (C_i(D_i(t)) + Y_i(t))`, over all `N` echelons, each with
its supply link, the links from the outside plants included. -/
noncomputable def robustObjective (D Y : Fin G.N → ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range G.T, ∑ i, (G.C i (D i t) + Y i t)

/-- A global minimizer of (32). -/
def IsRobustOptimal (D Y q : Fin G.N → ℕ → ℝ) (r : Fin G.N → ℕ → ℕ → ℝ) : Prop :=
  G.RobustFeasible D Y q r ∧
    ∀ (D' Y' q' : Fin G.N → ℕ → ℝ) (r' : Fin G.N → ℕ → ℕ → ℝ),
      G.RobustFeasible D' Y' q' r' → G.robustObjective D Y ≤ G.robustObjective D' Y'

/-- The extra cost of Theorem 4.2(b):
`∑_k (2 p_k h_k/(p_k + h_k)) ∑_{t<T} ∑_{s ∈ O(k)} A_s(t)`. -/
noncomputable def extraCost : ℝ :=
  ∑ k, 2 * G.p k * G.h k / (G.p k + G.h k) *
    ∑ t ∈ Finset.range G.T, ∑ s ∈ G.tree.sinksBelow k, G.A s t

end RobustInventory.SingleStation.Supplement.Network


