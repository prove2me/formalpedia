-- Prove2me | Definitions.Def_RobustInventory_SingleStation_Supplement_NetworkCap
-- name    : RobustInventory_SingleStation_Supplement_NetworkCap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:25:37.595478+00:00
-- url     : https://prove2.me/theorems/10bdc366-8533-48f4-8516-fa7cbb52b05d
-- title:
--   §4.2, (36)–(37): link and echelon capacities in the robust and modified networks
-- statement:
--   This file adds capacities to the tree network.
--
--   Each installation $i$ has a bound $d_i\in\mathbb R\cup\{+\infty\}$ on its supply link (the paper's $d_{ki}$ for $i\in N(k)$), and each echelon $k$ a capacity $C_k$.
--
--   1. The **capacitated robust problem** is (32) with $D_i(t)\le d_i$ (36) and, for every echelon $k$ and period $t<T$, constraint (37) on the same $q,r$:
--   $$\bar X_k(t+1)+\sum_{s\in O(k)}\Big(q_s(t)\Gamma_s(t)+\sum_{\tau=0}^{t}r_s(\tau,t)\Big)\le C_k .$$
--   2. The **capacitated modified supply chain** minimizes the cost under the demands (34) over feasible orders with the same link bounds and
--   $$X'_k(t+1)\le C'_k(t+1)=C_k-\frac{2p_k}{p_k+h_k}\sum_{s\in O(k)}A_s(t).$$
--
--   Both optimality notions are global minimization over the feasible set; Theorem 4.3 relates them.
--
--   **Formalization Note** A link bound may be $+\infty$. With $+\infty$ on every plant link this is (36) as printed, which bounds only the links between installations.
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), p. 159 (PDF 10), §4.2, Eqs. (36)–(37) and Theorem 4.3

import Definitions.Def_RobustInventory_SingleStation_Supplement_NetworkRobust

namespace RobustInventory.SingleStation.Supplement.Network

open Finset

variable (G : Network)

/-- The link capacities (36): `D_i(t) ≤ d_i`, where `d i` bounds the link from the only supplier
of `i` to `i` (the paper's `d_ki` for `i ∈ N(k)`); `d i = ⊤` means that this link has no bound. -/
def LinkCap (d : Fin G.N → WithTop ℝ) (D : Fin G.N → ℕ → ℝ) : Prop :=
  ∀ i, ∀ t < G.T, (D i t : WithTop ℝ) ≤ d i

/-- Feasibility in (32) with the link capacities (36) and, for every echelon `k` and period `t`,
the echelon capacity (37) `X̄_k(t+1) + ∑_{s ∈ O(k)} (q_s(t) Γ_s(t) + ∑_τ r_s(τ,t)) ≤ C_k`,
on the same `q`, `r` as in (32). `Cap k` is the paper's capacity `C_k`. -/
def RobustCapFeasible (d : Fin G.N → WithTop ℝ) (Cap : Fin G.N → ℝ)
    (D Y q : Fin G.N → ℕ → ℝ) (r : Fin G.N → ℕ → ℕ → ℝ) : Prop :=
  G.RobustFeasible D Y q r ∧ G.LinkCap d D ∧
    ∀ k, ∀ t < G.T, G.Xbar D k (t + 1) + G.protection q r k t ≤ Cap k

/-- A global minimizer of (32) with (36) and (37). -/
def IsRobustCapOptimal (d : Fin G.N → WithTop ℝ) (Cap : Fin G.N → ℝ)
    (D Y q : Fin G.N → ℕ → ℝ) (r : Fin G.N → ℕ → ℕ → ℝ) : Prop :=
  G.RobustCapFeasible d Cap D Y q r ∧
    ∀ (D' Y' q' : Fin G.N → ℕ → ℝ) (r' : Fin G.N → ℕ → ℕ → ℝ),
      G.RobustCapFeasible d Cap D' Y' q' r' → G.robustObjective D Y ≤ G.robustObjective D' Y'

/-- `C'_k(t+1) = C_k - (2 p_k/(p_k + h_k)) ∑_{s ∈ O(k)} A_s(t)` of Theorem 4.3. -/
noncomputable def modifiedCap (Cap : Fin G.N → ℝ) (k : Fin G.N) (t : ℕ) : ℝ :=
  Cap k - 2 * G.p k / (G.p k + G.h k) * ∑ s ∈ G.tree.sinksBelow k, G.A s t

/-- Feasibility in the nominal network of Theorem 4.3: the order constraints of (32), the same
link capacities, and `X'_k(t+1) ≤ C'_k(t+1)` for every echelon `k` and period `t`. -/
def ModifiedCapFeasible (d : Fin G.N → WithTop ℝ) (Cap : Fin G.N → ℝ)
    (D : Fin G.N → ℕ → ℝ) : Prop :=
  G.OrdersFeasible D ∧ G.LinkCap d D ∧
    ∀ k, ∀ t < G.T, G.Xmod D k (t + 1) ≤ G.modifiedCap Cap k t

/-- A global minimizer of the nominal network of Theorem 4.3. -/
def IsModifiedCapOptimal (d : Fin G.N → WithTop ℝ) (Cap : Fin G.N → ℝ)
    (D : Fin G.N → ℕ → ℝ) : Prop :=
  G.ModifiedCapFeasible d Cap D ∧
    ∀ D', G.ModifiedCapFeasible d Cap D' → G.modifiedCost D ≤ G.modifiedCost D'

end RobustInventory.SingleStation.Supplement.Network


