-- Prove2me | Definitions.Def_RobustInventory_SingleStation_Supplement_NetworkDynamics
-- name    : RobustInventory_SingleStation_Supplement_NetworkDynamics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:23:46.086749+00:00
-- url     : https://prove2.me/theorems/65963f2a-7768-48a3-815f-7f773db653f9
-- title:
--   §4.1, (28)–(31) and (34): echelon stocks, coupling constraint and the supply chain with the modified demands
-- statement:
--   This file defines the stock dynamics of the tree network and the deterministic supply chain with modified demands. Let $D_k(t)$ be the order of echelon $k$ to its only supplier.
--
--   The nominal echelon stock is $\bar X_k(t)=X_k(0)+\sum_{\tau<t}[D_k(\tau)-\sum_{s\in O(k)}\bar W_s(\tau)]$. An order array is **feasible** if $D_k(t)\ge0$ for every echelon and period, plant links included, and, for every installation $k$ that is not a sink,
--   $$\sum_{i\in N(k)}D_i(t)\le\bar X_k(t)-\sum_{i\in N(k)}\bar X_i(t).$$
--   The right-hand side is the stock on hand of installation $k$. It does not depend on demand, and this constraint makes it nonnegative.
--
--   With $A_s(t)$ the value of LP (13) at sink $s$, echelon $k$ sees at sink $s$ the **modified demand** (34)
--   $$W'_{s,k}(t)=\bar W_s(t)+\frac{p_k-h_k}{p_k+h_k}\,(A_s(t)-A_s(t-1)),$$
--   and its modified stock is $X'_k(t)=X_k(0)+\sum_{\tau<t}[D_k(\tau)-\sum_{s\in O(k)}W'_{s,k}(\tau)]$. The **modified supply chain** minimizes $\sum_{t<T}\sum_{k}[C_k(D_k(t))+R_k(X'_k(t+1))]$ over the feasible order arrays.
--
--   **Formalization Note** Constraint (31) is not imposed at a sink, where its empty left side would forbid the backlog that §4.1 allows. It is written with $\bar X$ as printed, also in the modified supply chain: substituting $X'$ would change the physical stock on hand, because the modification depends on the echelon.
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), p. 157 (PDF 8), Eqs. (28)–(31); p. 158 (PDF 9), Eq. (34)

import Definitions.Def_RobustInventory_SingleStation_Supplement_Network

namespace RobustInventory.SingleStation.Supplement.Network

open Finset

variable (G : Network)

/-- The nominal stock `X̄_k(t)` of echelon `k` at the beginning of period `t`, as below (31):
`X_k(0) + ∑_{τ<t} (D_k(τ) - ∑_{s ∈ O(k)} W̄_s(τ))`. Here `D k τ` is the order `D_{i_k k}(τ)` of
echelon `k` to its only supplier. -/
noncomputable def Xbar (D : Fin G.N → ℕ → ℝ) (k : Fin G.N) (t : ℕ) : ℝ :=
  G.X0 k + ∑ τ ∈ Finset.range t, (D k τ - ∑ s ∈ G.tree.sinksBelow k, G.Wbar s τ)

/-- The constraints of (32) on the orders alone: `D ≥ 0`, plant links included, and, for every
installation `k` that is not a sink, the coupling constraint (31)
`∑_{i ∈ N(k)} D_ki(t) ≤ X̄_k(t) - ∑_{i ∈ N(k)} X̄_i(t)`. A sink may backlog, so (31) is not
imposed on it. -/
def OrdersFeasible (D : Fin G.N → ℕ → ℝ) : Prop :=
  (∀ i, ∀ t < G.T, 0 ≤ D i t) ∧
    ∀ k, ¬ G.tree.IsSink k → ∀ t < G.T,
      ∑ i ∈ G.tree.children k, D i t ≤ G.Xbar D k t - ∑ i ∈ G.tree.children k, G.Xbar D i t

/-- (34): the modified demand `W'_{s,k}(t)` that echelon `k` sees at sink `s`. -/
noncomputable def Wmod (s k : Fin G.N) (t : ℕ) : ℝ :=
  G.Wbar s t + (G.p k - G.h k) / (G.p k + G.h k) * (G.A s t - G.Aprev s t)

/-- The modified stock `X'_k(t) = X_k(0) + ∑_{τ<t} (D_k(τ) - ∑_{s ∈ O(k)} W'_{s,k}(τ))`. -/
noncomputable def Xmod (D : Fin G.N → ℕ → ℝ) (k : Fin G.N) (t : ℕ) : ℝ :=
  G.X0 k + ∑ τ ∈ Finset.range t, (D k τ - ∑ s ∈ G.tree.sinksBelow k, G.Wmod s k τ)

/-- The cost of the deterministic supply chain with the modified demands (34):
`∑_t ∑_k (C_k(D_k(t)) + max(h_k X'_k(t+1), -p_k X'_k(t+1)))`, over all `N` echelons. -/
noncomputable def modifiedCost (D : Fin G.N → ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range G.T, ∑ k, (G.C k (D k t) + G.R k (G.Xmod D k (t + 1)))

/-- A global minimizer of the deterministic supply chain with the modified demands (34), under
the order constraints of (32). These constraints do not depend on the demand. -/
def IsModifiedOptimal (D : Fin G.N → ℕ → ℝ) : Prop :=
  G.OrdersFeasible D ∧ ∀ D', G.OrdersFeasible D' → G.modifiedCost D ≤ G.modifiedCost D'

end RobustInventory.SingleStation.Supplement.Network


