-- Prove2me | Definitions.Def_RobustInventory_SingleStation_Supplement_Network
-- name    : RobustInventory_SingleStation_Supplement_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:23:08.739695+00:00
-- url     : https://prove2.me/theorems/7daec3b3-0228-4edc-92f5-1fa0cea9a793
-- title:
--   §4.1: tree supply network, its echelons, costs and budgeted demand uncertainty, and the deviations $A_s(t)$
-- statement:
--   This file defines the supply chain of §4.1.
--
--   A **supply tree** on installations $1,\dots,N$ gives each installation at most one supplying installation and has no cycle. An installation without one is a **source**, supplied by an outside plant; several sources are allowed. Write $N(k)$ for the installations supplied by $k$. A **sink** supplies no installation. Echelon $k$ consists of $k$ and every installation that receives stock from it, directly or not, and $O(k)$ is the set of sinks in echelon $k$.
--
--   A **network** adds a horizon $T$, initial echelon stocks $X_k(0)$, and for each echelon $k$ costs $c_k>0$, $K_k\ge0$, $h_k\ge0$, $p_k>c_k$ with purchasing cost $C_k(u)=K_k+c_ku$ for $u>0$, $C_k(0)=0$, and holding/shortage cost $R_k(x)=\max(h_kx,-p_kx)$. Each sink $s$ has nominal demands $\bar W_s(t)$, deviations $\hat W_s(t)\ge0$ and budgets with $\Gamma_s(0)\ge0$, $0\le\Gamma_s(t+1)-\Gamma_s(t)\le1$. The worst deviation of its cumulative demand is the value of LP (13),
--   $$A_s(t)=\max\Big\{\sum_{\tau=0}^{t}\hat W_s(\tau)z_\tau:\ 0\le z_\tau\le1,\ \sum_{\tau=0}^{t}z_\tau\le\Gamma_s(t)\Big\},$$
--   with $A_s(-1)=0$.
--
--   **Formalization Note** Installations are `Fin N`. Demand data at installations that are not sinks are never used. The printed set $\mathcal P_s$ on p. 157 omits the absolute values on $Z_s(\tau)$ in the budget, a misprint for the set of §3.1; only LP (13) is used here. `deviationValue` is the same supremum as the published `Model.A`, stated for a deviation and a budget sequence alone, because a sink carries no single-station cost data.
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), p. 157 (PDF 8), §4.1; p. 153 (PDF 4), LP (13); p. 158 (PDF 9), Theorem 4.2

import Mathlib

namespace RobustInventory.SingleStation.Supplement

open Finset

/-- A tree network on the installations `Fin N` (§4.1, p. 157), with possibly several sources:
`parent i = some k` says that installation `k` supplies `i`, and `parent i = none` that `i` is a
source, supplied by an outside plant. No installation is its own direct or indirect supplier. -/
structure SupplyTree (N : ℕ) where
  parent : Fin N → Option (Fin N)
  acyclic : ∀ i, ¬ Relation.TransGen (fun a b => parent a = some b) i i

namespace SupplyTree

variable {N : ℕ} (G : SupplyTree N)

/-- `N(k)`: the installations supplied by installation `k`. -/
def children (k : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun i => G.parent i = some k)

/-- A sink supplies no installation. -/
def IsSink (k : Fin N) : Prop := G.children k = ∅

/-- `i` is in echelon `k`: it is `k` itself or it receives stock from `k`, directly or not. -/
def InEchelon (i k : Fin N) : Prop :=
  Relation.ReflTransGen (fun a b => G.parent a = some b) i k

open Classical in
/-- `O(k)`: the sink nodes in echelon `k` (so `O(s) = {s}` for a sink `s`). -/
noncomputable def sinksBelow (k : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun s => G.IsSink s ∧ G.InEchelon s k)

end SupplyTree

/-- The optimal value of the linear program (13) for deviations `what` and budgets `Γ`:
`max {∑_{τ=0}^{t} ŵ_τ z_τ : 0 ≤ z_τ ≤ 1, ∑_{τ=0}^{t} z_τ ≤ Γ_t}`.
For `Γ_t ≥ 0` the set of values is nonempty (`z = 0`) and bounded above (by `∑ |ŵ_τ|`), so the
supremum is the optimal value. -/
noncomputable def deviationValue (what Γ : ℕ → ℝ) (t : ℕ) : ℝ :=
  sSup {v : ℝ | ∃ z : ℕ → ℝ,
    ((∀ τ ≤ t, 0 ≤ z τ ∧ z τ ≤ 1) ∧ ∑ τ ∈ Finset.range (t + 1), z τ ≤ Γ t) ∧
    v = ∑ τ ∈ Finset.range (t + 1), what τ * z τ}

/-- The data of the supply chain of §4.1, p. 157.

* `N` installations, also indexing the `N` echelons, on the supply tree `tree`; periods `t < T`;
* `X0 k`: the initial stock `X_k(0)` of echelon `k`;
* `c k`, `K k`, `h k`, `p k`: the costs of echelon `k`, as in §3.1;
* `Wbar s t`, `What s t`, `Γ s t`: nominal demand, deviation and budget at a sink `s`;
  their values at installations that are not sinks are never used. -/
structure Network where
  N : ℕ
  T : ℕ
  tree : SupplyTree N
  X0 : Fin N → ℝ
  c : Fin N → ℝ
  K : Fin N → ℝ
  h : Fin N → ℝ
  p : Fin N → ℝ
  Wbar : Fin N → ℕ → ℝ
  What : Fin N → ℕ → ℝ
  Γ : Fin N → ℕ → ℝ
  hc : ∀ k, 0 < c k
  hK : ∀ k, 0 ≤ K k
  hh : ∀ k, 0 ≤ h k
  hpc : ∀ k, c k < p k
  hWhat : ∀ s, tree.IsSink s → ∀ t, 0 ≤ What s t
  hΓ0 : ∀ s, tree.IsSink s → 0 ≤ Γ s 0
  hΓmono : ∀ s, tree.IsSink s → ∀ t, Γ s t ≤ Γ s (t + 1)
  hΓstep : ∀ s, tree.IsSink s → ∀ t, Γ s (t + 1) ≤ Γ s t + 1

namespace Network

variable (G : Network)

/-- The purchasing cost (7) of echelon `k`: `K_k + c_k u` if `u > 0` and `0` otherwise
(orders are nonnegative). -/
noncomputable def C (k : Fin G.N) (u : ℝ) : ℝ := if 0 < u then G.K k + G.c k * u else 0

/-- The holding/shortage cost (8) of echelon `k`: `max(h_k x, -p_k x)`. -/
noncomputable def R (k : Fin G.N) (x : ℝ) : ℝ := max (G.h k * x) (-(G.p k * x))

/-- `A_s(t)`: the value of (13) with the deviations and budgets of sink `s`. -/
noncomputable def A (s : Fin G.N) (t : ℕ) : ℝ := deviationValue (G.What s) (G.Γ s) t

/-- `A_s(t - 1)`, with `A_s(-1) = 0`. -/
noncomputable def Aprev (s : Fin G.N) : ℕ → ℝ
  | 0 => 0
  | t + 1 => G.A s t

end Network

end RobustInventory.SingleStation.Supplement


