-- Prove2me | Definitions.Def_SensitivityPoA_Lipschitz_Setting
-- name    : SensitivityPoA_Lipschitz_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T17:38:29.256727+00:00
-- url     : https://prove2.me/theorems/910120ba-2ee2-4a86-b43e-2d6d3ce439e2
-- title:
--   §2–§3.2 — nonatomic congestion games: network (G1–G2, Condition 1), games (G3–G4, Condition 2), flows, WE (2.1), SO, C∗, ˜C, ρ (2.5), Dist (3.3)
-- statement:
--   This file fixes the model of nonatomic congestion games of Wu and Möhring (§2–§3.2).
--
--   **Combinatorial structure.** A network has a finite set $A$ of arcs, a finite nonempty set $K$ of origin–destination (O/D) pairs and a finite set $S$ of paths. Each path $s$ is a nonempty set of arcs, encoded by a $0/1$ incidence column $(A_{as})_{a\in A}$, and serves exactly one O/D pair $k(s)$; $S_k$ is the set of paths serving $k$. The standing assumptions are: the incidence is $0/1$; every path contains an arc; $K\neq\emptyset$; and **Condition 1**: every arc lies on some path, and $|S_k|\ge 2$ for every $k\in K$.
--
--   **Games.** A (generalized) game $\Gamma=(\tau,d)$ consists of an arc cost function $\tau_a:\mathbb R\to\mathbb R$ for every arc and a demand $d_k$ for every O/D pair, with total demand $T(d)=\sum_{k\in K} d_k$. It is *generalized* when every $\tau_a$ is continuous, non-decreasing and non-negative on $[0,\infty)$ and every $d_k\ge 0$. It satisfies **Condition 2** when $T(d)>0$ and $\tau_a(x)>0$ for all arcs $a$ and all $x\in(0,T(d)]$. The **game space** $\mathcal G(G,K,S)$ is the set of generalized games satisfying Condition 2.
--
--   **Flows and costs.** A flow of $\Gamma$ is a vector $f=(f_s)_{s\in S}\ge 0$ with $\sum_{s\in S_k} f_s=d_k$ for every $k$. Its arc flows are $f_a=\sum_{s\ni a} f_s$, its path costs $\tau_s(f)=\sum_{a\in s}\tau_a(f_a)$, and its total cost is
--   $$C(\Gamma,f)=\sum_{a\in A} f_a\,\tau_a(f_a).$$
--   A flow $\tilde f$ is a **Wardrop equilibrium (WE)** if, for every pair $k$ and all $s,s'\in S_k$, $\tilde f_s>0$ implies $\tau_s(\tilde f)\le\tau_{s'}(\tilde f)$ (2.1). A flow is a **social optimum (SO)** if it has minimum total cost among all flows.
--
--   **The three maps.** The SO cost $C^*(\Gamma)$ is the infimum of $C(\Gamma,f)$ over all flows; the WE cost $\tilde C(\Gamma)$ is the supremum of $C(\Gamma,\tilde f)$ over all WE flows $\tilde f$ (all WE flows have the same cost, so this is the cost of any WE flow); and the **price of anarchy** is
--   $$\rho(\Gamma)=\frac{\tilde C(\Gamma)}{C^*(\Gamma)}.$$
--
--   **The distance (3.3).** For two games $\Gamma=(\tau,d)$ and $\Gamma'=(\sigma,d')$,
--   $$\|\Gamma-\Gamma'\|=\max\Big\{\|d-d'\|_\infty,\ \max_{a\in A}\max_{x\in[0,\min\{T(d),T(d')\}]}|\tau_a(x)-\sigma_a(x)|,\ \|\tau(T(d))-\sigma(T(d'))\|_\infty\Big\}.$$
--   It compares two cost functions only where both games use them, plus their values at the respective total demands.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Arc flows, the WE condition and feasibility come from the published module `KellyStochasticNetworks_Wardrop` (`linkFlow`, `wardropFeasible`, `IsWardropEquilibrium`). Paths are arbitrary nonempty $0/1$ columns rather than loop-free paths of a digraph, a generalization the paper's proofs do not use. Cost functions are total functions on $\mathbb R$ whose properties are required on $[0,\infty)$ only. The total cost is written in arc form, which equals the path form $\sum_s f_s\tau_s(f)$ for $0/1$ incidence. $C^*$ is an `sInf` and $\tilde C$ an `sSup` of images; both are meaningful on the game space, where an SO flow and a WE flow exist. The norm on demand and endpoint vectors is Mathlib's sup norm, and the middle term of (3.3) is the `sSup` over $A\times[0,\min\{T(d),T(d')\}]$, a compact set on which the costs are continuous.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), pp. 10–16, §2.1–§3.2, G1–G4, (2.1), (2.5), Conditions 1–2, (3.2)–(3.3)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

namespace SensitivityPoA.Lipschitz
open KellyStochasticNetworks

/-- The fixed combinatorial structure `(G, K, S)` (G1–G2): `J` arcs, `R` paths (routes) and
`Sd` O/D pairs; `A j r` is the arc–path incidence (`1` if arc `j` lies on path `r`) and
`s r` is the O/D pair served by path `r`, so that `S_k = {r | s r = k}`. -/
structure Network where
  J : ℕ
  R : ℕ
  Sd : ℕ
  A : Fin J → Fin R → ℝ
  s : Fin R → Fin Sd

/-- Standing assumptions on the combinatorial structure: 0/1 incidence, every path is a
nonempty arc set (G2), `K` is nonempty (G1), and Condition 1 (every arc lies on some path,
and `|S_k| ≥ 2` for every pair `k`). -/
def Network.Standing (N : Network) : Prop :=
  (∀ j r, N.A j r = 0 ∨ N.A j r = 1) ∧
  (∀ r, ∃ j, N.A j r = 1) ∧
  0 < N.Sd ∧
  (∀ j, ∃ r, N.A j r = 1) ∧
  (∀ k, 2 ≤ (Finset.univ.filter fun r => N.s r = k).card)

/-- A (generalized) game `Γ = (τ, d)` on the network `N`: arc cost functions and demands. -/
structure Game (N : Network) where
  τ : Fin N.J → ℝ → ℝ
  d : Fin N.Sd → ℝ

/-- Total demand `T(d) = Σ_k d_k` (G4). -/
def totalDemand {n : ℕ} (d : Fin n → ℝ) : ℝ := ∑ k, d k

/-- A cost function in `C↑+(ℝ≥0)`: continuous, non-decreasing and non-negative on `[0, ∞)`
(G3, (3.2)); values at negative arguments are irrelevant. -/
def IsCostFn (h : ℝ → ℝ) : Prop :=
  ContinuousOn h (Set.Ici 0) ∧ MonotoneOn h (Set.Ici 0) ∧ ∀ x, 0 ≤ x → 0 ≤ h x

variable {N : Network}

/-- `Γ` lies in the generalized game space `C↑+(ℝ≥0)^A × ℝ^K_{≥0}` of (3.2). -/
def Game.IsGeneralized (Γ : Game N) : Prop :=
  (∀ j, IsCostFn (Γ.τ j)) ∧ ∀ k, 0 ≤ Γ.d k

/-- Condition 2: `T(d) > 0` and `τ_a(x) > 0` for all arcs `a` and all `x ∈ (0, T(d)]`. -/
def Game.Condition2 (Γ : Game N) : Prop :=
  0 < totalDemand Γ.d ∧ ∀ j x, 0 < x → x ≤ totalDemand Γ.d → 0 < Γ.τ j x

/-- The game space `G(G, K, S)`: generalized games satisfying Condition 2. -/
def gameSpace (N : Network) : Set (Game N) :=
  {Γ | Γ.IsGeneralized ∧ Γ.Condition2}

/-- A (path) flow of `Γ`: non-negative path flows with `Σ_{s ∈ S_k} f_s = d_k` for every `k`. -/
def IsFlow (Γ : Game N) (f : Fin N.R → ℝ) : Prop :=
  f ∈ wardropFeasible N.s Γ.d

/-- Path cost `τ_s(f) = Σ_{a ∈ s} τ_a(f_a)`. -/
def pathCost (Γ : Game N) (f : Fin N.R → ℝ) (r : Fin N.R) : ℝ :=
  ∑ j, Γ.τ j (linkFlow N.A f j) * N.A j r

/-- Total cost `C(Γ, f) = Σ_a f_a · τ_a(f_a)` (arc form). -/
def cost (Γ : Game N) (f : Fin N.R → ℝ) : ℝ :=
  ∑ j, linkFlow N.A f j * Γ.τ j (linkFlow N.A f j)

/-- Wardrop equilibrium (2.1). -/
def IsWE (Γ : Game N) (f : Fin N.R → ℝ) : Prop :=
  IsWardropEquilibrium N.A N.s Γ.τ Γ.d f

/-- Social optimum: a flow of minimum total cost. -/
def IsSO (Γ : Game N) (f : Fin N.R → ℝ) : Prop :=
  IsFlow Γ f ∧ ∀ g, IsFlow Γ g → cost Γ f ≤ cost Γ g

/-- The SO cost `C*(Γ)`: the infimum of the total cost over all flows. -/
noncomputable def SOCost (Γ : Game N) : ℝ :=
  sInf (cost Γ '' {f | IsFlow Γ f})

/-- The WE cost `C̃(Γ)`: the supremum of the total cost over all WE flows (all WE flows have
the same cost, so this is the cost of an arbitrary WE flow). -/
noncomputable def WECost (Γ : Game N) : ℝ :=
  sSup (cost Γ '' {f | IsWE Γ f})

/-- The price of anarchy `ρ(Γ) = C̃(Γ) / C*(Γ)` (2.5). -/
noncomputable def PoA (Γ : Game N) : ℝ :=
  WECost Γ / SOCost Γ

/-- The distance (3.3) between two (generalized) games `Γ = (τ, d)` and `Γ' = (σ, d')`:
`max{‖d − d'‖_∞, max_a max_{x ∈ [0, min{T(d), T(d')}]} |τ_a(x) − σ_a(x)|, ‖τ(T(d)) − σ(T(d'))‖_∞}`.
The norm on `Fin n → ℝ` is Mathlib's sup norm. -/
noncomputable def gameDist (Γ Γ' : Game N) : ℝ :=
  max ‖Γ.d - Γ'.d‖
    (max (sSup ((fun p : Fin N.J × ℝ => |Γ.τ p.1 p.2 - Γ'.τ p.1 p.2|) ''
        (Set.univ ×ˢ Set.Icc 0 (min (totalDemand Γ.d) (totalDemand Γ'.d)))))
      ‖fun j => Γ.τ j (totalDemand Γ.d) - Γ'.τ j (totalDemand Γ'.d)‖)

end SensitivityPoA.Lipschitz


