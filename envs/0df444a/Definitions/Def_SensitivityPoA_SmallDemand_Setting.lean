-- Prove2me | Definitions.Def_SensitivityPoA_SmallDemand_Setting
-- name    : SensitivityPoA_SmallDemand_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T17:38:36.411154+00:00
-- url     : https://prove2.me/theorems/800d116b-7f5a-4b9a-b9a2-eaaa387af241
-- title:
--   §2–§3.5 — nonatomic congestion games: network (G1–G2, Condition 1), games (G3–G4, Condition 2), flows, WE (2.1), SO, C∗, ˜C, ρ (2.5), Dist (3.3), Lipschitz on [0, T], demand normalization Λ_υ
-- statement:
--   This file sets up the nonatomic congestion games of Wu and Möhring (§2–§3.5).
--
--   1. **Structure** $(G, \mathcal K, \mathcal S)$. There are finitely many arcs $a \in A$, finitely many origin–destination (O/D) pairs $k \in \mathcal K$ and finitely many paths (routes) $s \in \mathcal S$. Each path serves exactly one O/D pair; $\mathcal S_k$ is the set of paths of pair $k$. A path is a set of arcs, recorded as a 0/1 arc–path incidence matrix $(A_{as})$. The **standing assumptions** are: incidences are $0$ or $1$; every path contains at least one arc (G2); $\mathcal K$ is nonempty (G1); and Condition 1: every arc lies on some path, and $|\mathcal S_k| \ge 2$ for every pair $k$.
--   2. **Games.** A game $\Gamma = (\tau, d)$ consists of arc cost functions $\tau_a : \mathbb R \to \mathbb R$ and demands $d_k \in \mathbb R$, with total demand $T(d) = \sum_{k} d_k$. A function $h$ is a **cost function** ($h \in C^{\uparrow}_{+}(\mathbb R_{\ge 0})$) if it is continuous, non-decreasing and non-negative on $[0, \infty)$. $\Gamma$ is a **generalized game** if every $\tau_a$ is a cost function and $d \ge 0$; it satisfies **Condition 2** if $T(d) > 0$ and $\tau_a(x) > 0$ for all $a$ and all $x \in (0, T(d)]$. The **game space** $\mathcal G(G, \mathcal K, \mathcal S)$ is the set of generalized games satisfying Condition 2.
--   3. **Flows and costs.** A flow $f = (f_s)_{s \in \mathcal S}$ of $\Gamma$ satisfies $f_s \ge 0$ and $\sum_{s \in \mathcal S_k} f_s = d_k$ for every $k$. Its arc flows are $f_a = \sum_{s \ni a} f_s$, its path costs $\tau_s(f) = \sum_{a \in s} \tau_a(f_a)$, and its total cost is
--   $$C(\Gamma, f) = \sum_{a \in A} f_a \, \tau_a(f_a).$$
--   A flow is a **Wardrop equilibrium** (WE) if every path carrying positive flow is a cheapest path of its pair, (2.1); it is a **social optimum** (SO) if it minimizes $C(\Gamma, \cdot)$ over all flows.
--   4. **The three maps.** $\mathcal C^*(\Gamma)$ is the infimum of $C(\Gamma, f)$ over all flows $f$; $\tilde{\mathcal C}(\Gamma)$ is the supremum of $C(\Gamma, f)$ over all WE flows $f$; the **price of anarchy** is
--   $$\rho(\Gamma) = \frac{\tilde{\mathcal C}(\Gamma)}{\mathcal C^*(\Gamma)}.$$
--   5. **Distance** (3.3). For $\Gamma = (\tau, d)$ and $\Gamma' = (\sigma, d')$,
--   $$\|\Gamma - \Gamma'\| = \max\Big\{ \|d - d'\|_\infty,\ \max_{a \in A,\ x \in [0, \min\{T(d), T(d')\}]} |\tau_a(x) - \sigma_a(x)|,\ \|\tau(T(d)) - \sigma(T(d'))\|_\infty \Big\}.$$
--   6. **Lipschitz on an interval.** $h$ is Lipschitz on $[0, T]$ with constant $M$ if $|h(x) - h(y)| \le M |x - y|$ for all $x, y \in [0, T]$.
--   7. **Demand normalization** (§3.5). For $\upsilon > 0$, $\Lambda_\upsilon(\tau, d) = (\tau \circ \upsilon, d/\upsilon)$ with $(\tau_a \circ \upsilon)(x) = \tau_a(x \cdot \upsilon)$ and $d/\upsilon = (d_k/\upsilon)_k$.
--
--   These are the objects of Corollary 5.1 and of its milestones.
--
--   **Formalization Note** The Wardrop condition, the flow polytope and the arc flows are taken from the published definition `KellyStochasticNetworks_Wardrop`. Paths are arbitrary nonempty 0/1 incidence columns rather than loop-free paths of a digraph, which is more general and is not used by the arguments of §5. The total cost is written in arc form; for 0/1 incidence it equals the path form $\sum_s f_s \tau_s(f)$. Cost functions are functions on $\mathbb R$ whose properties are required on $[0,\infty)$ only. $\mathcal C^*$ is a real infimum and $\tilde{\mathcal C}$ a real supremum: on the game space flows and WE flows exist and all WE flows have the same cost (p. 11), so these are the paper's values; off the game space $\rho$ carries no meaning, and every theorem of this mission quantifies over games of the game space. The max of (3.3) is a real supremum of the image of the compact set $A \times [0, \min\{T(d), T(d')\}]$, and $\|\cdot\|_\infty$ is Mathlib's sup norm on $\mathbb R^n$. The demand normalization uses the formula $\tau_a(x\upsilon)$ for every $x$, whereas the page defines it on $[0, T(d)/\upsilon]$; every quantity in this mission depends on cost values on $[0, T(d)/\upsilon]$ only.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), pp. 10–22, §2.1–§3.2, §3.5, G1–G4, (2.1), (2.5), Conditions 1–2, (3.2), (3.3), p. 13 (Lipschitz), p. 22 (demand normalization)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

namespace SensitivityPoA.SmallDemand

open KellyStochasticNetworks

/-- The fixed combinatorial structure `(G, K, S)` of a nonatomic congestion game (G1–G2): `J` arcs,
`R` routes (paths) and `Sd` origin–destination pairs; `A j r` is the arc–route incidence and `s r`
is the O/D pair served by route `r`, so `S_k = {r | s r = k}`. -/
structure Network where
  J : ℕ
  R : ℕ
  Sd : ℕ
  A : Fin J → Fin R → ℝ
  s : Fin R → Fin Sd

/-- Standing assumptions on the structure: 0/1 incidence, every route is a nonempty arc set (G2),
there is at least one O/D pair (G1), and Condition 1 (every arc lies on some route, and every
O/D pair has at least two routes). -/
def Network.Standing (N : Network) : Prop :=
  (∀ j r, N.A j r = 0 ∨ N.A j r = 1) ∧
  (∀ r, ∃ j, N.A j r = 1) ∧
  0 < N.Sd ∧
  (∀ j, ∃ r, N.A j r = 1) ∧
  ∀ k, 2 ≤ (Finset.univ.filter fun r => N.s r = k).card

/-- A (generalized) game `Γ = (τ, d)` on the structure `N`: arc cost functions and a demand vector. -/
structure Game (N : Network) where
  τ : Fin N.J → ℝ → ℝ
  d : Fin N.Sd → ℝ

/-- The total demand `T(d) = Σ_k d_k`. -/
def totalDemand {n : ℕ} (d : Fin n → ℝ) : ℝ := ∑ k, d k

/-- `h ∈ C↑+(ℝ≥0)`: continuous, non-decreasing and non-negative on `[0, ∞)` (G3, (3.2)). -/
def IsCostFn (h : ℝ → ℝ) : Prop :=
  ContinuousOn h (Set.Ici 0) ∧ MonotoneOn h (Set.Ici 0) ∧ ∀ x, 0 ≤ x → 0 ≤ h x

/-- `Γ` belongs to the generalized game space `C↑+(ℝ≥0)^A × ℝ^K_{≥0}` of (3.2). -/
def Game.IsGeneralized {N : Network} (Γ : Game N) : Prop :=
  (∀ j, IsCostFn (Γ.τ j)) ∧ ∀ k, 0 ≤ Γ.d k

/-- Condition 2: `T(d) > 0` and `τ_a(x) > 0` for all arcs `a` and all `x ∈ (0, T(d)]`. -/
def Game.Condition2 {N : Network} (Γ : Game N) : Prop :=
  0 < totalDemand Γ.d ∧ ∀ j x, 0 < x → x ≤ totalDemand Γ.d → 0 < Γ.τ j x

/-- The game space `G(G, K, S)`: generalized games satisfying Condition 2 (§3.2). -/
def gameSpace (N : Network) : Set (Game N) :=
  {Γ | Γ.IsGeneralized ∧ Γ.Condition2}

/-- A (path) flow of `Γ`: nonnegative route flows with `Σ_{s ∈ S_k} f_s = d_k` for every pair `k`. -/
def IsFlow {N : Network} (Γ : Game N) (f : Fin N.R → ℝ) : Prop :=
  f ∈ wardropFeasible N.s Γ.d

/-- The cost `τ_s(f) = Σ_{a ∈ s} τ_a(f_a)` of route `r` under the flow `f`. -/
def pathCost {N : Network} (Γ : Game N) (f : Fin N.R → ℝ) (r : Fin N.R) : ℝ :=
  ∑ j, Γ.τ j (linkFlow N.A f j) * N.A j r

/-- The total cost `C(Γ, f) = Σ_a f_a · τ_a(f_a)` (arc form). -/
def cost {N : Network} (Γ : Game N) (f : Fin N.R → ℝ) : ℝ :=
  ∑ j, linkFlow N.A f j * Γ.τ j (linkFlow N.A f j)

/-- `f` is a Wardrop equilibrium (WE) of `Γ`: Wardrop's first principle (2.1). -/
def IsWE {N : Network} (Γ : Game N) (f : Fin N.R → ℝ) : Prop :=
  IsWardropEquilibrium N.A N.s Γ.τ Γ.d f

/-- `f` is a social optimum (SO) of `Γ`: a flow of minimum total cost. -/
def IsSO {N : Network} (Γ : Game N) (f : Fin N.R → ℝ) : Prop :=
  IsFlow Γ f ∧ ∀ g, IsFlow Γ g → cost Γ f ≤ cost Γ g

/-- The SO cost `C∗(Γ)`: the infimum of the total cost over all flows of `Γ`. -/
noncomputable def SOCost {N : Network} (Γ : Game N) : ℝ :=
  sInf (cost Γ '' {f | IsFlow Γ f})

/-- The WE cost `˜C(Γ)`: the supremum (worst case) of the total cost over the WE flows of `Γ`. -/
noncomputable def WECost {N : Network} (Γ : Game N) : ℝ :=
  sSup (cost Γ '' {f | IsWE Γ f})

/-- The price of anarchy `ρ(Γ) = ˜C(Γ) / C∗(Γ)` (2.5). -/
noncomputable def PoA {N : Network} (Γ : Game N) : ℝ :=
  WECost Γ / SOCost Γ

/-- The distance (3.3) between two generalized games `Γ = (τ, d)` and `Γ' = (σ, d')`:
`max{‖d − d'‖_∞, max_{a, x ∈ [0, min{T(d), T(d')}]} |τ_a(x) − σ_a(x)|, ‖τ(T(d)) − σ(T(d'))‖_∞}`.
The norm on `Fin n → ℝ` is Mathlib's sup norm. -/
noncomputable def gameDist {N : Network} (Γ Γ' : Game N) : ℝ :=
  max ‖Γ.d - Γ'.d‖
    (max (sSup ((fun p : Fin N.J × ℝ => |Γ.τ p.1 p.2 - Γ'.τ p.1 p.2|) ''
        (Set.univ ×ˢ Set.Icc 0 (min (totalDemand Γ.d) (totalDemand Γ'.d)))))
      ‖fun j => Γ.τ j (totalDemand Γ.d) - Γ'.τ j (totalDemand Γ'.d)‖)

/-- `h` is Lipschitz continuous on `[0, T]` with Lipschitz constant `M` (p. 13). -/
def LipOnIcc (h : ℝ → ℝ) (T M : ℝ) : Prop :=
  ∀ x ∈ Set.Icc 0 T, ∀ y ∈ Set.Icc 0 T, |h x - h y| ≤ M * |x - y|

/-- The demand normalization `Λ_υ(τ, d) = (τ ∘ υ, d/υ)` (§3.5, p. 22), with
`(τ_a ∘ υ)(x) = τ_a(x · υ)`; the formula is used for every `x`. -/
noncomputable def demandNormalize {N : Network} (υ : ℝ) (Γ : Game N) : Game N :=
  ⟨fun j x => Γ.τ j (x * υ), fun k => Γ.d k / υ⟩

end SensitivityPoA.SmallDemand


