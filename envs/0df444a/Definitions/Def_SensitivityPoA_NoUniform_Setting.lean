-- Prove2me | Definitions.Def_SensitivityPoA_NoUniform_Setting
-- name    : SensitivityPoA_NoUniform_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T17:38:27.967574+00:00
-- url     : https://prove2.me/theorems/04290775-d3be-4c08-8d69-36e1c23c2245
-- title:
--   §2–§3.2, §3.5 — nonatomic congestion games: network, games (G1–G4, Conditions 1–2), flows, WE (2.1), C∗, ˜C, ρ (2.5), Dist (3.3), cost normalization Ψ_υ
-- statement:
--   This file fixes the model of nonatomic congestion games of Wu and Möhring (§2–§3.2) together with the cost normalization of §3.5.
--
--   **Combinatorial structure.** A network has arcs $a = 1,\dots,|A|$, paths (routes) $s = 1,\dots,|S|$ and origin–destination (O/D) pairs $k = 1,\dots,|K|$. A path is described by its arc incidence: $A_{as} = 1$ if arc $a$ lies on path $s$ and $A_{as}=0$ otherwise; each path serves exactly one O/D pair, and $S_k$ is the set of paths of pair $k$. The *standing assumptions* are:
--
--   1. incidences are $0$ or $1$, and every path contains at least one arc (G2);
--   2. there is at least one O/D pair (G1);
--   3. **Condition 1** (p. 14): every arc lies on some path, and $|S_k| \ge 2$ for every pair $k$.
--
--   A separate predicate, the **antichain condition**, says that no path of a pair $k$ is contained (as an arc set) in another path of the same pair.
--
--   **Games.** A game $\Gamma = (\tau, d)$ consists of arc cost functions $\tau_a : \mathbb R \to \mathbb R$ and demands $d_k$, with total demand $T(d) = \sum_{k} d_k$. It is a *generalized game* when every $\tau_a$ is continuous, non-decreasing and non-negative on $[0,\infty)$ and every $d_k \ge 0$ ((3.2)); it satisfies **Condition 2** when $T(d) > 0$ and $\tau_a(x) > 0$ for every arc $a$ and every $x \in (0, T(d)]$. The **game space** $\mathcal G(G, K, S)$ is the set of generalized games satisfying Condition 2.
--
--   **Flows and costs.** A flow $f = (f_s)_s$ is non-negative with $\sum_{s \in S_k} f_s = d_k$ for every $k$; its arc flows are $f_a = \sum_s A_{as} f_s$, and its total cost is
--   $$C(\Gamma, f) = \sum_{a} f_a\,\tau_a(f_a).$$
--   A flow is a **Wardrop equilibrium** (WE, (2.1)) if every used path of a pair $k$ has minimal path cost $\tau_s(f) = \sum_{a \in s} \tau_a(f_a)$ among the paths of $S_k$. The SO cost is $C^*(\Gamma) = \inf_f C(\Gamma, f)$ over all flows, the WE cost is $\tilde C(\Gamma) = \sup C(\Gamma, \tilde f)$ over WE flows $\tilde f$, and the **price of anarchy** is
--   $$\rho(\Gamma) = \frac{\tilde C(\Gamma)}{C^*(\Gamma)} \qquad (2.5).$$
--
--   **Distance.** For two games $\Gamma = (\tau, d)$, $\Gamma' = (\sigma, d')$, (3.3) sets
--   $$\|\Gamma - \Gamma'\| = \max\Big\{\|d - d'\|_\infty,\ \max_{a,\ x \in [0, \min\{T(d), T(d')\}]} |\tau_a(x) - \sigma_a(x)|,\ \|\tau(T(d)) - \sigma(T(d'))\|_\infty\Big\}.$$
--
--   **Cost normalization** (§3.5, p. 21). For $\upsilon > 0$, $\Psi_\upsilon(\tau, d) = (\tau/\upsilon, d)$ divides every arc cost function by $\upsilon$ and keeps the demands.
--
--   These objects are the setting of Theorem 8 and of every milestone of this mission.
--
--   **Formalization Note.** The published module `KellyStochasticNetworks_Wardrop` supplies arc flows (`linkFlow`), feasible flows (`wardropFeasible`) and Wardrop's first principle (`IsWardropEquilibrium`), reused here. Paths are arbitrary $0/1$ incidence columns rather than loop-free paths of a digraph; the antichain condition (true for loop-free $(o_k,t_k)$-paths) is a separate predicate assumed by the theorems of this mission, because without it (e.g. $S_k = \{\{a\},\{a,b\}\}$) every game has $\rho = 1$. Non-empty paths and $K \neq \emptyset$ are G1–G2 made explicit. Cost functions are functions on $\mathbb R$ whose properties are required on $[0,\infty)$ only. $C^*$ is an `sInf` and $\tilde C$ an `sSup` of a set of reals; the paper notes all WE flows have the same cost, so $\tilde C$ is the cost of any WE flow. The cost is in arc form, equal to the path form $\sum_s f_s \tau_s(f)$ for $0/1$ incidences. $\rho$ is a real quotient (Lean's $x/0 = 0$), which is why every theorem quantifies over the game space only. The middle term of the distance is the `sSup` of the image of the compact set $A \times [0, \min\{T(d), T(d')\}]$; the vector norms are Mathlib's sup norm on `Fin n → ℝ`, i.e. $\|\cdot\|_\infty$.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), pp. 10–16, 21, §2.1–§3.2, G1–G4, (2.1), (2.5), Conditions 1–2, (3.2), (3.3), §3.5 (cost normalization)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

namespace SensitivityPoA.NoUniform

open KellyStochasticNetworks

/-- The fixed combinatorial structure `(G, K, S)` (G1–G2, p. 10): `J` arcs, `R` routes (paths),
`Sd` O/D pairs; `A j r` is the arc–route incidence (`1` if arc `j` lies on route `r`) and `s r`
is the O/D pair served by route `r`, so `S_k = {r | s r = k}`. -/
structure Network where
  J : ℕ
  R : ℕ
  Sd : ℕ
  A : Fin J → Fin R → ℝ
  s : Fin R → Fin Sd

/-- Standing assumptions on `(G, K, S)`: incidences are `0/1`, every route is a non-empty arc set
(G2), `K` is non-empty (G1), and Condition 1 (p. 14): every arc lies on some route and every
O/D pair has at least two routes. -/
def Network.Standing (N : Network) : Prop :=
  (∀ j r, N.A j r = 0 ∨ N.A j r = 1) ∧
  (∀ r, ∃ j, N.A j r = 1) ∧
  0 < N.Sd ∧
  (∀ j, ∃ r, N.A j r = 1) ∧
  (∀ k, 2 ≤ (Finset.univ.filter fun r => N.s r = k).card)

/-- No route of an O/D pair is contained (as an arc set) in another route of the same pair.
This holds for loop-free `(o_k, t_k)`-paths of a digraph (G2) and is stated explicitly because
routes are encoded as arbitrary `0/1` incidence columns. -/
def Network.Antichain (N : Network) : Prop :=
  ∀ r r', N.s r = N.s r' → r ≠ r' → ¬ (∀ j, N.A j r = 1 → N.A j r' = 1)

/-- A (generalized) game `Γ = (τ, d)` on `N` (G3–G4): an arc cost function vector `τ` and a
demand vector `d`. Its properties are imposed by `IsGeneralized` and `Condition2`. -/
structure Game (N : Network) where
  τ : Fin N.J → ℝ → ℝ
  d : Fin N.Sd → ℝ

/-- Total demand `T(d) = ∑_k d_k` (G4). -/
def totalDemand {Sd : ℕ} (d : Fin Sd → ℝ) : ℝ := ∑ k, d k

/-- `h ∈ C↑+(ℝ≥0)`: continuous, non-decreasing and non-negative on `[0, ∞)` (G3, (3.2)). -/
def IsCostFn (h : ℝ → ℝ) : Prop :=
  ContinuousOn h (Set.Ici 0) ∧ MonotoneOn h (Set.Ici 0) ∧ ∀ x, 0 ≤ x → 0 ≤ h x

/-- `Γ` is a generalized game, an element of `C↑+(ℝ≥0)^A × ℝ^K_≥0` ((3.2), p. 16). -/
def Game.IsGeneralized {N : Network} (Γ : Game N) : Prop :=
  (∀ j, IsCostFn (Γ.τ j)) ∧ ∀ k, 0 ≤ Γ.d k

/-- Condition 2 (p. 14): `T(d) > 0` and `τ_a(x) > 0` for all arcs `a` and all `x ∈ (0, T(d)]`. -/
def Game.Condition2 {N : Network} (Γ : Game N) : Prop :=
  0 < totalDemand Γ.d ∧ ∀ j x, 0 < x → x ≤ totalDemand Γ.d → 0 < Γ.τ j x

/-- The game space `G(G, K, S)` (p. 15): generalized games satisfying Condition 2. -/
def gameSpace (N : Network) : Set (Game N) :=
  {Γ | Γ.IsGeneralized ∧ Γ.Condition2}

/-- A (path) flow of `Γ`: non-negative route flows with `∑_{s ∈ S_k} f_s = d_k` (p. 10). -/
def IsFlow {N : Network} (Γ : Game N) (f : Fin N.R → ℝ) : Prop :=
  f ∈ wardropFeasible N.s Γ.d

/-- Total cost `C(Γ, f) = ∑_a f_a τ_a(f_a)` (p. 11), with arc flow `f_a = linkFlow N.A f a`. -/
def cost {N : Network} (Γ : Game N) (f : Fin N.R → ℝ) : ℝ :=
  ∑ j, linkFlow N.A f j * Γ.τ j (linkFlow N.A f j)

/-- Wardrop equilibrium (2.1), p. 11: the published `IsWardropEquilibrium`. -/
def IsWE {N : Network} (Γ : Game N) (f : Fin N.R → ℝ) : Prop :=
  IsWardropEquilibrium N.A N.s Γ.τ Γ.d f

/-- SO cost `C∗(Γ)` (pp. 11, 18): the minimum total cost over all flows (`sInf`). -/
noncomputable def SOCost {N : Network} (Γ : Game N) : ℝ :=
  sInf (cost Γ '' {f | IsFlow Γ f})

/-- WE cost `C̃(Γ)` (pp. 11–12, 18): the (worst-case) total cost of a WE flow (`sSup`). -/
noncomputable def WECost {N : Network} (Γ : Game N) : ℝ :=
  sSup (cost Γ '' {f | IsWE Γ f})

/-- The price of anarchy `ρ(Γ) = C̃(Γ) / C∗(Γ)` ((2.5), p. 12). -/
noncomputable def PoA {N : Network} (Γ : Game N) : ℝ :=
  WECost Γ / SOCost Γ

/-- The distance `Dist(Γ, Γ') = ‖Γ − Γ'‖` of (3.3), p. 16:
`max{‖d − d'‖_∞, max_{a, x ∈ [0, min{T(d), T(d')}]} |τ_a(x) − σ_a(x)|, ‖τ(T(d)) − σ(T(d'))‖_∞}`.
The norm on `Fin n → ℝ` is Mathlib's sup norm. -/
noncomputable def gameDist {N : Network} (Γ Γ' : Game N) : ℝ :=
  max ‖Γ.d - Γ'.d‖
    (max (sSup ((fun p : Fin N.J × ℝ => |Γ.τ p.1 p.2 - Γ'.τ p.1 p.2|) ''
        (Set.univ ×ˢ Set.Icc 0 (min (totalDemand Γ.d) (totalDemand Γ'.d)))))
      ‖fun j => Γ.τ j (totalDemand Γ.d) - Γ'.τ j (totalDemand Γ'.d)‖)

/-- The cost normalization `Ψ_υ(τ, d) = (τ/υ, d)` (§3.5, p. 21). -/
noncomputable def costNormalize {N : Network} (υ : ℝ) (Γ : Game N) : Game N :=
  ⟨fun j x => Γ.τ j x / υ, Γ.d⟩

end SensitivityPoA.NoUniform


