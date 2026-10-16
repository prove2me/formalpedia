-- Prove2me | Definitions.Def_SensitivityPoA_Holder_Setting
-- name    : SensitivityPoA_Holder_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T17:38:37.936192+00:00
-- url     : https://prove2.me/theorems/18b9e436-2122-437b-b2bb-ea228ac54805
-- title:
--   §2–§3.2 — nonatomic congestion games: network, games (G1–G4, Conditions 1–2), flows, WE (2.1), SO, ǫ-approximate WE (2.7), Φ (2.6), C∗, C̃, ρ (2.5), Dist (3.3)
-- statement:
--   This file sets up the model of nonatomic congestion games of Wu and Möhring (§2–§3.2).
--
--   **Combinatorial structure.** A network $N$ has a finite set $A$ of arcs, a finite set $\mathcal S$ of paths and a finite non-empty set $\mathcal K$ of origin–destination (O/D) pairs. Each path $s$ serves exactly one O/D pair, and $\mathcal S_k$ is the set of paths of pair $k$. Paths are recorded through a 0/1 arc–path incidence matrix ($A_{a s} = 1$ iff $a \in s$). The §2 model assumptions are: every path contains at least one arc, $\mathcal K \neq \emptyset$, and $|\mathcal S_k| \ge 1$ for every $k$. From §3.1, Condition 1 also requires every arc to lie on a path and $|\mathcal S_k| \ge 2$.
--
--   **Games.** A (generalized) game $\Gamma = (\tau, d)$ consists of arc cost functions $\tau_a$ and demands $d_k$. It is *generalized* if every $\tau_a$ is continuous, non-decreasing and non-negative on $[0,\infty)$ and every $d_k \ge 0$. The total demand is $T(d) = \sum_{k} d_k$. The *game space* $\mathcal G(G,\mathcal K,\mathcal S)$ consists of the generalized games satisfying Condition 2: $T(d) > 0$ and $\tau_a(x) > 0$ for all arcs $a$ and all $x \in (0, T(d)]$.
--
--   **Flows and costs.** A flow $f = (f_s)_{s\in\mathcal S}$ is non-negative with $\sum_{s \in \mathcal S_k} f_s = d_k$ for each $k$. The arc flow is $f_a = \sum_{s \ni a} f_s$, the path cost is $\tau_s(f) = \sum_{a \in s} \tau_a(f_a)$, and the total cost is
--   $$C(\Gamma, f) = \sum_{a\in A} f_a\,\tau_a(f_a).$$
--   A flow is a *Wardrop equilibrium* (WE) if every used path of a pair is a cheapest path of that pair (2.1), a *social optimum* (SO) if it minimizes $C(\Gamma,\cdot)$, and an *$\epsilon$-approximate WE* if $\sum_a \tau_a(f_a)(f_a - g_a) \le \epsilon$ for every flow $g$ (2.7). The potential is $\Phi(\Gamma, f) = \sum_a \int_0^{f_a} \tau_a(x)\,dx$ (2.6).
--
--   **The three maps.** $\mathcal C^*(\Gamma)$ is the infimum of the total cost over all flows, $\tilde{\mathcal C}(\Gamma)$ the supremum of the total cost over all WE flows, and the price of anarchy is $\rho(\Gamma) = \tilde{\mathcal C}(\Gamma)/\mathcal C^*(\Gamma)$ (2.5).
--
--   **The metric.** For two games $\Gamma = (\tau, d)$, $\Gamma' = (\sigma, d')$,
--   $$\mathrm{Dist}(\Gamma,\Gamma') = \max\Big\{\|d - d'\|_\infty,\ \max_{a\in A}\max_{x\in[0,\min\{T(d),T(d')\}]}|\tau_a(x) - \sigma_a(x)|,\ \|\tau(T(d)) - \sigma(T(d'))\|_\infty\Big\}\quad(3.3),$$
--   written $\|\Gamma - \Gamma'\|$ in the paper. A function $h$ is Lipschitz on $[0,T]$ with constant $M$ if $|h(x)-h(y)| \le M|x-y|$ for all $x,y\in[0,T]$ (p. 13).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The arc flows, Wardrop equilibrium (2.1) and potential (2.6) are those of the published definition `KellyStochasticNetworks_Wardrop`. Paths are arbitrary non-empty 0/1 incidence columns rather than loop-free paths of a digraph; the results of this mission never use loop-freeness. Costs are functions $\mathbb R \to \mathbb R$ constrained only on $[0,\infty)$. $\mathcal C^*$ and $\tilde{\mathcal C}$ are `sInf`/`sSup` of real sets (on the game space the infimum is attained and all WE flows have the same cost, p. 11); $\min_{s'\in\mathcal S_k}\tau_{s'}(f)$ is the `sInf` of the finite non-empty set of path costs of pair $k$. The middle term of Dist is the `sSup` of the image of $A \times [0, \min\{T(d),T(d')\}]$, and $\|\cdot\|_\infty$ is Mathlib's sup norm on $\mathbb R^n$.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), pp. 10–16, §2.1–§3.2, G1–G4, (2.1), (2.5)–(2.7), Conditions 1–2, (3.1)–(3.3); Lipschitz continuity p. 13

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

namespace SensitivityPoA.Holder
open KellyStochasticNetworks

/-- The fixed combinatorial structure `(G, K, S)` (G1–G2, p. 10): `J` arcs, `R` paths, `Sd` O/D pairs,
the arc–path incidence `A j r` (`= 1` iff arc `j` lies on path `r`) and the O/D pair `s r` that path `r`
serves, so that `S_k = {r | s r = k}`. -/
structure Network where
  J : ℕ
  R : ℕ
  Sd : ℕ
  A : Fin J → Fin R → ℝ
  s : Fin R → Fin Sd

/-- The §2 model assumptions (G1–G2): 0/1 arc–path incidence, non-empty paths, a non-empty
set of O/D pairs, and at least one path for each pair. Condition 1 is imposed only from §3.1. -/
def Network.Basic (N : Network) : Prop :=
  (∀ j r, N.A j r = 0 ∨ N.A j r = 1) ∧
  (∀ r, ∃ j, N.A j r = 1) ∧
  0 < N.Sd ∧
  (∀ k, 0 < (Finset.univ.filter fun r => N.s r = k).card)

/-- Standing assumptions on the structure: 0/1 incidence, every path is a non-empty arc set (G2),
`K` is non-empty (G1), and Condition 1 (p. 14): every arc lies on some path and `|S_k| ≥ 2`. -/
def Network.Standing (N : Network) : Prop :=
  (∀ j r, N.A j r = 0 ∨ N.A j r = 1) ∧
  (∀ r, ∃ j, N.A j r = 1) ∧
  0 < N.Sd ∧
  (∀ j, ∃ r, N.A j r = 1) ∧
  (∀ k, 2 ≤ (Finset.univ.filter fun r => N.s r = k).card)

/-- A (generalized) game `Γ = (τ, d)` on the structure `N`: arc cost functions and a demand vector. -/
structure Game (N : Network) where
  τ : Fin N.J → ℝ → ℝ
  d : Fin N.Sd → ℝ

/-- Total demand `T(d) = ∑_k d_k` (G4). -/
def totalDemand {Sd : ℕ} (d : Fin Sd → ℝ) : ℝ := ∑ k, d k

/-- `C↑+(ℝ≥0)`: continuous, non-decreasing and non-negative on `[0, ∞)` (G3, (3.2)). -/
def IsCostFn (h : ℝ → ℝ) : Prop :=
  ContinuousOn h (Set.Ici 0) ∧ MonotoneOn h (Set.Ici 0) ∧ ∀ x, 0 ≤ x → 0 ≤ h x

/-- A generalized game: every cost function in `C↑+(ℝ≥0)` and every demand non-negative ((3.2)). -/
def Game.IsGeneralized {N : Network} (Γ : Game N) : Prop :=
  (∀ j, IsCostFn (Γ.τ j)) ∧ ∀ k, 0 ≤ Γ.d k

/-- Condition 2 (p. 14): `T(d) > 0` and `τ_a(x) > 0` for every arc and every `x ∈ (0, T(d)]`. -/
def Game.Condition2 {N : Network} (Γ : Game N) : Prop :=
  0 < totalDemand Γ.d ∧ ∀ j x, 0 < x → x ≤ totalDemand Γ.d → 0 < Γ.τ j x

/-- The game space `G(G, K, S)` (p. 15): generalized games satisfying Condition 2. -/
def gameSpace (N : Network) : Set (Game N) := {Γ | Γ.IsGeneralized ∧ Γ.Condition2}

variable {N : Network}

/-- `f` is a (path) flow of `Γ`: non-negative and `∑_{s ∈ S_k} f_s = d_k` for every pair `k`. -/
def IsFlow (Γ : Game N) (f : Fin N.R → ℝ) : Prop := f ∈ wardropFeasible N.s Γ.d

/-- Path cost `τ_s(f) = ∑_{a ∈ s} τ_a(f_a)`. -/
def pathCost (Γ : Game N) (f : Fin N.R → ℝ) (r : Fin N.R) : ℝ :=
  ∑ j, Γ.τ j (linkFlow N.A f j) * N.A j r

/-- `min_{s′ ∈ S_k} τ_{s′}(f)`, as the infimum of the finite set of path costs of pair `k`
(non-empty under `Network.Basic`). -/
noncomputable def minPathCost (Γ : Game N) (f : Fin N.R → ℝ) (k : Fin N.Sd) : ℝ :=
  sInf (pathCost Γ f '' {r | N.s r = k})

/-- Total cost `C(Γ, f) = ∑_a f_a τ_a(f_a)` (arc form, p. 11). -/
def cost (Γ : Game N) (f : Fin N.R → ℝ) : ℝ :=
  ∑ j, linkFlow N.A f j * Γ.τ j (linkFlow N.A f j)

/-- Wardrop equilibrium (2.1). -/
def IsWE (Γ : Game N) (f : Fin N.R → ℝ) : Prop :=
  IsWardropEquilibrium N.A N.s Γ.τ Γ.d f

/-- Social optimum: a flow of minimum total cost. -/
def IsSO (Γ : Game N) (f : Fin N.R → ℝ) : Prop :=
  IsFlow Γ f ∧ ∀ g, IsFlow Γ g → cost Γ f ≤ cost Γ g

/-- `ε`-approximate WE flow (2.7), arc form: `∑_a τ_a(f_a)(f_a − g_a) ≤ ε` for every flow `g`. -/
def IsApproxWE (Γ : Game N) (ε : ℝ) (f : Fin N.R → ℝ) : Prop :=
  IsFlow Γ f ∧ ∀ g, IsFlow Γ g →
    ∑ j, Γ.τ j (linkFlow N.A f j) * (linkFlow N.A f j - linkFlow N.A g j) ≤ ε

/-- The potential `Φ(Γ, f) = ∑_a ∫_0^{f_a} τ_a(x) dx` (2.6). -/
noncomputable def potential (Γ : Game N) (f : Fin N.R → ℝ) : ℝ :=
  wardropObjective N.A Γ.τ f

/-- SO cost `C∗(Γ)`: the infimum of the total cost over all flows. -/
noncomputable def SOCost (Γ : Game N) : ℝ := sInf (cost Γ '' {f | IsFlow Γ f})

/-- WE cost `C̃(Γ)`: the supremum (worst case) of the total cost over all WE flows. -/
noncomputable def WECost (Γ : Game N) : ℝ := sSup (cost Γ '' {f | IsWE Γ f})

/-- The price of anarchy `ρ(Γ) = C̃(Γ) / C∗(Γ)` (2.5). -/
noncomputable def PoA (Γ : Game N) : ℝ := WECost Γ / SOCost Γ

/-- Equivalence of games (3.1). -/
def Game.Equiv (Γ Γ' : Game N) : Prop :=
  Γ.d = Γ'.d ∧ ∀ j, ∀ x ∈ Set.Icc 0 (totalDemand Γ.d), Γ.τ j x = Γ'.τ j x

/-- The distance `Dist(Γ, Γ′)` (3.3): the maximum of `‖d − d′‖_∞`, the largest cost difference on
`A × [0, min{T(d), T(d′)}]`, and `‖τ(T(d)) − σ(T(d′))‖_∞` (Mathlib's norm on `Fin n → ℝ` is the sup norm). -/
noncomputable def gameDist (Γ Γ' : Game N) : ℝ :=
  max ‖Γ.d - Γ'.d‖
    (max (sSup ((fun p : Fin N.J × ℝ => |Γ.τ p.1 p.2 - Γ'.τ p.1 p.2|) ''
        (Set.univ ×ˢ Set.Icc 0 (min (totalDemand Γ.d) (totalDemand Γ'.d)))))
      ‖fun j => Γ.τ j (totalDemand Γ.d) - Γ'.τ j (totalDemand Γ'.d)‖)

/-- `h` is Lipschitz continuous on `[0, T]` with Lipschitz constant `M` (p. 13). -/
def LipOnIcc (h : ℝ → ℝ) (T M : ℝ) : Prop :=
  ∀ x ∈ Set.Icc 0 T, ∀ y ∈ Set.Icc 0 T, |h x - h y| ≤ M * |x - y|

end SensitivityPoA.Holder


