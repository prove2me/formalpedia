-- Prove2me | Definitions.Def_NetworkPricing_Caps_Model
-- name    : NetworkPricing_Caps_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:53.278364+00:00
-- url     : https://prove2.me/theorems/cf08fa6d-1e1d-4138-a75f-4ff6af91e2b8
-- title:
--   §2, pp. 4–6 — elastic-demand routing instance, potential (1), Wardrop flow, social welfare, optimal flow, marginal tolls, profits, capped (strong) Nash equilibria, Definition 1
-- statement:
--   This file sets up the regulated network pricing game of Correa, Guzmán, Lianeas, Nikolova and Schröder (§2 and Definition 1).
--
--   **Network and demand.** There are links $e \in E$, routes $P$ and commodities $k \in K$. Each route $P$ is the set of links $e$ with $A_{eP} = 1$, where $A$ is a $0/1$ link–route incidence matrix, and serves one commodity; $\mathcal P^k$ is the set of routes of commodity $k$. Commodity $k$ has a maximum demand $r_k \ge 0$ and a utility function $u_k : [0, r_k] \to \mathbb R_+$, nonincreasing and continuous; its aggregate utility is $U_k(y) = \int_0^y u_k(s)\,ds$. Each link has a latency function $\ell_e : \mathbb R_+ \to \mathbb R_+$, nondecreasing and convex on $[0,\infty)$ and differentiable.
--
--   **Flows.** A flow is a nonnegative route-flow vector $x = (x_P)_P$ with $r^k_x = \sum_{P \in \mathcal P^k} x_P \le r_k$ for every $k$; $X$ is the set of flows, and $x_e = \sum_{P \ni e} x_P$ is the flow on link $e$.
--
--   **Wardrop flows.** For a toll vector $t = (t_e)_e$, a Wardrop flow is a maximizer over $X$ of the potential
--
--   $$
--   \Phi_t(x) = \sum_{k \in K} U_k(r^k_x) - \sum_{e \in E} \int_0^{x_e} \big(\ell_e(y) + t_e\big)\,dy. \qquad (1)
--   $$
--
--   The instance has **unique Wardrop flows** if for every $t \ge 0$ all maximizers of (1) have the same link flows.
--
--   **Welfare and optimal tolls.** The social welfare is $SW(x) = \sum_k U_k(r^k_x) - \sum_e \ell_e(x_e)\,x_e$; an optimal flow $x^*$ maximizes it over $X$. The marginal tolls of $x^*$ are $\hat t_e = x^*_e\,\ell_e'(x^*_e)$. Given a selection $t \mapsto x(t)$ of Wardrop flows, a toll vector $\bar t \ge 0$ is **optimal** if $x(\bar t)$ has the link flows of an optimal flow.
--
--   **Operators' game.** Operator $e$ earns $\pi_e(t) = t_e\,x_e(t)$. With caps $\bar t$, the strategy of operator $e$ is $s_e \in [0, \bar t_e]$.
--
--   1. $t$ is a **Nash equilibrium with caps $\bar t$** if $0 \le t \le \bar t$ and for every $e$ and $s_e \in [0, \bar t_e]$, $\pi_e(s_e, t_{-e}) \le \pi_e(t)$.
--   2. $t$ is a **strong Nash equilibrium with caps $\bar t$** if $0 \le t \le \bar t$ and for no nonempty coalition $E^\Delta$ is there a $t'$ with $0 \le t' \le \bar t$, $t'_e = t_e$ for $e \notin E^\Delta$, and $\pi_e(t') > \pi_e(t)$ for all $e \in E^\Delta$.
--   3. (Definition 1a) $\bar t \ge 0$ is a **(strong) cap equilibrium** if $\bar t$ is the unique (strong) Nash equilibrium of the game with caps $\bar t$.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** Routes are an abstract finite route system with 0/1 incidence (the paper's $o_k$–$d_k$ paths are an instance). Latencies and utilities are functions on $\mathbb R$ constrained only on $[0,\infty)$ and $[0, r_k]$; "smooth" is read as differentiable on $\mathbb R$, and $\ell'_e$ is Lean's `deriv`. The Wardrop flow $x(t)$ is not defined here: theorems take a selection `flow` of maximizers of (1) for $t \ge 0$ as a hypothesis. Coalitions in the strong-Nash notion are nonempty: with $E^\Delta = \emptyset$ the page's formula fails for every profile.
-- source:
--   Correa, Guzmán, Lianeas, Nikolova & Schröder, Network Pricing: How to Induce Optimal Flows Under Strategic Link Operators, Operations Research (Articles in Advance, 2021), doi:10.1287/opre.2020.2067, §2.1–2.2 and Definition 1, pp. 4–6, display (1)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

namespace NetworkPricing.Caps

open KellyStochasticNetworks

/-- An instance of the network pricing game (§2.1, p. 5): links `Fin J`, routes `Fin R`,
commodities `Fin Sd`; `A e q = 1` iff link `e` lies on route `q`; route `q` serves commodity
`com q`; `r k` is the maximum demand of commodity `k`, `u k` its utility (reservation value)
function, and `ℓ e` the latency function of link `e`. -/
structure Instance (J R Sd : ℕ) where
  A : Fin J → Fin R → ℝ
  com : Fin R → Fin Sd
  r : Fin Sd → ℝ
  u : Fin Sd → ℝ → ℝ
  ℓ : Fin J → ℝ → ℝ

variable {J R Sd : ℕ}

/-- Standing assumptions of §2.1, p. 5: 0/1 incidence; `r_k ≥ 0`; `u_k : [0, r_k] → ℝ₊`
nonincreasing and continuous; `ℓ_e : ℝ₊ → ℝ₊` nondecreasing and convex on `[0, ∞)`, and
differentiable ("smooth"). -/
def Instance.Standing (I : Instance J R Sd) : Prop :=
  (∀ e q, I.A e q = 0 ∨ I.A e q = 1) ∧
  (∀ k, 0 ≤ I.r k) ∧
  (∀ k, AntitoneOn (I.u k) (Set.Icc 0 (I.r k))) ∧
  (∀ k, ContinuousOn (I.u k) (Set.Icc 0 (I.r k))) ∧
  (∀ k y, y ∈ Set.Icc 0 (I.r k) → 0 ≤ I.u k y) ∧
  (∀ e, MonotoneOn (I.ℓ e) (Set.Ici 0)) ∧
  (∀ e, ConvexOn ℝ (Set.Ici 0) (I.ℓ e)) ∧
  (∀ e, Differentiable ℝ (I.ℓ e)) ∧
  (∀ e y, 0 ≤ y → 0 ≤ I.ℓ e y)

/-- The amount `r^k_x = ∑_{P ∈ P^k} x_P` of commodity `k` routed by the route flow `f`. -/
def Instance.demand (I : Instance J R Sd) (f : Fin R → ℝ) (k : Fin Sd) : ℝ :=
  ∑ q ∈ Finset.univ.filter (fun q => I.com q = k), f q

/-- The set `X` of flows (§2.1.1): nonnegative route flows routing at most `r_k` of each
commodity `k`. -/
def Instance.Feasible (I : Instance J R Sd) (f : Fin R → ℝ) : Prop :=
  (∀ q, 0 ≤ f q) ∧ ∀ k, I.demand f k ≤ I.r k

/-- The aggregate utility `U_k(y) = ∫_0^y u_k(s) ds`. -/
noncomputable def Instance.U (I : Instance J R Sd) (k : Fin Sd) (y : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..y, I.u k s

/-- The objective of (1): `∑_k U_k(r^k_x) − ∑_e ∫_0^{x_e} (ℓ_e(y) + t_e) dy`. -/
noncomputable def Instance.potential (I : Instance J R Sd) (t : Fin J → ℝ)
    (f : Fin R → ℝ) : ℝ :=
  ∑ k, I.U k (I.demand f k) - ∑ e, ∫ y in (0:ℝ)..(linkFlow I.A f e), (I.ℓ e y + t e)

/-- `f` is a Wardrop flow under tolls `t`: a maximizer of (1) over `X`. -/
def Instance.IsWardropFlow (I : Instance J R Sd) (t : Fin J → ℝ) (f : Fin R → ℝ) : Prop :=
  I.Feasible f ∧ ∀ g, I.Feasible g → I.potential t g ≤ I.potential t f

/-- The uniqueness assumption of §2.1.2: for every toll vector `t ≥ 0`, all maximizers of (1)
have the same link flows. -/
def Instance.UniqueWardrop (I : Instance J R Sd) : Prop :=
  ∀ t : Fin J → ℝ, 0 ≤ t → ∀ f g, I.IsWardropFlow t f → I.IsWardropFlow t g →
    linkFlow I.A f = linkFlow I.A g

/-- Social welfare `SW(x, u) = ∑_k U_k(r^k_x) − ∑_e ℓ_e(x_e) x_e`. -/
noncomputable def Instance.socialWelfare (I : Instance J R Sd) (f : Fin R → ℝ) : ℝ :=
  ∑ k, I.U k (I.demand f k) - ∑ e, I.ℓ e (linkFlow I.A f e) * linkFlow I.A f e

/-- An optimal flow: a flow in `X` maximizing the social welfare over `X`. -/
def Instance.IsOptimalFlow (I : Instance J R Sd) (f : Fin R → ℝ) : Prop :=
  I.Feasible f ∧ ∀ g, I.Feasible g → I.socialWelfare g ≤ I.socialWelfare f

/-- The marginal toll `t̂_e = x*_e ℓ'_e(x*_e)` of the flow `fstar`. -/
noncomputable def Instance.marginalToll (I : Instance J R Sd) (fstar : Fin R → ℝ)
    (e : Fin J) : ℝ :=
  linkFlow I.A fstar e * deriv (I.ℓ e) (linkFlow I.A fstar e)

/-- `tbar` is an optimal toll vector: it is nonnegative and the Wardrop flow `flow tbar` it
induces has the link flows of the optimal flow `fstar`. -/
def Instance.IsOptimalToll (I : Instance J R Sd) (flow : (Fin J → ℝ) → Fin R → ℝ)
    (fstar : Fin R → ℝ) (tbar : Fin J → ℝ) : Prop :=
  0 ≤ tbar ∧ I.IsOptimalFlow fstar ∧ linkFlow I.A (flow tbar) = linkFlow I.A fstar

/-- The profit `π_e(t) = t_e x_e(t)` of the operator of link `e`, where `x(t) = flow t`. -/
noncomputable def Instance.profit (I : Instance J R Sd) (flow : (Fin J → ℝ) → Fin R → ℝ)
    (t : Fin J → ℝ) (e : Fin J) : ℝ :=
  t e * linkFlow I.A (flow t) e

/-- `t` lies in the capped strategy space: `0 ≤ t_e ≤ t̄_e` for every link `e`. -/
def InCaps (tbar t : Fin J → ℝ) : Prop :=
  0 ≤ t ∧ t ≤ tbar

/-- `t` is a Nash equilibrium of the game with caps `tbar`: each `t_e` is a best response
over `s_e ∈ [0, t̄_e]`. -/
def Instance.IsCappedNash (I : Instance J R Sd) (flow : (Fin J → ℝ) → Fin R → ℝ)
    (tbar t : Fin J → ℝ) : Prop :=
  InCaps tbar t ∧ ∀ e s, 0 ≤ s → s ≤ tbar e →
    I.profit flow (Function.update t e s) e ≤ I.profit flow t e

/-- `t` is a strong Nash equilibrium of the game with caps `tbar`: no nonempty coalition `D`
has a capped joint deviation `t'` (changing only coordinates in `D`) that strictly increases
the profit of every member of `D`. -/
def Instance.IsCappedStrongNash (I : Instance J R Sd) (flow : (Fin J → ℝ) → Fin R → ℝ)
    (tbar t : Fin J → ℝ) : Prop :=
  InCaps tbar t ∧ ∀ D : Finset (Fin J), D.Nonempty → ∀ t', InCaps tbar t' →
    (∀ e ∉ D, t' e = t e) → ¬ ∀ e ∈ D, I.profit flow t e < I.profit flow t' e

/-- Definition 1a: `tbar ≥ 0` is a cap equilibrium if `tbar` is the unique Nash equilibrium
of the game with caps `tbar`. -/
def Instance.IsCapEquilibrium (I : Instance J R Sd) (flow : (Fin J → ℝ) → Fin R → ℝ)
    (tbar : Fin J → ℝ) : Prop :=
  0 ≤ tbar ∧ I.IsCappedNash flow tbar tbar ∧ ∀ t, I.IsCappedNash flow tbar t → t = tbar

/-- Definition 1a (strong): `tbar ≥ 0` is a strong cap equilibrium if `tbar` is the unique
strong Nash equilibrium of the game with caps `tbar`. -/
def Instance.IsStrongCapEquilibrium (I : Instance J R Sd) (flow : (Fin J → ℝ) → Fin R → ℝ)
    (tbar : Fin J → ℝ) : Prop :=
  0 ≤ tbar ∧ I.IsCappedStrongNash flow tbar tbar ∧
    ∀ t, I.IsCappedStrongNash flow tbar t → t = tbar

end NetworkPricing.Caps


