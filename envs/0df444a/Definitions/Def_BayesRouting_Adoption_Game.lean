-- Prove2me | Definitions.Def_BayesRouting_Adoption_Game
-- name    : BayesRouting_Adoption_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T15:12:54.289266+00:00
-- url     : https://prove2.me/theorems/f55d5020-8819-42fd-925b-4263a09a4ffc
-- title:
--   Bayesian routing game Γ(λ): populations, type spaces, common prior, routes, costs, BWE and population costs
-- statement:
--   This file sets up the **Bayesian routing game** of Wu, Amin and Ozdaglar for a single origin–destination pair.
--
--   **Data.** A finite set $\mathcal I$ of traveler populations, one per traffic information system (TIS); for each $i\in\mathcal I$ a finite nonempty type space $\mathcal T^i$ (the signals population $i$ may receive), with type profiles $t=(t^i)_{i\in\mathcal I}\in\mathcal T=\prod_i\mathcal T^i$; a finite set $\mathcal S$ of network states; a finite set $\mathcal E$ of edges and a finite nonempty set $\mathcal R$ of routes, each route $r$ given by the set of edges it uses; a common prior $\pi\in\Delta(\mathcal S\times\mathcal T)$; state-dependent edge costs $c^s_e:\mathbb R\to\mathbb R$; and a total demand $D$. The standing assumptions are part of the object: $\pi(s,t)\ge0$ and $\sum_{s,t}\pi(s,t)=1$; $D>0$; each $c^s_e$ is positive on loads $z\ge0$, strictly increasing and differentiable; and every type profile has positive probability, $\sum_s\pi(s,t)>0$.
--
--   **Strategies.** For a size vector $\lambda=(\lambda^i)_{i\in\mathcal I}$, a strategy profile $q=(q^i_r(t^i))$ is feasible, $q\in\mathcal Q(\lambda)$, if
--   $$\sum_{r\in\mathcal R}q^i_r(t^i)=\lambda^iD,\qquad q^i_r(t^i)\ge0\qquad\text{for all } i,\ t^i,\ r.$$
--
--   **Beliefs, flows, loads, costs.** $\Pr(t^i)=\sum_s\sum_{t^{-i}}\pi(s,t^i,t^{-i})$ and $\beta^i(s,t^{-i}\mid t^i)=\pi(s,t^i,t^{-i})/\Pr(t^i)$. The route flow is $f_r(t)=\sum_iq^i_r(t^i)$ and the edge load $w_e(t)=\sum_{r\ni e}\sum_iq^i_r(t^i)$ (also $w_e(t)=\sum_{r\ni e}f_r(t)$ for a route flow $f$). The expected cost of route $r$ for population $i$ of type $t^i$ is
--   $$\mathbb E[c_r(q)\mid t^i]=\sum_{s\in\mathcal S}\sum_{t^{-i}}\sum_{e\in r}\beta^i(s,t^{-i}\mid t^i)\,c^s_e\big(w_e(t^i,t^{-i})\big).$$
--
--   **Equilibrium.** $q\in\mathcal Q(\lambda)$ is a **Bayesian Wardrop equilibrium (BWE)** of $\Gamma(\lambda)$ if $q^i_r(t^i)>0$ implies $\mathbb E[c_r(q)\mid t^i]\le\mathbb E[c_{r'}(q)\mid t^i]$ for every $r'$. The equilibrium population cost of population $i$ is
--   $$C^{i*}=\sum_{t^i\in\mathcal T^i}\Pr(t^i)\,\min_{r\in\mathcal R}\mathbb E[c_r(q)\mid t^i],$$
--   evaluated at a BWE $q$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Routes are edge sets (the results use the network only through route–edge incidence). Monotonicity and differentiability of the costs are required on all of $\mathbb R$, which loses no generality. The positivity of every type profile's probability is an assumption added to the paper's model: without it the equilibrium edge load need not be unique (a zero-probability profile's load does not affect any cost), and it makes the beliefs well defined; it excludes the paper's Example 2(i). The population cost is the last form of the paper's (7), which has no division by $\lambda^iD$ and is therefore the cost of an individual subscriber also when $\lambda^i=0$. The size vector is not a field; theorems take it as an argument.
-- source:
--   Wu, Amin, Ozdaglar, Value of Information in Bayesian Routing Games, Oper. Res. 69(1) 2021, pp. 152-153, §3.1-3.2, eqs. (1a)-(7)

import Mathlib

open Finset

namespace BayesRouting.Adoption

/-- The Bayesian routing game `Γ` of Wu, Amin, Ozdaglar (Oper. Res. 69(1) 2021, §3.1–3.2,
pp. 152–153), for a single origin–destination pair.

* `I` : populations (one per traffic information system, TIS);
* `T i` : the finite type space of population `i`; a type profile is `t : (i : I) → T i`;
* `S` : finite set of network states; `E` : edges; `R` : routes, each route given by its edge set
  `route r` (the results use the network only through this route–edge incidence);
* `prior s t = π(s, t)` : the common prior on states and type profiles;
* `cost s e` : the state-dependent edge cost `c^s_e`;
* `D` : the total demand.

The standing assumptions of the paper are fields: `π` is a probability distribution, `D > 0`,
each `c^s_e` is positive on loads `≥ 0`, strictly increasing and differentiable. The field
`prior_full_support` (every type profile has positive probability) is an assumption added by the
formalization; it makes the beliefs (2) well defined and the equilibrium edge load unique. -/
structure Game (I : Type) (T : I → Type) (S E R : Type) [Fintype I] [DecidableEq I]
    [∀ i, Fintype (T i)] [Fintype S] [Fintype E] [Fintype R] where
  /-- The common prior `π(s, t)`. -/
  prior : S → ((i : I) → T i) → ℝ
  /-- The state-dependent edge cost functions `c^s_e`. -/
  cost : S → E → ℝ → ℝ
  /-- The set of edges of each route. -/
  route : R → Finset E
  /-- The total demand `D`. -/
  D : ℝ
  prior_nonneg : ∀ s t, 0 ≤ prior s t
  prior_sum_one : ∑ s, ∑ t, prior s t = 1
  prior_full_support : ∀ t, 0 < ∑ s, prior s t
  D_pos : 0 < D
  cost_pos : ∀ s e z, 0 ≤ z → 0 < cost s e z
  cost_strictMono : ∀ s e, StrictMono (cost s e)
  cost_diff : ∀ s e, Differentiable ℝ (cost s e)

variable {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
  [∀ i, DecidableEq (T i)] {S E R : Type} [Fintype S] [Fintype E] [DecidableEq E] [Fintype R]

/-- The feasible strategy profiles `𝒬(λ)`, constraints (1a)–(1b) (p. 153): population `i` of type
`t^i` routes `q^i_r(t^i) ≥ 0` on route `r`, and `∑_r q^i_r(t^i) = λ^i D`. -/
def feasibleStrategies (G : Game I T S E R) (lam : I → ℝ) : Set ((i : I) → T i → R → ℝ) :=
  {q | (∀ i ti, ∑ r, q i ti r = lam i * G.D) ∧ ∀ i ti r, 0 ≤ q i ti r}

/-- `Pr(t^i) = ∑_s ∑_{t^{-i}} π(s, t^i, t^{-i})` (p. 153): the sum over all type profiles `t`
with `t i = t^i`. -/
def typeProb (G : Game I T S E R) (i : I) (ti : T i) : ℝ :=
  ∑ s, ∑ t ∈ univ.filter (fun t : (k : I) → T k => t i = ti), G.prior s t

/-- The interim belief (2) (p. 153): `β^i(s, t^{-i} | t^i) = π(s, t^i, t^{-i}) / Pr(t^i)`,
evaluated at a full type profile `t` with `t i = t^i` (the only way it is used). -/
noncomputable def belief (G : Game I T S E R) (i : I) (ti : T i) (s : S)
    (t : (k : I) → T k) : ℝ :=
  G.prior s t / typeProb G i ti

/-- The route flow (3) induced by a strategy profile: `f_r(t) = ∑_i q^i_r(t^i)`. -/
def routeFlow (q : (i : I) → T i → R → ℝ) : R → ((i : I) → T i) → ℝ :=
  fun r t => ∑ i, q i (t i) r

/-- The edge load of a route flow, `w_e(t) = ∑_{r ∋ e} f_r(t)` (second form of (4)). -/
def flowLoad (G : Game I T S E R) (f : R → ((i : I) → T i) → ℝ) : E → ((i : I) → T i) → ℝ :=
  fun e t => ∑ r ∈ univ.filter (fun r => e ∈ G.route r), f r t

/-- The edge load (4) induced by a strategy profile: `w_e(t) = ∑_{r ∋ e} ∑_i q^i_r(t^i)`. -/
def edgeLoad (G : Game I T S E R) (q : (i : I) → T i → R → ℝ) : E → ((i : I) → T i) → ℝ :=
  fun e t => ∑ r ∈ univ.filter (fun r => e ∈ G.route r), ∑ i, q i (t i) r

/-- The expected cost (5) of route `r` for population `i` of type `t^i`:
`𝔼[c_r(q) | t^i] = ∑_s ∑_{t^{-i}} ∑_{e ∈ r} β^i(s, t^{-i} | t^i) c^s_e(w_e(t^i, t^{-i}))`. -/
noncomputable def expCost (G : Game I T S E R) (q : (i : I) → T i → R → ℝ) (i : I) (ti : T i)
    (r : R) : ℝ :=
  ∑ s, ∑ t ∈ univ.filter (fun t : (k : I) → T k => t i = ti), ∑ e ∈ G.route r,
    belief G i ti s t * G.cost s e (edgeLoad G q e t)

/-- Bayesian Wardrop equilibrium (6) (p. 153): a feasible profile in which every type of every
population uses only routes of minimal expected cost. -/
def IsBWE (G : Game I T S E R) (lam : I → ℝ) (q : (i : I) → T i → R → ℝ) : Prop :=
  q ∈ feasibleStrategies G lam ∧
    ∀ i ti r, 0 < q i ti r → ∀ r', expCost G q i ti r ≤ expCost G q i ti r'

/-- The equilibrium population cost (7), last form (p. 153):
`C^{i*} = ∑_{t^i} Pr(t^i) min_r 𝔼[c_r(q) | t^i]`, evaluated at a strategy profile `q`
(the theorems evaluate it at a BWE). This form has no division by `λ^i D`, so it is the cost of
an individual traveler of population `i` also when `λ^i = 0`. -/
noncomputable def popCost [Nonempty R] (G : Game I T S E R)
    (q : (i : I) → T i → R → ℝ) (i : I) : ℝ :=
  ∑ ti, typeProb G i ti * univ.inf' univ_nonempty (fun r => expCost G q i ti r)

end BayesRouting.Adoption


