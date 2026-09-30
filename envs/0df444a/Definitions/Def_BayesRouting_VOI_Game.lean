-- Prove2me | Definitions.Def_BayesRouting_VOI_Game
-- name    : BayesRouting_VOI_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T14:39:50.073722+00:00
-- url     : https://prove2.me/theorems/33955e41-da59-46dc-91da-8f1aaa4b1be5
-- title:
--   Bayesian routing game $\Gamma(\lambda)$: populations, types, common prior, routes, state-dependent costs, strategies, BWE and population costs
-- statement:
--   A **Bayesian routing game** (Wu, Amin, Ozdaglar, §3) is played on a network with a single origin–destination pair. Its data are:
--
--   1. a finite set $\mathcal I$ of traveler populations, one per traffic information system (TIS);
--   2. for each $i\in\mathcal I$ a finite, nonempty type space $\mathcal T^i$ (the signals TIS $i$ can send); a type profile is $t=(t^i)_{i\in\mathcal I}\in\mathcal T=\prod_i\mathcal T^i$;
--   3. a finite set $\mathcal S$ of network states, and a common prior $\pi\in\Delta(\mathcal S\times\mathcal T)$;
--   4. a finite set $\mathcal E$ of edges and a finite nonempty set $\mathcal R$ of routes, each route given by the set of edges it uses;
--   5. for every state $s$ and edge $e$ a cost function $c^s_e$ that is positive, strictly increasing and differentiable;
--   6. a total demand $D>0$.
--
--   For a size vector $\lambda$ ($\lambda^i\ge 0$, $\sum_i\lambda^i=1$), a strategy profile $q=(q^i_r(t^i))$ is **feasible**, $q\in\mathcal Q(\lambda)$, if
--
--   $$\sum_{r\in\mathcal R}q^i_r(t^i)=\lambda^iD,\qquad q^i_r(t^i)\ge 0 .$$
--
--   With $\Pr(t^i)=\sum_s\sum_{t^{-i}}\pi(s,t^i,t^{-i})$, the belief is $\beta^i(s,t^{-i}\mid t^i)=\pi(s,t^i,t^{-i})/\Pr(t^i)$. The route flow is $f_r(t)=\sum_i q^i_r(t^i)$, the edge load $w_e(t)=\sum_{r\ni e}f_r(t)$, and the expected cost of route $r$ for type $t^i$ is
--
--   $$\mathbb E[c_r(q)\mid t^i]=\sum_{s}\sum_{t^{-i}}\sum_{e\in r}\beta^i(s,t^{-i}\mid t^i)\,c^s_e\big(w_e(t^i,t^{-i})\big).$$
--
--   A feasible $q$ is a **Bayesian Wardrop equilibrium** (BWE) if $q^i_r(t^i)>0$ implies $\mathbb E[c_r(q)\mid t^i]\le\mathbb E[c_{r'}(q)\mid t^i]$ for all $r'$. The **population cost** of population $i$ at $q$ is
--
--   $$C^{i}(q)=\sum_{t^i\in\mathcal T^i}\Pr(t^i)\min_{r\in\mathcal R}\mathbb E[c_r(q)\mid t^i],$$
--
--   which at a BWE is the equilibrium population cost $C^{i*}(\lambda)$ of eq. (7).
--
--   These objects are the common vocabulary of every statement in the mission.
--
--   **Formalization Note** The game is a structure whose fields are the data and the paper's standing assumptions: $\pi\ge0$, $\sum\pi=1$, $D>0$, $c^s_e(z)>0$ for $z\ge0$, and $c^s_e$ strictly monotone and differentiable on all of $\mathbb R$ (any cost on $[0,\infty)$ with these properties extends). One assumption is **added**: every type profile has positive probability, $\sum_s\pi(s,t)>0$; it makes every $\Pr(t^i)>0$ (so beliefs are well defined) and is needed for the uniqueness of the equilibrium edge load. It excludes perfectly correlated signals (the paper's Example 2(i)). Routes are encoded by their edge sets; the directed-graph structure is not used by any statement. The belief is evaluated at a full type profile $t$ whose $i$-th entry is $t^i$; sums over $t^{-i}$ are sums over profiles with $t^i$ fixed. $C^{i*}$ is defined by the last expression of (7), which does not divide by $\lambda^iD$.
-- source:
--   Wu, Amin, Ozdaglar, Value of Information in Bayesian Routing Games, Oper. Res. 69(1) 2021, pp. 152-153, §3.1-3.2, eqs. (1a)-(7)

import Mathlib

open Finset

namespace BayesRouting.VOI

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
formalization; it is what makes the beliefs (2) well defined and the equilibrium edge load unique. -/
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

/-- The interim belief (2) (p. 153): `β^i(s, t^{-i} | t^i) = π(s, t^i, t^{-i}) / Pr(t^i)`. It is
evaluated at a full type profile `t`; it is meaningful when `t i = t^i`, which is the only way it
is used. -/
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
(the theorems evaluate it at a BWE). -/
noncomputable def popCost [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R)
    (q : (i : I) → T i → R → ℝ) (i : I) : ℝ :=
  ∑ ti, typeProb G i ti * univ.inf' univ_nonempty (fun r => expCost G q i ti r)

end BayesRouting.VOI


