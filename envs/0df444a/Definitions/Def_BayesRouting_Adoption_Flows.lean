-- Prove2me | Definitions.Def_BayesRouting_Adoption_Flows
-- name    : BayesRouting_Adoption_Flows
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T15:16:04.923206+00:00
-- url     : https://prove2.me/theorems/ec326ce5-73cf-48d6-b212-3b37203b4499
-- title:
--   Route-flow constraints (14a)-(14d), impact of information Ĵ^i, equilibrium route flows and argmin sets of Φ̂
-- statement:
--   Route flows $f=(f_r(t))_{r\in\mathcal R,t\in\mathcal T}$ of the Bayesian routing game are constrained by
--   $$f_r(t^i,t^{-i})-f_r(\tilde t^i,t^{-i})=f_r(t^i,\tilde t^{-i})-f_r(\tilde t^i,\tilde t^{-i})\quad\text{for all } r,\ i,\ t^i,\tilde t^i,\ t^{-i},\tilde t^{-i},\tag{14a}$$
--   $$\sum_{r\in\mathcal R}f_r(t)=D,\qquad f_r(t)\ge0\qquad\text{for all } r,\ t.\tag{14b–c}$$
--   The **impact of information** on population $i$ is
--   $$\widehat J^i(f)=\max_{\widehat t\in\mathcal T}\Big(D-\sum_{r\in\mathcal R}\min_{t^i\in\mathcal T^i}f_r(t^i,\widehat t^{-i})\Big),$$
--   and the **information impact constraint** (IIC) of population $i$ at size vector $\lambda$ is $\widehat J^i(f)\le\lambda^iD$. The polytope $\mathcal F(\lambda)$ consists of the route flows satisfying (14a)–(14c) and (IIC) for all $i$. The set $\mathcal F^*(\lambda)$ of **equilibrium route flows** consists of the route flows induced by BWE of $\Gamma(\lambda)$. For a set $C$ of route flows, the argmin set of $\widehat\Phi$ over $C$ is the set of $f\in C$ with $\widehat\Phi(f)\le\widehat\Phi(g)$ for all $g\in C$.
--
--   These are the objects of the route-flow formulation of the equilibrium, which the mission uses to describe the size-independent edge load.
--
--   **Formalization Note** The paper defines $\widehat J^i(f)$ by the bracket at an arbitrary reference profile $\widehat t$; on flows satisfying (14a) the bracket does not depend on $\widehat t$, so the maximum over $\widehat t$ used here equals the paper's value there, and $\widehat J^i(f)\le\lambda^iD$ is exactly the paper's constraint (14d) (a bound for every $t^{-i}$).
-- source:
--   Wu, Amin, Ozdaglar, Value of Information in Bayesian Routing Games, Oper. Res. 69(1) 2021, pp. 155-156, eqs. (14a)-(14d), (16), (IIC), and the definition of F*(λ) on p. 156

import Mathlib
import Definitions.Def_BayesRouting_Adoption_Game
import Definitions.Def_BayesRouting_Adoption_Potential

open Finset

namespace BayesRouting.Adoption

variable {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
  [∀ i, DecidableEq (T i)] {S E R : Type} [Fintype S] [Fintype E] [DecidableEq E] [Fintype R]

/-- The route-flow constraints (14a)–(14c) (p. 155), which do not depend on `λ`:
(14a) for every route `r`, population `i`, types `t^i, t̃^i` and profiles `t^{-i}, t̃^{-i}`,
`f_r(t^i, t^{-i}) - f_r(t̃^i, t^{-i}) = f_r(t^i, t̃^{-i}) - f_r(t̃^i, t̃^{-i})`
(the profiles `t, t'` stand for `t^{-i}, t̃^{-i}`; their `i`-th entry is overwritten);
(14b) `∑_r f_r(t) = D` for every `t`; (14c) `f_r(t) ≥ 0`. -/
def flowBase (G : Game I T S E R) : Set (R → ((i : I) → T i) → ℝ) :=
  {f | (∀ r i (ti ti' : T i) (t t' : (k : I) → T k),
        f r (Function.update t i ti) - f r (Function.update t i ti') =
          f r (Function.update t' i ti) - f r (Function.update t' i ti')) ∧
      (∀ t, ∑ r, f r t = G.D) ∧ (∀ r t, 0 ≤ f r t)}

/-- The impact of information `Ĵ^i(f)` (16) (p. 155), taken as the maximum over the reference
profile `t̂` of `D - ∑_r min_{t^i} f_r(t^i, t̂^{-i})`. On flows satisfying (14a) the expression
does not depend on `t̂`, so this is the paper's `Ĵ^i`, and `Ĵ^i(f) ≤ λ^i D` is exactly (14d). -/
noncomputable def impact [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) (i : I)
    (f : R → ((k : I) → T k) → ℝ) : ℝ :=
  univ.sup' univ_nonempty (fun t : (k : I) → T k =>
    G.D - ∑ r, univ.inf' univ_nonempty (fun ti : T i => f r (Function.update t i ti)))

/-- The polytope `ℱ(λ)` of route flows satisfying (14a)–(14d), with (14d) written as (IIC):
`Ĵ^i(f) ≤ λ^i D` for every population `i` (p. 155). -/
def feasibleFlows [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) (lam : I → ℝ) :
    Set (R → ((i : I) → T i) → ℝ) :=
  flowBase G ∩ {f | ∀ i, impact G i f ≤ lam i * G.D}

/-- The set `ℱ*(λ)` of equilibrium route flows (p. 156): route flows (3) induced by some BWE of
`Γ(λ)`. -/
def eqFlows (G : Game I T S E R) (lam : I → ℝ) : Set (R → ((i : I) → T i) → ℝ) :=
  {f | ∃ q, IsBWE G lam q ∧ f = routeFlow q}

/-- The set of minimizers of `Φ̂` over a set `C` of route flows (the optimal solution set of
`min Φ̂(f) s.t. f ∈ C`). -/
def flowArgmin (G : Game I T S E R) (C : Set (R → ((i : I) → T i) → ℝ)) :
    Set (R → ((i : I) → T i) → ℝ) :=
  {f | f ∈ C ∧ ∀ g ∈ C, flowPotential G f ≤ flowPotential G g}

end BayesRouting.Adoption


