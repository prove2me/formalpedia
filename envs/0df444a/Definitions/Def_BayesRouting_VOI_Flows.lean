-- Prove2me | Definitions.Def_BayesRouting_VOI_Flows
-- name    : BayesRouting_VOI_Flows
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T14:45:17.455389+00:00
-- url     : https://prove2.me/theorems/6066f260-2665-4027-8b76-47ad25b50cd0
-- title:
--   Route-flow polytope $\mathcal F(\lambda)$, impact of information $\widehat J^i$, and equilibrium route flows $\mathcal F^*(\lambda)$
-- statement:
--   A route flow is a family $f=(f_r(t))_{r\in\mathcal R,\,t\in\mathcal T}$. The $\lambda$-independent constraints are
--
--   1. (14a) for every route $r$, population $i$, types $t^i,\tilde t^i\in\mathcal T^i$ and $t^{-i},\tilde t^{-i}\in\mathcal T^{-i}$: $f_r(t^i,t^{-i})-f_r(\tilde t^i,t^{-i})=f_r(t^i,\tilde t^{-i})-f_r(\tilde t^i,\tilde t^{-i})$;
--   2. (14b) $\sum_{r}f_r(t)=D$ for every $t$;
--   3. (14c) $f_r(t)\ge 0$.
--
--   The **impact of information** on population $i$ is
--
--   $$\widehat J^i(f)=D-\sum_{r\in\mathcal R}\min_{t^i\in\mathcal T^i}f_r(t^i,\widehat t^{-i}),$$
--
--   and the feasible route flows are
--
--   $$\mathcal F(\lambda)=\{f:\ f \text{ satisfies (14a)–(14c) and } \widehat J^i(f)\le\lambda^iD \text{ for all } i\in\mathcal I\ \text{(IIC)}\}.$$
--
--   The **equilibrium route flows** $\mathcal F^*(\lambda)$ are the route flows $f_r(t)=\sum_iq^i_r(t^i)$ induced by the BWE $q$ of $\Gamma(\lambda)$. For a set $C$ of route flows, $\operatorname{argmin}_C\widehat\Phi$ is the set of $f\in C$ with $\widehat\Phi(f)\le\widehat\Phi(g)$ for all $g\in C$.
--
--   These objects turn the equilibrium problem into convex programs over route flows, where the effect of the population sizes $\lambda$ is isolated in the (IIC) constraints.
--
--   **Formalization Note** $\widehat J^i(f)$ is taken as the maximum of the displayed expression over the reference profile $\widehat t$. On flows satisfying (14a) the expression does not depend on $\widehat t$ (the paper's (16)), and with the maximum the single inequality $\widehat J^i(f)\le\lambda^iD$ is exactly (14d) for all $t^{-i}$. In (14a) the profiles $t^{-i},\tilde t^{-i}$ are full profiles whose $i$-th entry is overwritten.
-- source:
--   Wu, Amin, Ozdaglar, Value of Information in Bayesian Routing Games, Oper. Res. 69(1) 2021, pp. 155-156, eqs. (14a)-(14d), (16), (IIC), (OPT-F) and the definition of F*(lambda)

import Mathlib
import Definitions.Def_BayesRouting_VOI_Game
import Definitions.Def_BayesRouting_VOI_Potential

open Finset

namespace BayesRouting.VOI

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

end BayesRouting.VOI


