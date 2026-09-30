-- Prove2me | Definitions.Def_BayesRouting_Adoption_Potential
-- name    : BayesRouting_Adoption_Potential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T15:14:17.436342+00:00
-- url     : https://prove2.me/theorems/28630b61-8992-4be5-8e71-45fcafcbcb67
-- title:
--   Weighted potential Φ, its route-flow form Φ̂, and the equilibrium potential Ψ(λ)
-- statement:
--   In the Bayesian routing game $\Gamma(\lambda)$, the **weighted potential** of a strategy profile $q$ is
--   $$\Phi(q)=\sum_{s\in\mathcal S}\sum_{e\in\mathcal E}\sum_{t\in\mathcal T}\pi(s,t)\int_0^{\sum_{r\ni e}\sum_{i\in\mathcal I}q^i_r(t^i)}c^s_e(z)\,dz,$$
--   and the same expression written for a route flow $f$ is
--   $$\widehat\Phi(f)=\sum_{s\in\mathcal S}\sum_{e\in\mathcal E}\sum_{t\in\mathcal T}\pi(s,t)\int_0^{\sum_{r\ni e}f_r(t)}c^s_e(z)\,dz.$$
--   The **equilibrium potential** $\Psi(\lambda)$ is the optimal value of $\min\,\Phi(q)$ subject to $q\in\mathcal Q(\lambda)$.
--
--   $\Psi$ is the function whose minimizers the mission identifies with the equilibrium adoption rates.
--
--   **Formalization Note** The integrals are interval integrals of the continuous costs. $\Psi(\lambda)$ is the infimum of $\Phi$ over $\mathcal Q(\lambda)$; for $\lambda$ in the probability simplex the feasible set is nonempty and compact, so the infimum is the paper's minimum. For a $\lambda$ outside the simplex with a negative entry the feasible set is empty and the infimum takes Lean's default value $0$; every statement therefore evaluates $\Psi$ only at size vectors in the simplex.
-- source:
--   Wu, Amin, Ozdaglar, Value of Information in Bayesian Routing Games, Oper. Res. 69(1) 2021, p. 154, Lemma 1 eq. (9), eq. (10), and the definition of Ψ(λ) after Theorem 1

import Mathlib
import Definitions.Def_BayesRouting_Adoption_Game

open Finset

namespace BayesRouting.Adoption

variable {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
  [∀ i, DecidableEq (T i)] {S E R : Type} [Fintype S] [Fintype E] [DecidableEq E] [Fintype R]

/-- The weighted potential (9) (Lemma 1, p. 154):
`Φ(q) = ∑_s ∑_e ∑_t π(s, t) ∫_0^{∑_{r∋e} ∑_i q^i_r(t^i)} c^s_e(z) dz`. -/
noncomputable def potential (G : Game I T S E R) (q : (i : I) → T i → R → ℝ) : ℝ :=
  ∑ s, ∑ e, ∑ t, G.prior s t * ∫ z in (0 : ℝ)..(edgeLoad G q e t), G.cost s e z

/-- The potential (10) as a function of a route flow (p. 154):
`Φ̂(f) = ∑_s ∑_e ∑_t π(s, t) ∫_0^{∑_{r∋e} f_r(t)} c^s_e(z) dz`. -/
noncomputable def flowPotential (G : Game I T S E R) (f : R → ((i : I) → T i) → ℝ) : ℝ :=
  ∑ s, ∑ e, ∑ t, G.prior s t * ∫ z in (0 : ℝ)..(flowLoad G f e t), G.cost s e z

/-- `Ψ(λ)`, the optimal value of (OPT-𝒬) (p. 154): the infimum of `Φ` over `𝒬(λ)`. For `λ` in
the simplex the feasible set is nonempty and compact, so the infimum is attained; for a `λ` with
a negative entry the set is empty and Lean's `sInf ∅ = 0` is a junk value, which is why every
statement keeps the `λ` at which `Ψ` is evaluated in the simplex. -/
noncomputable def eqPotential (G : Game I T S E R) (lam : I → ℝ) : ℝ :=
  sInf (potential G '' feasibleStrategies G lam)

end BayesRouting.Adoption


