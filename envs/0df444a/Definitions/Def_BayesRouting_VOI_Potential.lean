-- Prove2me | Definitions.Def_BayesRouting_VOI_Potential
-- name    : BayesRouting_VOI_Potential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T14:42:59.150774+00:00
-- url     : https://prove2.me/theorems/52a3c45c-b2dd-4c4f-a3e3-731d0ce72f89
-- title:
--   Weighted potential $\Phi$, its route-flow and edge-load forms $\widehat\Phi$, $\check\Phi$, and the equilibrium potential value $\Psi(\lambda)$
-- statement:
--   In the Bayesian routing game, the **weighted potential** of a strategy profile $q$ is
--
--   $$\Phi(q)=\sum_{s\in\mathcal S}\sum_{e\in\mathcal E}\sum_{t\in\mathcal T}\pi(s,t)\int_0^{\sum_{r\ni e}\sum_{i\in\mathcal I}q^i_r(t^i)}c^s_e(z)\,dz .$$
--
--   The same expression written in terms of a route flow $f=(f_r(t))$ or an edge load $w=(w_e(t))$ is
--
--   $$\widehat\Phi(f)=\sum_{s}\sum_{e}\sum_{t}\pi(s,t)\int_0^{\sum_{r\ni e}f_r(t)}c^s_e(z)\,dz,\qquad \check\Phi(w)=\sum_{s}\sum_{e}\sum_{t}\pi(s,t)\int_0^{w_e(t)}c^s_e(z)\,dz .$$
--
--   The **equilibrium potential value** is the optimal value of $\min\{\Phi(q): q\in\mathcal Q(\lambda)\}$ (problem (OPT-$\mathcal Q$)):
--
--   $$\Psi(\lambda)=\inf_{q\in\mathcal Q(\lambda)}\Phi(q).$$
--
--   Finally, for a profile $q$, a coordinate $(i,t^i,r)$ and a number $x$, $q[(i,t^i,r)\mapsto x]$ denotes $q$ with $q^i_r(t^i)$ replaced by $x$; it is used to state partial derivatives of $\Phi$.
--
--   $\Phi$ is the function whose minimizers over $\mathcal Q(\lambda)$ are the equilibria, and $\Psi$ is the function whose directional derivatives give the relative value of information.
--
--   **Formalization Note** The integrals are interval integrals of the continuous costs. $\Psi$ is an `sInf` of the image of $\Phi$ on $\mathcal Q(\lambda)$. For $\lambda$ in the simplex this set is nonempty and compact, so the infimum is the minimum; for a $\lambda$ with a negative entry $\mathcal Q(\lambda)$ is empty and Lean's value is the junk $0$. Every statement therefore keeps $\lambda$ (and each perturbed $\lambda$) in the simplex.
-- source:
--   Wu, Amin, Ozdaglar, Value of Information in Bayesian Routing Games, Oper. Res. 69(1) 2021, p. 154, eqs. (9)-(11), (OPT-Q) and the definition of Psi(lambda)

import Mathlib
import Definitions.Def_BayesRouting_VOI_Game

open Finset

namespace BayesRouting.VOI

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

/-- The potential (11) as a function of an edge load (p. 154):
`Φ̌(w) = ∑_s ∑_e ∑_t π(s, t) ∫_0^{w_e(t)} c^s_e(z) dz`. -/
noncomputable def loadPotential (G : Game I T S E R) (w : E → ((i : I) → T i) → ℝ) : ℝ :=
  ∑ s, ∑ e, ∑ t, G.prior s t * ∫ z in (0 : ℝ)..(w e t), G.cost s e z

/-- `Ψ(λ)`, the optimal value of (OPT-𝒬) (p. 154): the infimum of `Φ` over `𝒬(λ)`. For `λ` in
the simplex the feasible set is nonempty and compact, so the infimum is attained; for a `λ` with
a negative entry the set is empty and Lean's `sInf ∅ = 0` is a junk value, which is why every
statement keeps `λ` in the simplex. -/
noncomputable def eqPotential (G : Game I T S E R) (lam : I → ℝ) : ℝ :=
  sInf (potential G '' feasibleStrategies G lam)

/-- The strategy profile `q` with the single coordinate `q^i_r(t^i)` replaced by `x`. -/
def setCoord [DecidableEq R] (q : (i : I) → T i → R → ℝ) (i : I) (ti : T i) (r : R) (x : ℝ) :
    (k : I) → T k → R → ℝ :=
  Function.update q i (Function.update (q i) ti (Function.update (q i ti) r x))

end BayesRouting.VOI


