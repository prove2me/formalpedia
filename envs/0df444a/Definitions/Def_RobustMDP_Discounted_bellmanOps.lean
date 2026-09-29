-- Prove2me | Definitions.Def_RobustMDP_Discounted_bellmanOps
-- name    : RobustMDP_Discounted_bellmanOps
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:57:34.896987+00:00
-- url     : https://prove2.me/theorems/f4314d63-1669-40b5-948d-469efa65a02f
-- title:
--   The robust Bellman operator (29) and the robust policy-evaluation operator (30)
-- statement:
--   The **robust Bellman operator** $g : \mathbb R^n \to \mathbb R^n$ of (29) is
--   $$(g(v))_i := \min_{a \in \mathcal A} \big(c(i, a) + \nu\, \sigma_{\mathcal P_i^a}(v)\big), \qquad i \in \mathcal X.$$
--   For a stationary control policy $\pi = (\mathbf a, \mathbf a, \dots)$, the **robust policy-evaluation operator** $g_\pi$ of (30) is
--   $$(g_\pi(v))_i := c(i, \mathbf a(i)) + \nu\, \sigma_{\mathcal P_i^{\mathbf a(i)}}(v), \qquad i \in \mathcal X.$$
--
--   These are the right-hand sides of the optimality equation (19), the value iteration (20) and the evaluation equation (23) of Theorem 3.
--
--   **Formalization Note** The minimum over the finite nonempty action set is `Finset.inf'`. The paper prints $\sigma_{\mathcal P_i^{\mathbf a(i)}}(v^\pi)$ in (30), a slip for $\sigma_{\mathcal P_i^{\mathbf a(i)}}(v)$; the operator here is the corrected one.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 786, Eqs. (29)–(30); p. 785, Eqs. (19), (23)

import Mathlib
import Definitions.Def_RobustMDP_Discounted_Model
import Definitions.Def_RobustMDP_Shared_supportFunction

namespace RobustMDP.Discounted

/-- The robust Bellman operator `g` of (29) (p. 786), the right side of (19)/(20):
`(g(v))_i = min_{a ∈ 𝒜} (c(i, a) + ν σ_{𝒫_i^a}(v))`, a minimum over the finite nonempty
action set. -/
noncomputable def Model.bellmanOp {n : ℕ} {A : Type} [Fintype A] [Nonempty A] (M : Model n A)
    (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Finset.univ.inf' Finset.univ_nonempty
    (fun a => M.cost i a + M.discount * Shared.supportFunction (M.rows a i) v)

/-- The robust policy-evaluation operator of (30) (p. 786), the right side of (23), for a
stationary policy `π = (𝐚, 𝐚, …)`: `(g(v))_i = c(i, 𝐚(i)) + ν σ_{𝒫_i^{𝐚(i)}}(v)`. -/
noncomputable def Model.policyOp {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A)
    (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => M.cost i (π i) + M.discount * Shared.supportFunction (M.rows (π i) i) v

end RobustMDP.Discounted


