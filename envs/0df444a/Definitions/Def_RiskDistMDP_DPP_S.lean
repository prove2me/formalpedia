-- Prove2me | Definitions.Def_RiskDistMDP_DPP_S
-- name    : RiskDistMDP_DPP_S
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:56:46.757389+00:00
-- url     : https://prove2.me/theorems/c5ea2828-42e8-4e48-9a0e-74b3bb3837c3
-- title:
--   Risk-averse Bellman operator $S_tv(x)=\inf_{\lambda\in\varpi_t(x)}G^\lambda_tv(x)$ (4.3)
-- statement:
--   For $t\in\mathbb N$ and $v\in\ell^\infty(\mathbb X,\mathcal B(\mathbb X))$,
--   $$S_tv(x):=\inf_{\lambda\in\varpi_t(x)}G^\lambda_tv(x)=\inf_{\lambda\in\varpi_t(x)}\sigma_{t,x}\big(\widetilde P^v_{t,x,\lambda}\big).$$
--   It is the Bellman operator of the risk-averse problem: the optimal value functions solve $J=S_tJ$.
--
--   **Formalization Note** The infimum is taken in `EReal`, a complete lattice, over exactly $\varpi_t(x)$.
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, (4.3), p. 18

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_G
import Definitions.Def_RiskDistMDP_DPP_MarkovPolicies

set_option autoImplicit false

namespace RiskDistMDP.DPP

/-- The risk-averse **Bellman operator** `S_t v(x) := inf_{λ∈ϖ_t(x)} G^λ_t v(x)` of
arXiv:2203.09612v4, (4.3), p.18, for `t ∈ ℕ`.

**Formalization Note** The infimum is taken in `EReal`, a complete lattice, over exactly
`ϖ_t(x)`; there is no junk value. -/
noncomputable def S {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸] (R : RiskMDP 𝕏 𝔸)
    (t : ℕ) (v : 𝕏 → ℝ) (x : 𝕏) : EReal :=
  ⨅ l ∈ varpi R.toBorelMDP t x, G R t l v x

end RiskDistMDP.DPP


