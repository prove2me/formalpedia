-- Prove2me | Definitions.Def_RiskDistMDP_DPP_argminSet
-- name    : RiskDistMDP_DPP_argminSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:56:26.398196+00:00
-- url     : https://prove2.me/theorems/8de3f8c0-2060-4343-9a0e-05f8a54a57b2
-- title:
--   Minimizing randomized actions $\operatorname{argmin}_{\lambda\in\varpi_t(x)}G^\lambda_tv(x)$
-- statement:
--   For $t\in\mathbb N$, $v$ and $x$, the set
--   $$\operatorname*{argmin}_{\lambda\in\varpi_t(x)}G^\lambda_tv(x)=\{\lambda\in\varpi_t(x):G^\lambda_tv(x)\le G^{\lambda'}_tv(x)\ \text{for all }\lambda'\in\varpi_t(x)\}.$$
--   Selectors from these sets are the optimal Markovian policies of Theorems 4.2 and 5.5.
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, (4.5), p. 18; (5.7), p. 23

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_G
import Definitions.Def_RiskDistMDP_DPP_MarkovPolicies

set_option autoImplicit false

open MeasureTheory

namespace RiskDistMDP.DPP

/-- `argmin_{λ ∈ ϖ_t(x)} G^λ_t v(x)` (arXiv:2203.09612v4, (4.5), p.18, and (5.7), p.23): the
admissible randomized actions at which `λ ↦ G^λ_t v(x)` attains its minimum over `ϖ_t(x)`. -/
def argminSet {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸] (R : RiskMDP 𝕏 𝔸) (t : ℕ)
    (v : 𝕏 → ℝ) (x : 𝕏) : Set (ProbabilityMeasure 𝔸) :=
  {l | l ∈ varpi R.toBorelMDP t x ∧ ∀ l' ∈ varpi R.toBorelMDP t x, G R t l v x ≤ G R t l' v x}

end RiskDistMDP.DPP


