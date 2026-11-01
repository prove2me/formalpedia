-- Prove2me | Definitions.Def_BayesBAI_bayesSimpleRegret
-- name    : BayesBAI_bayesSimpleRegret
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:59:26.628891+00:00
-- url     : https://prove2.me/theorems/fdeaa938-249f-4c62-9ace-e96724580a2a
-- title:
--   The Bayesian simple regret $\mathrm R_H(T)$ of two-stage exploration
-- statement:
--   For a prior $H$ on $[0,1]^K$, the Bayesian simple regret of Algorithm 1 is
--   $$
--   \mathrm R_H(T)=\mathbb E_{\mu\sim H}[\mathrm R_\mu(T)].
--   $$
--
--   **Formalization Note.** Under `RegularPrior` the integrand is continuous, and bounded on the cube that carries $H$, so this is an integral of an integrable function.
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, eq. (3), p.2

import Mathlib
import Definitions.Def_BayesBAI_simpleRegret

open MeasureTheory

namespace BayesBAI

/-- The Bayesian simple regret `R_H(T) = 𝔼_{μ∼H}[R_μ(T)]` of Algorithm 1, (3), Komiyama, Ariu, Kato,
Qin, arXiv:2111.09885v3, p.2.

**Formalization Note.** This is a Bochner integral. Under `RegularPrior` the integrand is continuous in
`μ`, `H` lives on the cube, and the function is bounded there, so `Integrable` holds
(`Solutions/verification/BayesBAI_sanity.lean`) and the value is genuine. -/
noncomputable def bayesSimpleRegret {K : ℕ} (hK : 2 ≤ K) (H : Measure (Fin K → ℝ))
    (sel : TieBreak K) (q : ℝ) (T : ℕ) : ℝ :=
  ∫ μ, simpleRegret hK sel q T μ ∂H

end BayesBAI


