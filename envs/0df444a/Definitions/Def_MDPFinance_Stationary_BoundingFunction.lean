-- Prove2me | Definitions.Def_MDPFinance_Stationary_BoundingFunction
-- name    : MDPFinance_Stationary_BoundingFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:42:07.03252+00:00
-- url     : https://prove2.me/theorems/dd954514-c9a9-41cc-82f5-5d63287a83d5
-- title:
--   Definition 2.5.2 — upper bounding function for a stationary model
-- statement:
--   A measurable $b : E \to \mathbb{R}_{\geq 0}$ is an **upper bounding function** for a
--   stationary Markov Decision Model if there are $c_r, c_g, \alpha_b \geq 0$ with $r^+(x,a) \leq
--   c_r\,b(x)$, $g^+(x) \leq c_g\,b(x)$, and $\int b(x')\,Q(dx' \mid x,a) \leq \alpha_b\,b(x)$
--   for every admissible $(x,a)$.
--
--   **Formalization Note.** Same shape as chunk `02b`'s non-stationary `IsUpperBoundingFunction`,
--   with the time index dropped (the constants and inequalities hold uniformly, not per stage).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 40, PDF 55, Definition 2.5.2

import Mathlib
import Definitions.Def_MDPFinance_Stationary_Model

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Stationary

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- Definition 2.5.2 (Bäuerle–Rieder, p. 40, PDF 55). A measurable mapping `b : E → ℝ_+` is
called an upper bounding function for the stationary Markov Decision Model if there exist
`c_r, c_g, α_b ∈ ℝ_+` such that: (i) `r^+(x,a) ≤ c_r b(x)` for all `(x,a) ∈ D`, (ii)
`g^+(x) ≤ c_g b(x)` for all `x ∈ E`, (iii) `∫ b(x') Q(dx'|x,a) ≤ α_b b(x)` for all
`(x,a) ∈ D`. -/
structure IsUpperBoundingFunction (M : StationaryMarkovDecisionModel E A) (b : E → ℝ)
    (cr cg αb : ℝ) : Prop where
  hb_meas : Measurable b
  hb_nonneg : ∀ x, 0 ≤ b x
  hcr : 0 ≤ cr
  hcg : 0 ≤ cg
  hαb : 0 ≤ αb
  hr : ∀ xa ∈ M.D, max (M.r xa) 0 ≤ cr * b xa.1
  hg : ∀ x, max (M.g x) 0 ≤ cg * b x
  hQ : ∀ xa ∈ M.D, ∫ x', b x' ∂(M.Q xa) ≤ αb * b xa.1

end MDPFinance.Stationary


