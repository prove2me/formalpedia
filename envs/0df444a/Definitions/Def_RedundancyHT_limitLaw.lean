-- Prove2me | Definitions.Def_RedundancyHT_limitLaw
-- name    : RedundancyHT_limitLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:26:57.529126+00:00
-- url     : https://prove2.me/theorems/7c713456-c8b5-4bdc-8387-0489eae6e504
-- title:
--   The limit law: one exponential variable times the critical arrival proportions
-- statement:
--   Let $E$ be an exponential random variable with rate one. The limit law is the law of the random vector
--   $$X=\Bigl(E\,\frac{p_S}{p_{\mathcal T^*}}\Bigr)_{S\in\mathcal T^*},\ (0)_{S\notin\mathcal T^*}.$$
--   All coordinates are driven by the same variable $E$, so the law is concentrated on a ray of the non-negative orthant.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, Theorem 2, p.12

import Definitions.Def_RedundancyHT_pSet

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The limit law of Theorem 2**: the law of `(Exp(1) (p_S/p_𝒯*)_{S∈𝒯*}, (0)_{S∉𝒯*})`
(arXiv:2005.14566v5, Theorem 2, p.12), with `Exp(1)` of rate one, as (15) on p.18 confirms.
A single exponential variable drives all coordinates. -/
def limitLaw {n m : ℕ} (D : Model n m) (T : Finset (Fin n)) : Measure (Fin n → ℝ) :=
  (ProbabilityTheory.expMeasure 1).map
    (fun x i => if i ∈ T then x * (pOf D i / pSet D T) else 0)

end RedundancyHT


