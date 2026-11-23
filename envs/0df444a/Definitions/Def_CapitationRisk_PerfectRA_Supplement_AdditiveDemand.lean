-- Prove2me | Definitions.Def_CapitationRisk_PerfectRA_Supplement_AdditiveDemand
-- name    : CapitationRisk_PerfectRA_Supplement_AdditiveDemand
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:37:34.955395+00:00
-- url     : https://prove2.me/theorems/cd03f1c0-7fcb-4c2e-ae3b-c63cf2f99365
-- title:
--   Equations (20)–(21) — additive demand with population and need probabilities
-- statement:
--   Let Λ_i be the nonnegative population of type i, and let ξ_is be nonnegative service-need probabilities with ∑_s ξ_is=1. The additive specification requires both
--   $$\lambda_i^s(x)=\Lambda_i\xi_{is}x,\qquad \lambda_i(w)=\sum_s\Lambda_i\xi_{is}w_s.$$
--   The first identity holds on each service's full interval and the second on the full quality box. This specializes the existing model for Theorem 4 while preserving every service, patient type, cost function and endpoint.
--
--   **Formalization Note** Probability upper bounds follow from nonnegativity and the unit sum. Zero population is syntactically permitted but excluded by the inherited strictly positive target enrollment. No positivity of each individual service probability is imposed.
-- source:
--   She, Ayer & Montanera, Can big data cure risk selection in healthcare capitation program? A game theoretical analysis, author manuscript (SSRN 3556992; MSOM 2022), pp. 24–25, (20)–(21)

import Definitions.Def_CapitationRisk_PerfectRA_Model

namespace CapitationRisk.PerfectRA.Supplement

variable {S I : Type*} [Fintype S] [Fintype I]

/-- The full specification (20)–(21), on the source's quality intervals and box.
Population sizes and need probabilities remain parameters, not a numerical specialization. -/
structure AdditiveDemand (M : Model S I) (population : I → ℝ)
    (need : I → S → ℝ) : Prop where
  population_nonneg : ∀ i, 0 ≤ population i
  need_nonneg : ∀ i s, 0 ≤ need i s
  need_total : ∀ i, ∑ s, need i s = 1
  service : ∀ s i, ∀ x ∈ Set.Icc (M.wl s) 1,
    M.lamS s i x = population i * need i s * x
  plan : ∀ i, ∀ w ∈ M.box,
    M.lam i w = ∑ s, population i * need i s * w s

end CapitationRisk.PerfectRA.Supplement


