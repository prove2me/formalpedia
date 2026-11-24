-- Prove2me | Definitions.Def_HealthRefPricing_PriceCompare_Supplement_Assumption5
-- name    : HealthRefPricing_PriceCompare_Supplement_Assumption5
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:39:08.931241+00:00
-- url     : https://prove2.me/theorems/33ddcb43-36a4-45d4-ada5-2613085f560c
-- title:
--   Assumption 5, Appendix p. 2 — limiting RV best-response shares at most one half
-- statement:
--   Fix the two-provider RV game and cost share $\lambda$. For provider $j$, let $b_j(y)$ be a profit-maximizing own price when the rival charges $y$. Write $S^{RV}_j(b_j(y),y)$ for its multinomial-logit share at this profile. Assumption 5 requires best responses to exist for every rival price, and, along every best-response selection, a real limiting share satisfying
--
--   $$\lim_{y\to+\infty}S^{RV}_j(b_j(y),y)=\bar S^{RV}_j\le\tfrac12,\qquad j=1,2.$$
--
--   The limit may be witnessed separately for each selection. This makes the paper's assumption on best-response limits precise and prevents a universal assertion over nonexistent best responses from holding vacuously.
--
--   **Formalization Note** This uses the same convention as the published Assumption2: an existing best-response selection and convergence along every such selection. Providers use `Fin 2`: index 0 is provider 1 and index 1 provider 2. The price profile uses the published `vs`; the only changed ingredient is the RV out-of-pocket rule.
-- source:
--   Nassiri, Adida & Mamani, Reference pricing for healthcare services, author manuscript (SSRN 3176280, version of Dec. 28, 2020; eScholarship 3sm502rz), Appendix p. 2 (PDF 35), Assumption 5; p. 12 (PDF 13), notation preceding Assumption 1

import Mathlib
import Definitions.Def_HealthRefPricing_PriceCompare_Supplement_RV

namespace HealthRefPricing.PriceCompare.Supplement

/-- Assumption 5 (Appendix p. 2), with the same limit and selection convention as base Assumption2. -/
def Assumption5 (P : Params) (lam : ℝ) : Prop :=
  ∀ j : Fin 2, (∃ br : ℝ → ℝ, ∀ y, IsBestRespRV P lam j y (br y)) ∧
    ∀ br : ℝ → ℝ, (∀ y, IsBestRespRV P lam j y (br y)) →
      ∃ L : ℝ, L ≤ 1 / 2 ∧
        Filter.Tendsto (fun y => share P (oopRV P lam (vs j (br y) y)) j)
          Filter.atTop (nhds L)

end HealthRefPricing.PriceCompare.Supplement


