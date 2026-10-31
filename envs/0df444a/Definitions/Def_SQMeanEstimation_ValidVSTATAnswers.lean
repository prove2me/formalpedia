-- Prove2me | Definitions.Def_SQMeanEstimation_ValidVSTATAnswers
-- name    : SQMeanEstimation_ValidVSTATAnswers
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:48.795275+00:00
-- url     : https://prove2.me/theorems/21bc7c4e-a47e-422e-b034-ded0488de9a2
-- title:
--   Answers that $\mathrm{VSTAT}_\mu(n)$ may return to an SQ algorithm
-- statement:
--   Let $\mu$ be a distribution on $\mathbb R^d$, $n>0$, and let $A$ be a non-adaptive SQ algorithm with queries $\phi_1,\dots,\phi_m$. A vector $v\in\mathbb R^m$ is a **valid answer vector of $\mathrm{VSTAT}_\mu(n)$** for $A$ if for every $i$
--   $$
--   |v_i-p_i|\le\max\Big\{\frac1n,\ \sqrt{\frac{p_i(1-p_i)}{n}}\Big\},\qquad p_i=\mathbf E_{w\sim\mu}[\phi_i(w)].
--   $$
--   These are exactly the answers the oracle of Definition 2.1 is allowed to give.
--
--   **Formalization Note** The expectation is the Lebesgue (Bochner) integral against the measure $\mu$ on `Fin d → ℝ`.
-- source:
--   Feldman, Guzmán, Vempala, Statistical Query Algorithms for Mean Vector Estimation and Stochastic Convex Optimization, arXiv:1512.09170v2, Definition 2.1, p.11

import Mathlib
import Definitions.Def_SQMeanEstimation_vstatTol
import Definitions.Def_SQMeanEstimation_NonadaptiveSQ

open MeasureTheory

namespace SQMeanEstimation

/-- **Answers a VSTAT oracle may give to a non-adaptive SQ algorithm.**
Feldman, Guzmán, Vempala, arXiv:1512.09170v2, Definition 2.1, p.11: VSTAT_D(n), given φ, "returns
some value v such that |v − p| ≤ max{1/n, √(p(1−p)/n)}, where p ≐ E_{w∼D}[φ(w)]".

`ValidVSTATAnswers μ n A v` says that, for every query `φᵢ` of `A`, the answer `vᵢ` is within
`vstatTol n pᵢ` of `pᵢ = ∫ φᵢ dμ`. Any such answer vector may be returned by VSTAT_μ(n).

**Formalization Note.** The input distribution `D` is a measure `μ` on `Fin d → ℝ`; the
expectation is the Bochner integral (the queries are measurable and `[0,1]`-valued, so they are
integrable against a probability measure). -/
def ValidVSTATAnswers {d m : ℕ} (μ : Measure (Fin d → ℝ)) (n : ℝ) (A : NonadaptiveSQ d m)
    (v : Fin m → ℝ) : Prop :=
  ∀ i, |v i - ∫ w, A.query i w ∂μ| ≤ vstatTol n (∫ w, A.query i w ∂μ)

end SQMeanEstimation


