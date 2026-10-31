-- Prove2me | Definitions.Def_SQMeanEstimation_SolvesLqMeanEstimation
-- name    : SQMeanEstimation_SolvesLqMeanEstimation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:17:39.976234+00:00
-- url     : https://prove2.me/theorems/4bb7a139-b146-4d43-a909-bbbd4db6faab
-- title:
--   An SQ algorithm solves $\ell_q$ mean estimation with error $\varepsilon$ using $\mathrm{VSTAT}(n)$
-- statement:
--   A non-adaptive SQ algorithm $A$ **solves $\ell_q$ mean estimation with error $\varepsilon$ using $\mathrm{VSTAT}(n)$** if for every Borel probability distribution $\mu$ on $\mathbb R^d$ supported on the unit ball $B_q^d$, and for every answer vector $v$ that $\mathrm{VSTAT}_\mu(n)$ may return to the queries of $A$,
--   $$
--   \big\|\mathbf E_{w\sim\mu}[w]-\tilde w(v)\big\|_q\le\varepsilon,
--   $$
--   where $\tilde w(v)$ is the output of $A$.
--
--   This is the mean estimation problem of §3 (p.12) over $\mathcal W=B_q^d$ in the norm $\|\cdot\|_q$, solved by a statistical query algorithm against an arbitrary (adversarial) VSTAT oracle.
--
--   **Formalization Note** "Supported on $B_q^d$" is "$\|w\|_q\le1$ for $\mu$-almost every $w$". The mean is the Bochner integral of the identity, which is integrable because it is almost surely bounded.
-- source:
--   Feldman, Guzmán, Vempala, Statistical Query Algorithms for Mean Vector Estimation and Stochastic Convex Optimization, arXiv:1512.09170v2, §3, p.12; Definition 2.1, p.11

import Mathlib
import Definitions.Def_SQMeanEstimation_lqNorm
import Definitions.Def_SQMeanEstimation_NonadaptiveSQ
import Definitions.Def_SQMeanEstimation_ValidVSTATAnswers

open MeasureTheory

namespace SQMeanEstimation

/-- **A non-adaptive SQ algorithm solves ℓq mean estimation with error ε using VSTAT(n).**
Feldman, Guzmán, Vempala, arXiv:1512.09170v2, §3, p.12: "The mean estimation problem over W in
norm ‖·‖ is the problem in which, given an error parameter ε and access to a distribution D
supported over W, the goal is to find a vector w̃ such that ‖E_{w∼D}[w] − w̃‖ ≤ ε. We will be
concerned primarily with the case when W is the unit ball of ‖·‖"; with Definition 2.1, p.11.

`SolvesLqMeanEstimation q ε n A` says: for every Borel probability measure `μ` on ℝᵈ supported on
the unit ℓq ball, and for every answer vector `v` that VSTAT_μ(n) may return to the queries of
`A`, the output satisfies `‖E_μ[w] − A(v)‖_q ≤ ε`.

**Formalization Note.** "Supported on `Bᵈ_q`" is `∀ᵐ w ∂μ, lqNorm q w ≤ 1`. The mean
`E_μ[w]` is the Bochner integral `∫ w, w ∂μ` in `Fin d → ℝ` (the identity is a.s. bounded, hence
integrable). The algorithm must succeed against every valid answer vector, i.e. against every
behaviour of the oracle. -/
def SolvesLqMeanEstimation {d m : ℕ} (q ε n : ℝ) (A : NonadaptiveSQ d m) : Prop :=
  ∀ (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ], (∀ᵐ w ∂μ, lqNorm q w ≤ 1) →
    ∀ v : Fin m → ℝ, ValidVSTATAnswers μ n A v →
      lqNorm q ((∫ w, w ∂μ) - A.output v) ≤ ε

end SQMeanEstimation


