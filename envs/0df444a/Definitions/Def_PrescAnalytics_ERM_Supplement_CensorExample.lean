-- Prove2me | Definitions.Def_PrescAnalytics_ERM_Supplement_CensorExample
-- name    : PrescAnalytics_ERM_Supplement_CensorExample
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:55:48.869089+00:00
-- url     : https://prove2.me/theorems/5d7ef675-440f-4b31-a957-25fe9ff6c5dc
-- title:
--   A smooth bounded-cost counterexample to the printed censoring theorem
-- statement:
--   Let $T$ be uniform on $[0,1/4]$, and let $B,D$ be independent fair Bernoulli variables independent of $T$. Define
--   $$X=T,\qquad Y=T+B,\qquad V=T+2D.$$
--   The conditional response and threshold are independent, both marginal distributions are atomless, and their conditional upper endpoints are $x+1<x+2$. Nevertheless $P(Y=V)=1/4$. A $C^2$ quintic step $s$ is zero below $1/4$ and one above $1$. On the decision set $\{0,1\}$ take $c(z;y)=(1-z)s(y)+3z/5$. The true costs are $1/2$ and $3/5$, whereas the transformed cost of decision zero tends to $4^{-1/3}>3/5$. These explicit objects support the refutation target, rather than an altered version of the censoring theorem. The law, smooth step and cost are constructed by definitions, not arbitrary variables pinned by the desired conclusions.
-- source:
--   Bertsimas, Kallus, From Predictive to Prescriptive Analytics, arXiv:1402.5481v4, pp. 24–25, Theorem 11; p. 51, proof of Theorem 11

import Mathlib
import Definitions.Def_PrescAnalytics_ERM_Supplement_Censoring

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace PrescAnalytics.ERM.Supplement

/-- Uniform covariate T on [0,1/4]. -/
noncomputable def exampleCovariateLaw : Measure ℝ :=
  (4 : ℝ≥0∞) • volume.restrict (Set.Icc 0 (1/4 : ℝ))

/-- Independent fair bits B,D used for the response and censoring threshold. -/
noncomputable def exampleBitLaw : Measure ℝ :=
  (1/2 : ℝ≥0∞) • (Measure.dirac 0 + Measure.dirac 1)

/-- X=T, Y=T+B, V=T+2D. Both marginals are atomless, but Y=V with probability 1/4.
Conditionally on X, B and D remain independent; upper endpoints are X+1 < X+2. -/
noncomputable def censorExampleLaw :
    Measure (EuclideanSpace ℝ (Fin 1) × (EuclideanSpace ℝ (Fin 1) × ℝ)) :=
  ((exampleCovariateLaw).prod (exampleBitLaw.prod exampleBitLaw)).map
    (fun p => (scalarVector p.1, (scalarVector (p.1 + p.2.1), p.1 + 2 * p.2.2)))

noncomputable def examplePairLaw : Measure (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) :=
  censorExampleLaw.map (fun p => (p.1, p.2.1))

/-- C² smooth step: zero on (-∞,1/4], one on [1,∞). -/
noncomputable def exampleStep (y : ℝ) : ℝ :=
  if y ≤ 1/4 then 0 else if 1 ≤ y then 1 else
    let t := (y - 1/4) / (3/4)
    6 * t^5 - 15 * t^4 + 10 * t^3

/-- At z=0 the cost distinguishes the two response bands. At z=1 it is the constant 3/5. -/
noncomputable def exampleCost (z y : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  (1 - z 0) * exampleStep (y 0) + (z 0) * (3/5)

def exampleDecisions : Set (EuclideanSpace ℝ (Fin 1)) := {scalarVector 0, scalarVector 1}

end PrescAnalytics.ERM.Supplement


