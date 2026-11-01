-- Prove2me | Definitions.Def_CloudCostOpt_sampleMeasure
-- name    : CloudCostOpt_sampleMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:02:18.206102+00:00
-- url     : https://prove2.me/theorems/ee58bd50-89ae-496a-8f1f-eae317d37d40
-- title:
--   Probability law of the arrivals and step outcomes
-- statement:
--   Given arrival rates $\lambda_i\ge0$, the probability measure on the sample space makes all coordinates independent, with
--
--   1. $N(i,t)\sim\mathrm{Poisson}(\lambda_i)$ (the number of arrivals of a rate-$\lambda_i$ Poisson process in a unit period);
--   2. $U(i,t,s,l,j,k)$ uniform on $[0,1]$.
--
--   An order sent to resource $j$ completes its step exactly when its uniform is below $\beta_{i,j}$, a Bernoulli$(\beta_{i,j})$ trial independent of everything else. This realizes the binomial completions (4) and the conditional independence stated on p.14.
--
--   **Formalization Note** The measure is the product of two `Measure.infinitePi` measures, of `poissonMeasure` and of the uniform measure on `unitInterval`.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §1, p.3 ("type-i orders arrive according to a Poisson process with rate λᵢ; these I Poisson arrival processes are independent"); §3, p.13 ("all service completions are independent")

import Mathlib
import Definitions.Def_CloudCostOpt_Omega

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **The probability measure** of the model with arrival rates `lam`: the arrival counts
`N (i, t)` are independent `Poisson(λᵢ)` variables (the counts of `I` independent Poisson processes
over unit periods), the uniforms are i.i.d. uniform on `[0, 1]`, and the two families are
independent.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §1, p.3 ("type-`i` orders arrive according to a Poisson process with rate `λᵢ`; these `I`
Poisson arrival processes are independent"), and p.13 ("all service completions are independent").

Formalization Note: the step outcome of an order sent to `j` is `U < β_{i,j}`, a Bernoulli(`β_{i,j}`)
trial, independent of everything else; this realizes (4) and the conditional independence of p.14. -/
noncomputable def sampleMeasure (S : System) (lam : Fin S.I → ℝ≥0) : Measure (Omega S) :=
  (Measure.infinitePi fun p : Fin S.I × ℕ => poissonMeasure (lam p.1)).prod
    (Measure.infinitePi fun _ : Fin S.I × ℕ × ℕ × ℕ × Fin (S.J + 1) × ℕ =>
      (volume : Measure unitInterval))

end CloudCostOpt


