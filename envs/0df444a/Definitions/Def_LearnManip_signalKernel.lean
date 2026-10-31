-- Prove2me | Definitions.Def_LearnManip_signalKernel
-- name    : LearnManip_signalKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:44.219+00:00
-- url     : https://prove2.me/theorems/e7498500-069f-4ee6-87a2-a8810bfa8583
-- title:
--   Likelihood of the Gaussian signal
-- statement:
--   The likelihood of the signal (1): given $\theta$, the terminal signal $Z^q=\theta q+B_q$ has law $N(\theta q,q)$, as a Markov kernel in $\theta$.
--
--   **Formalization Note.** $Z^q$ is the terminal value of the signal, the quantity that enters (2). It is sufficient for the path.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (1), p.7

import Mathlib

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The likelihood of the Gaussian signal (1), p.7, of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04):
given `θ`, the signal `Z^q = θ q + B_q` has law `N(θ q, q)`.

**Formalization Note.** `Z^q` is the terminal value of the signal, the quantity that enters (2). The
path adds no information about `θ`, since `Z^q` is sufficient. -/
noncomputable def signalKernel (q : ℝ≥0) : Kernel ℝ ℝ where
  toFun θ := gaussianReal (θ * q) q
  measurable' := measurable_gaussianReal.comp
    ((measurable_id.mul_const (q : ℝ)).prodMk measurable_const)

instance signalKernel.isMarkovKernel (q : ℝ≥0) : IsMarkovKernel (signalKernel q) :=
  ⟨fun θ => by
    change IsProbabilityMeasure (gaussianReal (θ * q) q)
    infer_instance⟩

end LearnManip


