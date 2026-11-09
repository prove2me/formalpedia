-- Prove2me | Definitions.Def_CubeSampling_cubeMeasure
-- name    : CubeSampling_cubeMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:15:45.675037+00:00
-- url     : https://prove2.me/theorems/7cc69806-2129-4f6a-ba1b-cb6cb6fd00ff
-- title:
--   The uniform probability measure $\mu_d$ on $\{-1,1\}^d$
-- statement:
--   $\mu_d$ is the **uniform probability measure** on $\{-1,1\}^d$: every point has mass $2^{-d}$. The inputs $X_1,\dots,X_n$ of the regression model are i.i.d. with law $\mu_d$, so the sample $(X_1,\dots,X_n)$ has law $\mu_d^{\otimes n}$.
--
--   **Formalization Note** Built from Mathlib's uniform probability mass function on a finite type; an instance records that it is a probability measure.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 1.1, p.3

import Mathlib
import Definitions.Def_CubeSampling_Cube
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CubeSampling

/-- The uniform probability measure `μ_d` on `{−1, 1}^d` (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §1.1, p.3), used for the
i.i.d. inputs `X_i ~ μ_d`; the sample `(X_1, …, X_n)` has law `Measure.pi (fun _ => μ_d)`. -/
noncomputable def cubeMeasure (d : ℕ) : Measure (Cube d) := (PMF.uniformOfFintype (Cube d)).toMeasure

instance cubeMeasure.isProbabilityMeasure (d : ℕ) : IsProbabilityMeasure (cubeMeasure d) := by
  unfold cubeMeasure; infer_instance

end CubeSampling


