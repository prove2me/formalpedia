-- Prove2me | Definitions.Def_IntroMatrixConc_Sampling_Defs
-- name    : IntroMatrixConc_Sampling_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:37:15.457734+00:00
-- url     : https://prove2.me/theorems/f6937b03-56fa-4c3f-bf40-aac3f2eb99e2
-- title:
--   §6.2.1 — matrix sampling estimator
-- statement:
--   For a positive integer $n$ and a family of rectangular random matrices $R_1,\ldots,R_n$ of the same size, the **matrix sampling estimator** is their empirical average:
--
--   $$
--   \overline R_n(\omega)=\frac{1}{n}\sum_{k=1}^{n}R_k(\omega).
--   $$
--
--   This definition supplies the estimator used in Corollary 6.2.1 and its sampling-rate consequence. The definition itself is total at $n=0$, where it returns the zero matrix; every theorem about the estimator requires $n>0$.
-- source:
--   Tropp, arXiv:1501.01571v1, §6.2.1, p. 81 (PDF p. 87), estimator display

import Definitions.Def_TroppMatrixConcentration_probability

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace IntroMatrixConc.Sampling

/-- The empirical mean of `n` rectangular random matrices, as in §6.2.1.
The theorem statements using it require `0 < n`. -/
def samplingEstimator {Ω : Type*} {d₁ d₂ n : ℕ}
    (R : Fin n → Ω → Matrix (Fin d₁) (Fin d₂) ℂ)
    (ω : Ω) : Matrix (Fin d₁) (Fin d₂) ℂ :=
  ((n : ℝ)⁻¹) • ∑ k, R k ω

end IntroMatrixConc.Sampling


