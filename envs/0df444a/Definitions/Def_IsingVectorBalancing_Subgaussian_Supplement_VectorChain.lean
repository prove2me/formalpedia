-- Prove2me | Definitions.Def_IsingVectorBalancing_Subgaussian_Supplement_VectorChain
-- name    : IsingVectorBalancing_Subgaussian_Supplement_VectorChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:15:51.503209+00:00
-- url     : https://prove2.me/theorems/a2700969-e8dd-4951-8991-a7abaeef101b
-- title:
--   Vector-law single-site residuals, margin and explicit mixing bound
-- statement:
--   For input vectors $v_i$, let $\alpha_0=\min_i(1-\|v_i\|_2^2)$. On the published tilted sign law $\mu_h$, $P_i f$ is the weighted average of the two configurations obtained by replacing spin $i$, and $D_i f=f-P_i f$. Set $P_i f=0$ on a null conditioning fiber. For real fields $h_i$, define the natural-number bound
--
--   $$B(v,h,\varepsilon)=\left\lceil\frac n{\alpha_0}\left(\log\frac1\varepsilon+n\log2+2\sum_i|h_i|+n^2\log\frac{2-\alpha_0}{\alpha_0}\right)\right\rceil.$$
--
--   This formula is used only with $n\ge1$, $\alpha_0>0$ and $0<\varepsilon<1$, so every logarithm and denominator has its source domain. It packages the proof's constants without a gap or convergence assumption.
-- source:
--   Heng Guo, Daniel Spielman, Xinyuan Zhang, STOC 2027 submission #1240 (October 2026), pp. 10–11, 16 (PDF 11–12, 17), Section 7, (9), proof of Theorem 2

import Definitions.Def_IsingVectorBalancing_Subgaussian_Law
import Definitions.Def_mm_mcmc

open scoped BigOperators
set_option autoImplicit false

namespace IsingVectorBalancing.Subgaussian.Supplement

/-- The minimum margin, equal to 1 minus the largest squared norm when n > 0. -/
noncomputable def alpha0 {n d : ℕ} (v : Fin n → Vec d) : ℝ :=
  ⨅ i : Fin n, 1 - ‖v i‖ ^ 2

/-- Binary single-site conditional expectation on the actual tilted law.
On a null fiber real division returns zero, as specified in the source. -/
noncomputable def binaryAverage {n : ℕ} (μ : Configuration n → ℝ)
    (i : Fin n) (f : Configuration n → ℝ) (σ : Configuration n) : ℝ :=
  (∑ a : Bool, μ (Function.update σ i a) * f (Function.update σ i a)) /
    ∑ a : Bool, μ (Function.update σ i a)

noncomputable def binaryResidual {n : ℕ} (μ : Configuration n → ℝ)
    (i : Fin n) (f : Configuration n → ℝ) (σ : Configuration n) : ℝ :=
  f σ - binaryAverage μ i f σ

/-- The exact bound obtained from the two displays on p.16/PDF17. -/
noncomputable def vectorMixingBound {n d : ℕ} (v : Fin n → Vec d)
    (h : Fin n → ℝ) (ε : ℝ) : ℕ :=
  ⌈(n : ℝ) / alpha0 v * (Real.log (1 / ε) + (n : ℝ) * Real.log 2 +
    2 * ∑ i, |h i| + (n : ℝ) ^ 2 * Real.log ((2 - alpha0 v) / alpha0 v))⌉₊

end IsingVectorBalancing.Subgaussian.Supplement


