-- Prove2me | Definitions.Def_UniformPrecSched_Makespan_Supplement_Weighted
-- name    : UniformPrecSched_Makespan_Supplement_Weighted
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:19:36.646519+00:00
-- url     : https://prove2.me/theorems/c6ccfdc8-5bb7-4799-ae3d-b1542e4e757a
-- title:
--   Release dates, weights, objective, approximation ratio and reversible time scaling
-- statement:
--   For an existing scheduling instance, let $r_j\ge0$ and $w_j\ge0$ denote release dates and weights. A schedule respects releases when $S_j\ge r_j$, and its weighted objective is
--
--   $$W(\sigma)=\sum_j w_j C_j(\sigma).$$
--
--   Write $K$ for the original number of distinct speeds. The approximation function is $\min\{K+2\sqrt K+1,1.89\log_2m+c\sqrt{\log_2m}\}$ for $m\ge2$, and $K+2\sqrt K+1$ for $m=1$. The multiplier $c$ will be chosen absolutely by the theorem.
--
--   For the interval construction multiply requirements and release dates by $a=1+\sum_j s_{\max}/p_j$, leaving speeds, weights and precedence unchanged. This makes all processing durations at least one; final start times are divided by $a$. Empty jobs have objective zero and $a=1$. These definitions extend the published model without imposing an input normalization or a precedence order on releases.
-- source:
--   Chudak & Shmoys, Approximation algorithms for precedence-constrained scheduling problems on parallel machines that run at different speeds, authors' manuscript (preprint of J. Algorithms, 1999, DOI 10.1006/jagm.1998.0987), pp. 1–2 (PDF 1–2), scheduling conventions; p. 12 (PDF 12), time normalization; p. 14 (PDF 14), Theorem 4.1

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Rounding

namespace UniformPrecSched.Makespan.Supplement

variable {n m : ℕ}

/-- Chudak–Shmoys, §1, pp. 1–2, PDF 1–2: nonnegative releases and weights,
including zero weights. No monotonicity of releases along precedence is required. -/
structure ReleaseWeights (n : ℕ) where
  r : Fin n → ℝ
  w : Fin n → ℝ
  r_nonneg : ∀ j, 0 ≤ r j
  w_nonneg : ∀ j, 0 ≤ w j

/-- The additional release-date constraint on the published nonpreemptive schedules. -/
def RespectsRelease (R : ReleaseWeights n) {I : Instance n m} (σ : Schedule I) : Prop :=
  ∀ j, R.r j ≤ σ.S j

/-- The objective Σ_j w_j C_j; it is zero on the empty job set. -/
noncomputable def weightedCost (R : ReleaseWeights n) {I : Instance n m}
    (σ : Schedule I) : ℝ := ∑ j, R.w j * σ.C j

/-- K + 2√K + 1, the finite-speed guarantee. -/
noncomputable def speedRatio (I : Instance n m) : ℝ :=
  (numSpeeds I : ℝ) + 2 * Real.sqrt (numSpeeds I) + 1

/-- Theorem 4.1, p. 14, PDF 14. Logarithms are base two. The asymptotic
branch applies for m ≥ 2; at m = 1 the finite-speed guarantee is retained. -/
noncomputable def approximationRatio (c : ℝ) (I : Instance n m) : ℝ :=
  if 2 ≤ m then min (speedRatio I)
    (1.89 * Real.logb 2 m + c * Real.sqrt (Real.logb 2 m)) else speedRatio I

/-- Explicit time normalization for §4, p. 12, PDF 12. Multiplying time
by this positive rational-preserving factor makes every processing duration at least one. -/
noncomputable def timeScale (I : Instance n m) : ℝ :=
  1 + ∑ j, maxSpeed I / I.p j

/-- The normalized instance; speeds and precedence are unchanged. -/
noncomputable def scaledInstance (I : Instance n m) : Instance n m where
  p := fun j => timeScale I * I.p j
  s := I.s
  prec := I.prec
  m_pos := I.m_pos
  p_pos := by
    intro j
    apply mul_pos _ (I.p_pos j)
    unfold timeScale
    have : 0 ≤ ∑ k, maxSpeed I / I.p k :=
      Finset.sum_nonneg fun k _ => le_of_lt (div_pos (maxSpeed_pos I) (I.p_pos k))
    linarith
  s_pos := I.s_pos
  prec_irrefl := I.prec_irrefl
  prec_trans := I.prec_trans

/-- Releases scale with time and weights do not. -/
noncomputable def scaledReleaseWeights (I : Instance n m) (R : ReleaseWeights n) :
    ReleaseWeights n where
  r := fun j => timeScale I * R.r j
  w := R.w
  r_nonneg := by
    intro j
    apply mul_nonneg _ (R.r_nonneg j)
    unfold timeScale
    have : 0 ≤ ∑ k, maxSpeed I / I.p k :=
      Finset.sum_nonneg fun k _ => le_of_lt (div_pos (maxSpeed_pos I) (I.p_pos k))
    linarith
  w_nonneg := R.w_nonneg

end UniformPrecSched.Makespan.Supplement


