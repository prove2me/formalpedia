-- Prove2me | Definitions.Def_BayesBAI_tapeExp
-- name    : BayesBAI_tapeExp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:54:54.987688+00:00
-- url     : https://prove2.me/theorems/985ca0cd-db57-4758-92d1-98a5efa14478
-- title:
--   The expectation $\mathbb E_\mu$ over the reward tape
-- statement:
--   For $f$ a real function of the tape,
--   $$
--   \mathbb E_\mu[f]=\sum_{\omega}\mathbb P_\mu(\omega)\,f(\omega).
--   $$
--   The sample space is finite, so this is a finite sum and no integrability question arises.
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, §1, p.1

import Mathlib
import Definitions.Def_BayesBAI_tapeProb

namespace BayesBAI

/-- The expectation `𝔼_μ[f]` over the reward tape, for Komiyama, Ariu, Kato, Qin,
arXiv:2111.09885v3, §1, p.1. The sample space is finite, so this is a finite sum. -/
noncomputable def tapeExp {K T : ℕ} (μ : Fin K → ℝ) (f : Tape K T → ℝ) : ℝ :=
  ∑ ω, tapeProb μ ω * f ω

end BayesBAI


