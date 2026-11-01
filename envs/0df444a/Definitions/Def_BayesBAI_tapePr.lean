-- Prove2me | Definitions.Def_BayesBAI_tapePr
-- name    : BayesBAI_tapePr
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:55:42.931274+00:00
-- url     : https://prove2.me/theorems/2d036e13-dc32-4750-bf19-d8d65e071896
-- title:
--   The probability $\mathbb P_\mu[A]$ of an event of the tape
-- statement:
--   For a set $A$ of tapes, $\mathbb P_\mu[A]=\mathbb E_\mu[\mathbf 1[A]]$.
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, §1, p.1

import Mathlib
import Definitions.Def_BayesBAI_tapeExp

namespace BayesBAI

/-- The probability `ℙ_μ[A]` of an event of the reward tape, for Komiyama, Ariu, Kato, Qin,
arXiv:2111.09885v3, §1, p.1. -/
noncomputable def tapePr {K T : ℕ} (μ : Fin K → ℝ) (A : Set (Tape K T)) : ℝ :=
  tapeExp μ (A.indicator 1)

end BayesBAI


