-- Prove2me | Definitions.Def_LocalDOvS_SUS_sampleSizes
-- name    : LocalDOvS_SUS_sampleSizes
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:26:18.171415+00:00
-- url     : https://prove2.me/theorems/0ac5a7f9-b0ad-4f10-aae0-a022ab40050a
-- title:
--   Sample sizes $L$ used by the algorithm
-- statement:
--   The set of sample sizes at which the corrected SUS algorithm can compute an empirical mean,
--
--   $$
--   L:=\{n(M):3\le M\le N\}\cup\{n_{\mathrm{fin}}\}.
--   $$
--
--   It has at most $N-1$ elements, and it is fixed before any simulation, which is what lets one union bound cover an adaptive run.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, Algorithm 2, pp.15–16 (corrected)

import Mathlib
import Definitions.Def_LocalDOvS_SUS_nLook
import Definitions.Def_LocalDOvS_SUS_nFin

open scoped NNReal

namespace LocalDOvS.SUS

/-- The sample sizes at which the corrected shrinking uniform sampling algorithm ever computes
an empirical mean (Zhang–Zheng–Lavaei, arXiv:2012.02427v2, Algorithm 2, pp.15–16, corrected):
`L := {n(M) : 3 ≤ M ≤ N} ∪ {n_fin}`. -/
noncomputable def sampleSizes (N : ℕ) (σ : ℝ≥0) (ε δ : ℝ) : Finset ℕ :=
  (Finset.Icc 3 N).image (nLook N σ ε δ) ∪ {nFin N σ ε δ}

end LocalDOvS.SUS


