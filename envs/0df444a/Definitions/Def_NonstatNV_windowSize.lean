-- Prove2me | Definitions.Def_NonstatNV_windowSize
-- name    : NonstatNV_windowSize
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:01:55.018874+00:00
-- url     : https://prove2.me/theorems/4d69f053-1990-49d5-8220-fa03a17596ca
-- title:
--   Window size $n=\lceil\kappa T^{(1-v)/2}\rceil$
-- statement:
--   The **window size** used by the Fixed-Time-Window Policy and by PERP, for horizon $T$, variation parameter $v$ and scaling constant $\kappa>0$, is
--
--   $$
--   n=\big\lceil \kappa\,T^{(1-v)/2}\big\rceil .
--   $$
--
--   **Formalization Note** The ceiling is kept, as in Algorithms 1 and 4.
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, Algorithm 1, p.16; Algorithm 4, p.23

import Mathlib

namespace NonstatNV

/-- The window size `n = ⌈κ T^{(1−v)/2}⌉` of the Fixed-Time-Window Policy and of PERP
(Algorithms 1 and 4 of An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4, pp.16, 23), with the ceiling kept. -/
noncomputable def windowSize (T : ℕ) (v κ : ℝ) : ℕ :=
  ⌈κ * (T : ℝ) ^ ((1 - v) / 2)⌉₊

end NonstatNV


