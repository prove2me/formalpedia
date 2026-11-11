-- Prove2me | Definitions.Def_GaussDiffSVP_Budget
-- name    : GaussDiffSVP_Budget
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:49.025517+00:00
-- url     : https://prove2.me/theorems/1d3c824e-d32f-46cb-9c43-5c710eda4b8b
-- title:
--   Schedules of sublinear budgets $(w_n, h_n, b_n)$ and $\ell_n = n w_n + L_{\log}$
-- statement:
--   A **schedule** consists of three sequences: the relative shell width $w_n$, the smoothing and thinning budget $h_n$, and the extra initial list exponent $b_n$. Every schedule has the logarithmic error in shell counts
--   $$\ell_n = n w_n + \lceil\log_2(n+2)\rceil .$$
--   The paper uses two schedules: the default one for SVP and batches (163) and the single-sample one (166).
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §3.3, p.19; (163), p.80; (166), p.86

import Mathlib
import Definitions.Def_GaussDiffSVP_Llog

namespace GaussDiffSVP

/-- A schedule of sublinear budgets (Gao–Han–Hu, *Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §3.3, p.19; App. C.1.2, p.80; App. C.3.2, p.86): the
relative shell width `w_n`, the smoothing and thinning budget `h_n` and the extra initial list
exponent `b_n`, as functions of the dimension `n`. -/
structure Budget where
  /-- the relative shell width `w_n` -/
  w : ℕ → ℝ
  /-- the smoothing and thinning budget `h_n` -/
  h : ℕ → ℝ
  /-- the extra initial list exponent `b_n` -/
  b : ℕ → ℝ

/-- The logarithmic error in shell counts `ℓ_n = n w_n + ⌈log₂(n + 2)⌉` of a schedule (§3.3, p.19;
(163), p.80; (166), p.86); both schedules of the paper use this formula. -/
noncomputable def Budget.ell (β : Budget) (n : ℕ) : ℝ := n * β.w n + Llog n

end GaussDiffSVP


