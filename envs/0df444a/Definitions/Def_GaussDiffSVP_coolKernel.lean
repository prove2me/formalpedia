-- Prove2me | Definitions.Def_GaussDiffSVP_coolKernel
-- name    : GaussDiffSVP_coolKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:02:16.572516+00:00
-- url     : https://prove2.me/theorems/eb5d0418-6ad7-40ba-bde4-94fd59745496
-- title:
--   Cooling activation probability $q_j$
-- statement:
--   For children at level $j$ with input width $r = r_j$ and input coefficient $\Upsilon_j$,
--   $$q_j(x,y) = \frac{2^{-h_n}}{D^+_j}\,K(x,y),\qquad D^+_j = \Upsilon_j B_j 2^{b_{\deg}},\quad b_{\deg} = \lceil 10\ell_n\rceil .$$
--   Theorem 5.2 asserts that these are at most one.
--
--   **Formalization Note** Values in $[0,\infty]$; the schedule quantities are explicit arguments.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (44)–(45), p.28

import Mathlib
import Definitions.Def_GaussDiffSVP_coolPairWeight
import Definitions.Def_GaussDiffSVP_coolB

open scoped ENNReal

namespace GaussDiffSVP

/-- The cooling activation probability (45) (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.28) for children at level `j` with input width
`r = r_j` and input coefficient `Υ = Υ_j`:
`q_j(x, y) = 1[x, y ∈ S_r(a₀)] 1[E_r(x − y) ∈ a₁(1 ± w_n)] (2^{−h_n} / D_j^+) ω_r(x − y)`,
with `D_j^+ = Υ_j B_j 2^{b_deg}` and `b_deg = ⌈10 ℓ_n⌉` (44); the indicator–weight product is
`coolPairWeight`.

**Formalization Note.** Values in `ℝ≥0∞`. The schedule quantities `w = w_n`, `h = h_n`,
`ℓ = ℓ_n` are explicit arguments. Whether `q_j ≤ 1` is not built in; Theorem 5.2 asserts it. -/
noncomputable def coolKernel {n : ℕ} (w h ℓ u r Υ : ℝ) (x y : SuperlatSVP.E n) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) ^ (-h) / (Υ * coolB n w u r * (2 : ℝ) ^ ⌈10 * ℓ⌉₊)) *
    coolPairWeight w u r x y

end GaussDiffSVP


