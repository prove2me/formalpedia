-- Prove2me | Definitions.Def_AFIsingKS_betaKS
-- name    : AFIsingKS_betaKS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:13:47.525331+00:00
-- url     : https://prove2.me/theorems/14f194e8-6ec7-4c39-8dfb-0183de2eb482
-- title:
--   Kesten–Stigum threshold $\beta_{\mathrm{KS}}(d)$
-- statement:
--   For an integer $d\ge3$, the **Kesten–Stigum threshold** of the antiferromagnetic Ising model on $d$-regular graphs is
--   $$\beta_{\mathrm{KS}}(d)=2\operatorname{arctanh}\frac1{\sqrt{d-1}}.$$
--   It is the reconstruction threshold of the broadcast process on the $(d-1)$-ary tree, and the upper end of the range of inverse temperatures treated by this mission.
--
--   **Formalization Note** For $d\ge3$ the argument of the inverse hyperbolic tangent lies in $(0,1)$, so the value is genuine and positive. Every statement of the mission assumes $d\ge3$.
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), eq. (1), p.4

import Mathlib

open Real

namespace AFIsingKS

/-- The Kesten–Stigum threshold `β_KS(d) = 2 arctanh(1/√(d−1))` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), eq. (1), p.4).

**Formalization Note.** For `d ≥ 3` the argument `1/√(d−1)` lies in `(0,1)`, so `Real.artanh` takes
its genuine value and `betaKS d > 0`. Every statement of the mission assumes `3 ≤ d`. -/
noncomputable def betaKS (d : ℕ) : ℝ :=
  2 * Real.artanh (1 / Real.sqrt ((d : ℝ) - 1))

end AFIsingKS


