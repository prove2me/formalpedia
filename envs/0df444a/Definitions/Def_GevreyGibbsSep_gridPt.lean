-- Prove2me | Definitions.Def_GevreyGibbsSep_gridPt
-- name    : GevreyGibbsSep_gridPt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:42.291893+00:00
-- url     : https://prove2.me/theorems/31854ab5-8fa3-441f-83fc-67eb514e1029
-- title:
--   Grid points $x_k=2\pi k/(2N+1)$
-- statement:
--   The grid point of index $k\in[-N,\dots,N]^d$ is $x_k=\frac{2\pi k}{2N+1}$, coordinatewise.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Appendix A 1, p.20; Eq. (A12), p.21

import Mathlib
import Definitions.Def_GevreyGibbsSep_Grid

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The grid point `x_k = 2π k/(2N + 1)`, `k ∈ [−N, …, N]^d` (arXiv:2608.24527 (sha256
d4fd40eb…), p.20 and Eq. (A12), p.21). -/
noncomputable def gridPt (d N : ℕ) (k : Grid d N) : Fin d → ℝ :=
  fun i => 2 * Real.pi * (((k i : ℕ) : ℝ) - N) / (2 * N + 1)

end GevreyGibbsSep


