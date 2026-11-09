-- Prove2me | Definitions.Def_GevreyGibbsSep_LjN
-- name    : GevreyGibbsSep_LjN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:38:53.7682+00:00
-- url     : https://prove2.me/theorems/98e298be-3b37-4fd3-8527-508a8c810d56
-- title:
--   Finer-grid Witten factors $L_{j,N}$
-- statement:
--   The finer-grid factors of the discretized Witten Laplacian are
--   $$L_{j,N}=-\frac{i}{\sqrt\beta}\,\iota_N\tilde\partial_j-\frac{i\sqrt\beta}{2}\,\mathrm{diag}\big([\partial_jE]_{2N}\big)\,\iota_N ,$$
--   mapping the $N$-grid to the $2N$-grid; $[\partial_jE]_{2N}$ is the vector of values of $\partial_jE$ on the $2N$-grid.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Eq. (A41), p.25

import Mathlib
import Definitions.Def_GevreyGibbsSep_grad
import Definitions.Def_GevreyGibbsSep_Grid
import Definitions.Def_GevreyGibbsSep_gridPt
import Definitions.Def_GevreyGibbsSep_iotaN
import Definitions.Def_GevreyGibbsSep_fourierDeriv

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The finer-grid factor `L_{j,N} = −(i/√β) ι_N ∂̃_j − (i√β/2) diag([∂_j E]_{2N}) ι_N`,
Eq. (A41), p.25 of arXiv:2608.24527 (sha256 d4fd40eb…), mapping the `N`-grid to the `2N`-grid. -/
noncomputable def LjN (d N : ℕ) (β : ℝ) (E : (Fin d → ℝ) → ℝ) (j : Fin d) :
    Matrix (Grid d (2 * N)) (Grid d N) ℂ :=
  (-(Complex.I / (Real.sqrt β : ℂ))) • (iotaN d N * fourierDeriv d N j)
  - (Complex.I * (Real.sqrt β : ℂ) / 2) •
      (Matrix.diagonal (fun y => ((grad E (gridPt d (2 * N) y) j : ℝ) : ℂ)) * iotaN d N)

end GevreyGibbsSep


