-- Prove2me | Definitions.Def_GevreyGibbsSep_HN
-- name    : GevreyGibbsSep_HN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:39:52.535921+00:00
-- url     : https://prove2.me/theorems/be4f631d-7348-4498-91a4-5e0de597e94d
-- title:
--   Discretized Witten Laplacian $\mathbb H_N$
-- statement:
--   The discretized Witten Laplacian on the $N$-grid,
--   $$\mathbb H_N=\sum_{j=1}^{d}L_{j,N}^*L_{j,N}=\mathbb W_N^\dagger\mathbb W_N,$$
--   a Hermitian positive semi-definite matrix; its ground state approximates the grid state $|[e^{-\beta E/2}]_N\rangle$.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Section A 3, p.25; p.9

import Mathlib
import Definitions.Def_GevreyGibbsSep_Grid
import Definitions.Def_GevreyGibbsSep_LjN

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The discretized Witten Laplacian `H_N = ∑_j L_{j,N}^* L_{j,N}` (arXiv:2608.24527 (sha256
d4fd40eb…), p.25, and `H_N = W_N^† W_N`, p.9 and p.28). -/
noncomputable def HN (d N : ℕ) (β : ℝ) (E : (Fin d → ℝ) → ℝ) :
    Matrix (Grid d N) (Grid d N) ℂ :=
  ∑ j, (LjN d N β E j).conjTranspose * LjN d N β E j

end GevreyGibbsSep


