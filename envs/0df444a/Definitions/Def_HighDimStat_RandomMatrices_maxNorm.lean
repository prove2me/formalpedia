-- Prove2me | Definitions.Def_HighDimStat_RandomMatrices_maxNorm
-- name    : HighDimStat_RandomMatrices_maxNorm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:20:40.61591+00:00
-- url     : https://prove2.me/theorems/32107ccf-f284-4934-8b51-435efae76e7a
-- title:
--   The elementwise max-norm of a matrix
-- statement:
--   The **elementwise max-norm** $\|M\|_{\max} := \max_{i,j}|M_{ij}|$, used in Eq. (6.54)'s
--   hypothesis $\|\hat\Sigma-\Sigma\|_{\max}\le\lambda_n$.
--
--   **Formalization Note** Realized as `⨆` over the finite type `Fin d × Fin d`; equals the true
--   maximum for `d>0`, and is Mathlib's junk value `0` at `d=0`, harmless since no entries exist
--   to measure either.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 181 (PDF p. 201), Eq. (6.54)

import Mathlib

namespace HighDimStat.RandomMatrices

/-- The **elementwise max-norm** `‖M‖_max := max_{i,j} |M_{ij}|`, Wainwright, *High-Dimensional
Statistics* (2019), used in Eq. (6.54)'s hypothesis `‖Σ̂-Σ‖_max ≤ λn`. Realized as `⨆` over the
finite type `Fin d × Fin d`; equals the true maximum for `d > 0`, and is Mathlib's junk value `0`
at `d = 0`, harmless since no entries exist to measure either. -/
noncomputable def maxNorm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ⨆ p : Fin d × Fin d, |M p.1 p.2|

end HighDimStat.RandomMatrices


