-- Prove2me | Definitions.Def_SparseHistComm_anExp
-- name    : SparseHistComm_anExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:38:33.548401+00:00
-- url     : https://prove2.me/theorems/774cdc81-1d28-4fcc-a2cb-9882c0288ca3
-- title:
--   Analysis expectation $E[g(R, X, M)]$
-- statement:
--   The **expectation** of a nonnegative function $g(R, X, M)$ under the analysis prior of Section IV is $E[g] = \int_\Omega E[g(r, X, M) \mid R = r]\, d\mu(r)$: the public randomness is averaged last.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section IV, p.8

import Mathlib
import Definitions.Def_SparseHistComm_condExp
open MeasureTheory
open scoped ENNReal

namespace SparseHistComm

/-- The **analysis expectation** `E[g(R, X, M)]` under the prior of Section IV (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), p.8): the
integral over the public randomness of the conditional analysis expectation. -/
noncomputable def anExp {n d : ℕ} (P : Protocol n d) (k : ℕ)
    (g : P.Ω → (Fin n → Finset (Fin d)) → (Fin n → List Bool) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ r, condExp P k r (g r) ∂P.μ

end SparseHistComm


