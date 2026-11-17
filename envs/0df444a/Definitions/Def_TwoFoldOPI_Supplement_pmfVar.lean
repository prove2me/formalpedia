-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_pmfVar
-- name    : TwoFoldOPI_Supplement_pmfVar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:54:05.50386+00:00
-- url     : https://prove2.me/theorems/4a099cf8-fa33-4850-9469-503633ac268d
-- title:
--   The variance $\sigma^2$ of a distribution on $\mathbb Z$
-- statement:
--   For a distribution $D$ on $\mathbb Z$ with mean $\mu$, its variance is
--   $$\sigma^2(D)=\sum_{z\in\mathbb Z}(z-\mu)^2\,D(z),$$
--   and $\sigma=\sqrt{\sigma^2}$ is the standard deviation.
--
--   **Formalization Note** Every statement using it assumes a finite third absolute moment, under which the series converges absolutely.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.4, Theorem 5.38, p. 34

import Mathlib
import Definitions.Def_TwoFoldOPI_Supplement_pmfMean

namespace TwoFoldOPI

namespace Supplement

/-- **The variance `σ² = Var[D]` of a distribution on `ℤ`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.4, Theorem 5.38, p.34: "let µ_r, σ_r be the mean and standard deviation of D_r … There
exists r ∈ [R] such that Var[D_r] > 0".

`pmfVar D = Σ_{z ∈ ℤ} (z − µ)² · D(z)` with `µ = pmfMean D`; the standard deviation is
`σ = √(pmfVar D)`, so `σ² = pmfVar D`.

**Formalization Note.** Every statement using it assumes a finite third absolute moment, under which
the series converges absolutely. -/
noncomputable def pmfVar (D : PMF ℤ) : ℝ :=
  ∑' z : ℤ, ((z : ℝ) - pmfMean D) ^ 2 * (D z).toReal

end Supplement

end TwoFoldOPI


