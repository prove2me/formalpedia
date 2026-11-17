-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_pmfMean
-- name    : TwoFoldOPI_Supplement_pmfMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:53:34.841923+00:00
-- url     : https://prove2.me/theorems/3ca1e837-84ad-4e42-900f-d931e0562bcd
-- title:
--   The mean $\mu$ of a distribution on $\mathbb Z$
-- statement:
--   For a distribution $D$ on $\mathbb Z$, its mean is
--   $$\mu(D)=\sum_{z\in\mathbb Z}z\,D(z).$$
--
--   **Formalization Note** The series is a real `tsum`; every statement using it assumes a finite third absolute moment, so the series converges absolutely.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.4, Theorem 5.38, p. 34

import Mathlib

namespace TwoFoldOPI

namespace Supplement

/-- **The mean `µ` of a distribution on `ℤ`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.4, Theorem 5.38, p.34: "For r ∈ [R], let µ_r, σ_r be the mean and standard deviation of
D_r."

`pmfMean D = Σ_{z ∈ ℤ} z · D(z)`.

**Formalization Note.** The series is a `tsum` of reals. Every statement using it assumes a finite
third absolute moment, which makes the series absolutely convergent, so the `tsum` is the mean. -/
noncomputable def pmfMean (D : PMF ℤ) : ℝ :=
  ∑' z : ℤ, (z : ℝ) * (D z).toReal

end Supplement

end TwoFoldOPI


