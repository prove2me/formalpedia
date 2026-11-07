-- Prove2me | Definitions.Def_LosslessQLTC_betaConst
-- name    : LosslessQLTC_betaConst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:18:10.918997+00:00
-- url     : https://prove2.me/theorems/4279693f-2d0c-4a30-bf1c-33e46394e8bc
-- title:
--   The ratio $\beta$ as a function of the degrees
-- statement:
--   In the soundness bound of Theorem 5.5, $\beta=\|V_3\|/\|V_2\|$. By biregularity $\|V_I\|=|V_\emptyset|/D'_I$, so
--
--   $$\beta=\frac{\sum_{|I|=3}1/D'_I}{\sum_{|I|=2}1/D'_I},$$
--
--   which is a positive constant depending only on the degree parameters. The same function evaluated at $D$ gives the ratio $\beta^{\mathrm{rev}}=\|V_1\|_{X^{\mathrm{rev}}}/\|V_2\|_{X^{\mathrm{rev}}}$ of the reversed complex.
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), proof of Theorem 5.5, p.43

import Mathlib
import Definitions.Def_LosslessQLTC_normC

namespace LosslessQLTC

variable {k : ℕ}

/-- The ratio `β = ∥V_3∥ / ∥V_2∥` of the proof of Theorem 5.5 (arXiv:2610.00525, held version,
sha256 d61f0ed9…, p.43), written as a function of the degrees: by biregularity
`∥V_I∥ = |V_∅| / D′_I`, so
`β = (Σ_{|I| = 3} 1/D′_I) / (Σ_{|I| = 2} 1/D′_I)` is "a positive constant depending only on the
degree parameters". The same function at `D` is the ratio `β^rev` of `X^rev`. -/
noncomputable def betaConst (D' : Fin k → ℕ) : ℝ :=
  (∑ I ∈ Finset.powersetCard 3 Finset.univ, 1 / (prodD D' I : ℝ)) /
    (∑ I ∈ Finset.powersetCard 2 Finset.univ, 1 / (prodD D' I : ℝ))

end LosslessQLTC


