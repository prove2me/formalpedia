-- Prove2me | Definitions.Def_CubeSampling_Lambda
-- name    : CubeSampling_Lambda
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:15:13.606961+00:00
-- url     : https://prove2.me/theorems/19431f24-4a9e-4b28-979d-e4d7fcebbb2b
-- title:
--   The exponent $\Lambda_{d,k} = d\,\Psi(k/d)$
-- statement:
--   $$
--   \Lambda_{d,k} = d\,\Psi(k/d).
--   $$
--   It is the leading exponent of the parametric sample threshold: $N_{\mathrm{par}} = (m+t)\,e^{\Lambda_{d,k} \pm O(k^{1/3})}$.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 1.1, p.4

import Mathlib
import Definitions.Def_CubeSampling_Psi

namespace CubeSampling

/-- The exponent `Λ_{d,k} = d Ψ(k/d)` (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §1.1, p.4). -/
noncomputable def Lambda (d k : ℕ) : ℝ := d * Psi ((k : ℝ) / d)

end CubeSampling


