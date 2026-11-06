-- Prove2me | Definitions.Def_DRSub4633_affNorm
-- name    : DRSub4633_affNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:02:44.934675+00:00
-- url     : https://prove2.me/theorems/56dc8c92-27fe-4e04-b50e-42256a36a9f4
-- title:
--   The affine normalizer $\ell$
-- statement:
--   $$\ell(z)=f(0)+\langle d,z\rangle,$$
--   with the chain increments $d$ of $f$ at the state $x$.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eq. (11), p.10

import Mathlib
import Definitions.Def_DRSub4633_chainD

namespace DRSub4633

/-- **The affine normalizer `ℓ(z) = f(0) + ⟨d, z⟩`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, Eq. (11), p.10. -/
noncomputable def affNorm {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f 0 + ∑ j, chainD f x j * z j

end DRSub4633


