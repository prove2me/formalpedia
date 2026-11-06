-- Prove2me | Definitions.Def_DRSub4633_resid
-- name    : DRSub4633_resid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:03:58.693781+00:00
-- url     : https://prove2.me/theorems/b2f62e38-8581-49b7-b7d7-6290cec900e9
-- title:
--   The normalized residual $F=f-\ell$
-- statement:
--   $$F(z)=f(z)-\ell(z).$$
--   By Lemma 4.3 it is nonnegative and DR-submodular on the cube and vanishes at $0$, $(0_S,1_L)$ and $1$.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eq. (11), p.10

import Mathlib
import Definitions.Def_DRSub4633_affNorm

namespace DRSub4633

/-- **The normalized residual `F(z) = f(z) − ℓ(z)`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, Eq. (11), p.10. -/
noncomputable def resid {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f z - affNorm f x z

end DRSub4633


