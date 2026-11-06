-- Prove2me | Definitions.Def_DRSub4633_aPath
-- name    : DRSub4633_aPath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:57:36.006714+00:00
-- url     : https://prove2.me/theorems/a18d3977-eae8-4750-94e4-691a1f9730fc
-- title:
--   The small-coordinate path $a(t)$
-- statement:
--   For the state $x$, a time $t$ and a small coordinate $j$ (with $u=x_S$),
--   $$a_j(t)=1-e^{-tu_j}.$$
--   At $t=1$ this is the recovered small coordinate $h(x_j)$.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eq. (10), p.10

import Mathlib

namespace DRSub4633

/-- **The small-coordinate path `a_j(t) = 1 − e^(−t u_j)`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, Eq. (10),
p.10, with `u = x_S`.

**Formalization Note.** Defined for every coordinate `j`; only its values on the small coordinates
(`x_j ≤ s`) are read. -/
noncomputable def aPath {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : Fin n → ℝ :=
  fun j => 1 - Real.exp (-(t * x j))

end DRSub4633


