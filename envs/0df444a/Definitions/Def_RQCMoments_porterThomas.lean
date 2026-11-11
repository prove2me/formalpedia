-- Prove2me | Definitions.Def_RQCMoments_porterThomas
-- name    : RQCMoments_porterThomas
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:08:06.767203+00:00
-- url     : https://prove2.me/theorems/57fb67b2-f95c-4a68-ba69-7a48c25567f2
-- title:
--   Porter–Thomas law $\mathrm{Beta}(1,N-1)$
-- statement:
--   For an integer $N\ge 2$, the **Porter–Thomas law** is the Beta distribution $\mathrm{Beta}(1,N-1)$ on $[0,1]$, with density
--   $$
--   f(x)=(N-1)(1-x)^{N-2},\qquad 0<x<1,
--   $$
--   and distribution function $F(z)=1-(1-z)^{N-1}$ for $z\in[0,1]$.
--
--   It is the law of a single output probability $|U_{xy}|^2$ of a Haar random $U\in U(N)$ (§2.3), and the comparison law in Theorem 4.9.
--
--   **Formalization Note** Mathlib's `ProbabilityTheory.betaMeasure 1 (N - 1)`, a measure on $\mathbb R$ concentrated on $(0,1)$; it is a probability measure for $N\ge 2$.
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), (17), §2.3, Theorem 4.9, p.15 and p.29 (PDF pp.17, 31)

import Mathlib

set_option autoImplicit false

namespace RQCMoments

/-- The Porter–Thomas law `Beta(1, N − 1)` on `[0,1]`, with density `(N−1)(1−x)^{N−2}`
(Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), (17), p.15; Theorem 4.9, p.29; (77), p.25 with `D = N − 1`).

**Formalization Note** This is Mathlib's `ProbabilityTheory.betaMeasure 1 (N − 1)` (real
parameter `N − 1`), a measure on `ℝ` concentrated on `(0,1)`; it is a probability measure for
`N ≥ 2`. Its distribution function at `z` is `porterThomas N (Set.Iic z)`. -/
noncomputable def porterThomas (N : ℕ) : MeasureTheory.Measure ℝ :=
  ProbabilityTheory.betaMeasure 1 ((N : ℝ) - 1)

end RQCMoments


