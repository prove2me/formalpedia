-- Prove2me | Definitions.Def_MatrixSpencer_gam
-- name    : MatrixSpencer_gam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:07.968647+00:00
-- url     : https://prove2.me/theorems/8d09d283-ff95-4aeb-986e-4c52e915a67f
-- title:
--   The standard Gaussian measure $\gamma_n$
-- statement:
--   The standard Gaussian measure $\gamma_n$ on $\mathbb R^n$: under it, $g=(g_1,\dots,g_n)$ has independent standard Gaussian coordinates. Every probability and expectation in the small-ball part of the mission is with respect to this probability measure.
--
--   **Formalization Note** This is Mathlib's `ProbabilityTheory.stdGaussian` on `E n`.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), §2.1, p.6

import Mathlib
import Definitions.Def_RBMSensitivity_E
open RBMSensitivity (E)

namespace MatrixSpencer

/-- **The standard Gaussian measure `γₙ`.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), §2.1, p.6: "We denote by γₙ the standard Gaussian measure on ℝⁿ. Unless otherwise
specified, g = (g₁, …, gₙ) ∼ γₙ has independent standard Gaussian coordinates."

**Formalization Note.** This is Mathlib's `ProbabilityTheory.stdGaussian` on the Euclidean space
`E n`, a probability measure. Its coordinates in the standard basis are independent `N(0, 1)`. -/
noncomputable abbrev gam (n : ℕ) : MeasureTheory.Measure (E n) :=
  ProbabilityTheory.stdGaussian (E n)

end MatrixSpencer


