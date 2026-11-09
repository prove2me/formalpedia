-- Prove2me | Definitions.Def_GevreyGibbsSep_torusRep
-- name    : GevreyGibbsSep_torusRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:47.511142+00:00
-- url     : https://prove2.me/theorems/74022afc-ebbf-452f-a01c-c099ee428609
-- title:
--   Representative in $[0,2\pi)^d$ of a torus point
-- statement:
--   Every point $x\in\mathbb T^d$ has a unique representative in $[0,2\pi)^d$. Oracle answers are "evaluated at any representative of $x$"; since all derivatives of periodic functions are periodic, this choice does not matter.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Definition B.2, p.34

import Mathlib
import Definitions.Def_GevreyGibbsSep_Torus

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The representative of a point of `T^d` in `[0, 2π)^d` (arXiv:2608.24527 (sha256
d4fd40eb…), Definition B.2, p.34: the answer is "evaluated at any representative of x"). -/
noncomputable def torusRep {d : ℕ} (x : Torus d) : Fin d → ℝ :=
  fun i => ((AddCircle.equivIco (2 * Real.pi) 0 (x i) : Set.Ico (0 : ℝ) (0 + 2 * Real.pi)) : ℝ)

end GevreyGibbsSep


