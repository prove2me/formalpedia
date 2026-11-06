-- Prove2me | Definitions.Def_HOTrap_taylorConst
-- name    : HOTrap_taylorConst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:46:01.123013+00:00
-- url     : https://prove2.me/theorems/6c3ff437-a277-4db8-92c7-d0bc6c67c885
-- title:
--   Taylor constants $a_{j,\beta}$
-- statement:
--   For integers $j\ge0$, the Taylor constants are
--   $$
--   a_{j,\beta}:=\prod_{i=1}^j\frac1{\beta+i},\qquad a_{0,\beta}=1.
--   $$
--
--   They are the constants of the Hölder Taylor remainder, Lemma A.3.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Appendix A, Notation, p.53

import Mathlib

namespace HOTrap

/-- **The Taylor constants** `a_{j,β} := ∏_{i=1}^j 1/(β+i)`, with `a_{0,β} = 1`. Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Appendix A,
Notation, p.53. -/
noncomputable def taylorConst (j : ℕ) (β : ℝ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 j, (β + (i : ℝ))⁻¹

end HOTrap


