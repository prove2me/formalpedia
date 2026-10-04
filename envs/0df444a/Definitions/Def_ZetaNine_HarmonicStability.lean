-- Prove2me | Definitions.Def_ZetaNine_HarmonicStability
-- name    : ZetaNine_HarmonicStability
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-02T14:08:35.670997+00:00
-- url     : https://prove2.me/theorems/f0f5ed09-0e3c-48af-b45b-f53a12ecf11f
-- title:
--   Generalized harmonic sums and actual log denominators
-- statement:
--   For a rational number $q$, define $\ell(q)=\log\operatorname{den}(q)$ using its reduced positive denominator, with $\operatorname{den}(0)=1$. For natural $s,N$, define the actual rational generalized harmonic sum $H_N^{(s)}=\sum_{j=1}^Nj^{-s}$. These are definitions only; the prime-number-theorem growth rate is not assumed.
-- source:
--   https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02; research/harmonic-denominator-stability-2026-10-01.md, section 2 clearing bound and section 3 Lemma 2 / Corollary 3.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

/-! Lightweight definition source for the formal integration of
`HarmonicStability.lean`. It contains only the two actual mathematical
objects and no theorem assumptions, prime-number-theorem axiom, or proof.
The root agent will install these definitions in the shared Definitions
module and replace the standalone proof file's matching definition block
by that import. -/

set_option autoImplicit false

open scoped BigOperators

namespace ZetaNine.HarmonicStability

/-- Natural logarithm of the reduced positive rational denominator. -/
noncomputable def logDen (q : ℚ) : ℝ := Real.log (q.den : ℝ)

/-- The generalized harmonic rational number, including `N=0` and `s=0`. -/
def harmonicPower (s N : ℕ) : ℚ :=
  ∑ j ∈ Finset.Icc 1 N, 1 / (j : ℚ) ^ s

end ZetaNine.HarmonicStability


