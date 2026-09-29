-- Prove2me | Definitions.Def_GeneralCK_LogBounds
-- name    : GeneralCK_LogBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T20:48:36.324531+00:00
-- url     : https://prove2.me/theorems/c2cabe70-d77f-47d8-a7d5-c26890dc4e64
-- title:
--   Rational logarithm interval checker
-- statement:
--   For a rational number $w$ and a natural number $n$, define $$L_n(w)=2\sum_{i=0}^{n-1}\frac{w^{2i+1}}{2i+1},\qquad U_n(w)=L_n(w)+\frac{2w^{2n+1}}{1-w^2}.$$ For rational bounds $\ell,u$, the Boolean checker accepts precisely when $0\le w<1$, $\ell\le L_n(w)$, and $U_n(w)\le u$. All checker arithmetic is exact over the rationals. Its separate soundness theorem connects acceptance to a real logarithm enclosure used by the Courtade–Kumar interval certificates.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/LogBounds.lean#L10-L20

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace GeneralCK.Certificates
open scoped BigOperators

/-- Rational partial sum for log((1+w)/(1-w)). -/
def logLower (w : ℚ) (n : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range n, w ^ (2 * i + 1) / (2 * i + 1)

/-- A conservative, proved Taylor remainder. -/
def logUpper (w : ℚ) (n : ℕ) : ℚ :=
  logLower w n + 2 * w ^ (2 * n + 1) / (1 - w ^ 2)

/-- Acceptance uses exact rational arithmetic only. -/
def checkLog (w : ℚ) (n : ℕ) (lo hi : ℚ) : Bool :=
  decide (0 ≤ w ∧ w < 1 ∧ lo ≤ logLower w n ∧ logUpper w n ≤ hi)



end GeneralCK.Certificates


