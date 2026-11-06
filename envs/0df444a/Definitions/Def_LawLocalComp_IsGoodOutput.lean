-- Prove2me | Definitions.Def_LawLocalComp_IsGoodOutput
-- name    : LawLocalComp_IsGoodOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:12:26.796449+00:00
-- url     : https://prove2.me/theorems/40af3db5-869d-425d-a18f-036692b55fee
-- title:
--   Rational conditional-mean output preserving means and point masses
-- statement:
--   An output law $Y$ for the input law $X$ is **admissible** in the sense of Theorem 1.1 when:
--   1. $Y$ is rational;
--   2. $Y$ is a conditional-mean replacement of $X$;
--   3. $\mathbb E Y=\mathbb E X$;
--   4. if $X$ is the point mass at $t$, then so is $Y$.
--
--   These are the properties "rational law-local conditional-mean maps … preserve means and point masses" of Theorem 1.1.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 1.1, p.2

import Mathlib
import Definitions.Def_LawLocalComp_IsRatLaw
import Definitions.Def_LawLocalComp_mean
import Definitions.Def_LawLocalComp_IsCondMean

namespace LawLocalComp

/-- **A rational conditional-mean output preserving means and point masses.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 1.1, p.2 ("rational law-local conditional-mean maps … preserve means and point
masses").

`IsGoodOutput X Y`: `Y` is rational, `Y` is a conditional-mean replacement of `X`, `E Y = E X`,
and if `X` is the point mass at `t` then so is `Y`. -/
def IsGoodOutput (X Y : Law) : Prop :=
  IsRatLaw Y ∧ IsCondMean X Y ∧ mean Y = mean X ∧
    ∀ t : ℝ, X.w = Finsupp.single t 1 → Y.w = Finsupp.single t 1

end LawLocalComp


