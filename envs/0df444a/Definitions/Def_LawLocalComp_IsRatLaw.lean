-- Prove2me | Definitions.Def_LawLocalComp_IsRatLaw
-- name    : LawLocalComp_IsRatLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:11:19.953134+00:00
-- url     : https://prove2.me/theorems/2906e99b-69ab-4c62-8f9b-0c643c84df16
-- title:
--   Rational law
-- statement:
--   A law $X$ is **rational** if every atom $x$ of $X$ and its mass $\mathbb P(X=x)$ are rational numbers. The paper's maps see "one finite nonnegative rational law" and return rational laws.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), §1, p.2

import Mathlib
import Definitions.Def_LawLocalComp_Law

namespace LawLocalComp

/-- **A rational law.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), §1, p.2 ("one finite nonnegative rational law"; "rational law-local conditional-mean maps").

`IsRatLaw X`: every atom of `X` and the mass of every atom are rational numbers. -/
def IsRatLaw (X : Law) : Prop :=
  ∀ x ∈ X.w.support, (∃ q : ℚ, (q : ℝ) = x) ∧ ∃ q : ℚ, (q : ℝ) = X.w x

end LawLocalComp


