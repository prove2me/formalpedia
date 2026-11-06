-- Prove2me | Definitions.Def_LawLocalComp_IsListRep
-- name    : LawLocalComp_IsListRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:11:20.150743+00:00
-- url     : https://prove2.me/theorems/e30dcdc1-51f3-4a77-9061-bcfbe5ac12da
-- title:
--   A list of (atom, mass) pairs represents a law
-- statement:
--   A list $\ell$ of rational pairs $(x,m)$ **represents** a law $X$ if all its entries are nonnegative and, for every $x$, $\mathbb P(X=x)$ is the sum of the masses listed at the atom $x$. Atoms may repeat, in any order.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), §1, p.2; §3, p.5

import Mathlib
import Definitions.Def_LawLocalComp_Law
open Classical

namespace LawLocalComp

/-- **A list of rational (atom, mass) pairs represents a law.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), §1, p.2 ("one finite nonnegative rational law"); §3, p.5 ("Merge equal inputs").

`IsListRep ℓ X`: all entries of `ℓ` are nonnegative and, for every `x`, `P(X = x)` is the sum of the
masses listed at atom `x`. Repeated atoms are allowed and their masses add up. -/
def IsListRep (l : List (ℚ × ℚ)) (X : Law) : Prop :=
  (∀ z ∈ l, 0 ≤ z.1 ∧ 0 ≤ z.2) ∧
    ∀ x : ℝ, X.w x = (l.map fun z => if (z.1 : ℝ) = x then (z.2 : ℝ) else 0).sum

end LawLocalComp


