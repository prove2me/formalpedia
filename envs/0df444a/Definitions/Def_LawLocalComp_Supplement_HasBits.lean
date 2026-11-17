-- Prove2me | Definitions.Def_LawLocalComp_Supplement_HasBits
-- name    : LawLocalComp_Supplement_HasBits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:03:37.37106+00:00
-- url     : https://prove2.me/theorems/777ae16d-8b14-4ede-8be9-678cc9147758
-- title:
--   A finite law with a description of at most $B$ bits
-- statement:
--   Let $X$ be a finite nonnegative law and $B$ a natural number. $X$ **has a description of at most $B$ bits** if there is a list $\ell$ of rational (atom, mass) pairs that represents $X$ (every entry is nonnegative and, for every $x$, $P(X = x)$ is the sum of the masses listed at atom $x$) and whose bit length is at most $B$.
--
--   In particular such an $X$ is rational. This is the notion in which the witness laws of Theorems 6.1 and 6.2 have "polynomial description" and in which the probe laws of Theorem 6.2 have polynomial "scalar encodings".
--
--   **Formalization Note** The representation predicate is the base mission's published `IsListRep`; repeated atoms in the list are allowed.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 6.1, p.9 ("witness description is polynomial in 1/ε, log N and accuracy bits"); Theorem 6.2, p.10; proof of Theorem 6.2, p.12 ("Law/probe bits are polynomial")

import Mathlib
import Definitions.Def_LawLocalComp_IsListRep
import Definitions.Def_LawLocalComp_Supplement_bitLen

namespace LawLocalComp

namespace Supplement

/-- **A law with a description of at most `B` bits.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 6.1, p.9 ("witness description is polynomial in 1/ε, log N and accuracy bits");
Theorem 6.2, p.10 ("Law/probe bits are polynomial, not necessarily expanded copy lists", p.12).

`HasBits X B`: some list of rational (atom, mass) pairs represents `X` (in the sense of the
published `IsListRep`) and has total bit length at most `B`. In particular `X` is rational. -/
def HasBits (X : Law) (B : ℕ) : Prop := ∃ l : List (ℚ × ℚ), IsListRep l X ∧ bitLen l ≤ B

end Supplement

end LawLocalComp


