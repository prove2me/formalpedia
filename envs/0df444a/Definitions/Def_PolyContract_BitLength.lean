-- Prove2me | Definitions.Def_PolyContract_BitLength
-- name    : PolyContract_BitLength
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:40:49.493556+00:00
-- url     : https://prove2.me/theorems/42d87b01-74f5-4c2b-9ff7-1c75a335a9ed
-- title:
--   Bit-length predicates of Theorem 3.6
-- statement:
--   Two predicates on real numbers:
--
--   1. $r$ is a quotient of two integers of absolute value less than $2^\nu$;
--   2. $r$ is a rational $a/b$ whose numerator and denominator have bit length at most $B$, i.e. $|a|,|b|<2^B$.
--
--   They express the hypothesis and the conclusion of Theorem 3.6.
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Theorem 3.6, p.8 (PDF p.9)

import Mathlib

set_option autoImplicit false

namespace PolyContract

/-- `r` is a quotient of two integers of absolute value less than `2^ν` (Klimm, Lippke, Warode,
arXiv:2611.04934, version of November 3, 2026, sha256 18cfc0a5…, Theorem 3.6, p.8). -/
def IsSmallQuot (ν : ℕ) (r : ℝ) : Prop :=
  ∃ a b : ℤ, b ≠ 0 ∧ |a| < 2 ^ ν ∧ |b| < 2 ^ ν ∧ r = a / b

/-- `r` is a rational whose numerator and denominator have bit length at most `B`
(arXiv:2611.04934, Theorem 3.6, p.8): `r = a/b` with integers `b ≠ 0` and `|a|, |b| < 2^B`.

**Formalization Note** An integer has bit length at most `B` iff its absolute value is less
than `2^B`. -/
def HasBitLength (B : ℕ) (r : ℝ) : Prop :=
  ∃ a b : ℤ, b ≠ 0 ∧ a.natAbs < 2 ^ B ∧ b.natAbs < 2 ^ B ∧ r = a / b

end PolyContract


