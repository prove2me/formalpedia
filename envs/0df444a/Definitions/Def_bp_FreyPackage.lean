-- Prove2me | Definitions.Def_bp_FreyPackage
-- name    : bp_FreyPackage
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-05-20T01:04:59.387435+00:00
-- url     : https://prove2.me/theorems/5f396031-c470-44f3-bdae-c18e4024acc3
-- statement:
--   **Frey package.** A bundle $(a, b, c, p)$ of nonzero pairwise-coprime integers $a, b, c$ and a prime $p \geq 5$ with $a \equiv 3 \pmod 4$, $b$ even, and $a^p + b^p = c^p$. From a counterexample to FLT one can always normalize to a Frey package; the associated Frey curve $Y^2 = X(X - a^p)(X + b^p)$ then has a mod-$p$ Galois representation that the Mazur and Wiles–Taylor–Wiles theorems show cannot exist. Mirrors `FreyPackage` in the [Imperial College FLT formalization](https://github.com/ImperialCollegeLondon/FLT) (blueprint Def 2.5.1).
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Nat.Prime.Basic

/-- A *Frey Package* is a 4-tuple `(a, b, c, p)` of three nonzero pairwise-coprime
integers `a`, `b`, `c` and a prime `p ≥ 5`, with `a ≡ 3 [ZMOD 4]`, `b ≡ 0 [ZMOD 2]`,
and `a^p + b^p = c^p`. These conditions guarantee that the Frey curve
`Y² = X(X − aᵖ)(X + bᵖ)` satisfies the running hypotheses of §4.1 of Serre [1987].
Mirrors `FreyPackage` from the Imperial College FLT formalization
(https://github.com/ImperialCollegeLondon/FLT, blueprint Def 2.5.1). -/
structure FreyPackage where
  a : ℤ
  b : ℤ
  c : ℤ
  ha0 : a ≠ 0
  hb0 : b ≠ 0
  hc0 : c ≠ 0
  p : ℕ
  pp : Nat.Prime p
  hp5 : 5 ≤ p
  hFLT : a ^ p + b ^ p = c ^ p
  hgcdab : gcd a b = 1
  ha4 : (a : ZMod 4) = 3
  hb2 : (b : ZMod 2) = 0


