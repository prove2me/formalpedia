-- Prove2me | Definitions.Def_BeatingGV42_classNumber
-- name    : BeatingGV42_classNumber
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:48.246662+00:00
-- url     : https://prove2.me/theorems/aa8778c8-e40d-4855-8116-73e04c8cea18
-- title:
--   The class number $h_F$
-- statement:
--   The **class number** of a function field $F/\mathbb F_Q$ is $h_F=|\mathcal C^0_F|$, the number of divisor classes of degree $0$. Whenever $F$ has a rational place, $|\mathcal C^m_F|=h_F$ for every integer $m$, so $h_F$ normalizes the uniform average over $\mathcal C^m_F$ in Lemma 4.3; its growth along optimal sequences is Lemma 4.8, eq. (4.13).
--
--   **Formalization Note** $h_F$ = `Nat.card (AlgebraicCurve.Pic0 k F)`. `Nat.card` of an infinite type is $0$; for a function field over a finite field the group is finite, so the junk value does not occur.
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), §3, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

namespace BeatingGV42

/-- **The class number** `h_F = |C^0_F|` (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §3, p.11 (PDF p.13)).

**Formalization Note** `C^0_F` is the platform's `AlgebraicCurve.Pic0 k F` (degree-zero divisors
modulo principal divisors) and `h_F = Nat.card (Pic0 k F)`. `Nat.card` of an infinite type is `0`;
for a function field over a finite field `Pic0` is finite (the class number formula
`AlgebraicCurve.LPolynomial_eval_one_eq_natCard_pic0` evaluates it), so the junk value does not
occur. -/
noncomputable def classNumber (k F : Type*) [Field k] [Field F] [Algebra k F] : ℕ :=
  Nat.card (Pic0 k F)

end BeatingGV42


