-- Prove2me | Definitions.Def_BeatingGV42_degClasses
-- name    : BeatingGV42_degClasses
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:34.457107+00:00
-- url     : https://prove2.me/theorems/4299fc0e-28d3-4a55-99c0-c1286120ebdc
-- title:
--   Divisor classes of degree $m$, $\mathcal C^m_F$
-- statement:
--   Let $F/\mathbb F_Q$ be a function field and $\mathcal C_F$ its divisor class group (divisors modulo principal divisors), with $[G]$ the class of a divisor $G$. For an integer $m$, the set of **divisor classes of degree $m$** is
--   $$
--   \mathcal C^m_F=\{[G]\in\mathcal C_F:\deg G=m\}.
--   $$
--   Lemma 4.3 averages the weight distributions of the codes $C_L(D,G_\gamma)$ over $\gamma\in\mathcal C^m_F$.
--
--   **Formalization Note** $\mathcal C_F$ is the platform's `AlgebraicCurve.Pic k F`; a class lies in $\mathcal C^m_F$ when it is the class of some divisor of degree $m$. Principal divisors have degree $0$ (part of `IsCurveOver`), so the degree of a class is well defined.
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), §3, p.11 (PDF p.13), and §4.2, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

namespace BeatingGV42

/-- **Divisor classes of degree `m`** `C^m_F = {[G] ∈ C_F : deg[G] = m}`
(Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §3, p.11 (PDF p.13), and §4.2, p.13 (PDF p.15)): "We write C_F for the divisor class group,
[G] for the class of G, and C^m_F for the set of classes of degree m."

**Formalization Note** `C_F` is the platform's `AlgebraicCurve.Pic k F` (divisors modulo principal
divisors), and `C^m_F` is the set of classes of some divisor of degree `m`. Since principal divisors
have degree `0` (part of `IsCurveOver`), a class lies in at most one `C^m_F`. -/
def degClasses (k F : Type*) [Field k] [Field F] [Algebra k F] (m : ℤ) : Set (Pic k F) :=
  {γ | ∃ G : Divisor k F, Divisor.degree G = m ∧ (QuotientAddGroup.mk G : Pic k F) = γ}

end BeatingGV42


