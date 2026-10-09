-- Prove2me | Definitions.Def_Octonion_IsCayleyUnit
-- name    : Octonion_IsCayleyUnit
-- status  : Definition
-- author  : @jawneeboy
-- created : 2026-09-23T13:27:57.358737+00:00
-- url     : https://prove2.me/theorems/f8672ad6-f08d-46a4-b0f6-a8d151b9c6b4
-- title:
--   Two-sided units of the chosen Cayley order
-- statement:
--   Use the Cayley–Dickson model $\mathbb O_R=\mathbb H_R\times\mathbb H_R$, with $(a,b)(c,d)=(ac-\bar d b,da+b\bar c)$ and $\overline{(a,b)}=(\bar a,-b)$. Let $\mathcal C\subset\mathbb O_{\mathbb Q}$ be the chosen Cayley order: $x=a/2$ for $a\in\mathbb Z^8$, with the mask $\sum_{a_i\text{ odd}}2^i$ in $M=\{0,15,51,60,86,89,101,106,149,154,166,169,195,204,240,255\}$. Call $x$ a unit of $\mathcal C$ when $x\in\mathcal C$ and there is $y\in\mathcal C$ with $xy=yx=1$. Equivalently, $$x\in\mathcal C\quad\land\quad\exists y\in\mathcal C,\ xy=yx=1.$$ This definition requires the inverse itself to belong to the order.
-- source:
--   Standard reference: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345. Relevant topics appear in Chapter 6 (composition algebras), Chapter 9 (octavian integers), and Section 10.1 (the 240 octavian units), as confirmed by the publisher's table of contents. Supporting exposition: John Baez, Integral Octonions (Part 6), September 17, 2013, https://math.ucr.edu/home/baez/octonions/integers/integers_6.html. These references concern the classical mathematics. This contribution supplies Lean definitions and machine-checked proofs in the stated coordinate convention; it does not claim new mathematical results or reproduce a particular proof from the book. The topic references do not assert that the exact Lean statement occurs there. Verification of the book references is limited to its table of contents, not a statement-by-statement comparison with the book; no page-specific or numbered theorem attribution is claimed. Local formalization: Basic/Def_Octonion_IsCayleyUnit.lean; SHA-256 ce7e0ca09e1ec9057ca4b87cd797616cff631d1a13a7b9c0be0de0fc6a690b6a.

import Definitions.Def_Octonion_cayleyIntegers
import Definitions.Def_Octonion_octonions
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace Octonion

/-- A Cayley unit is a Cayley integer admitting a two-sided inverse that is again a Cayley
integer. For example, the scalar `2` belongs to the order, but its ambient inverse
`1/2` does not, so `2` is not a Cayley unit. The definition requires the same witness
to satisfy both inverse equations. For a Cayley integer of squared norm one,
`isCayleyUnit_iff_normSq` constructs conjugation as such a two-sided inverse. -/
def IsCayleyUnit (x : octonions ℚ) : Prop :=
  isCayley x ∧ ∃ y, isCayley y ∧ x * y = 1 ∧ y * x = 1

end Octonion


