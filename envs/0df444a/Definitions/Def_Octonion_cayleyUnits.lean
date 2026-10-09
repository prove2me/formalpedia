-- Prove2me | Definitions.Def_Octonion_cayleyUnits
-- name    : Octonion_cayleyUnits
-- status  : Definition
-- author  : @jawneeboy
-- created : 2026-09-23T13:28:05.765882+00:00
-- url     : https://prove2.me/theorems/978e11b1-a939-43b9-8706-80f0c969241e
-- title:
--   An explicit finite list of Cayley units
-- statement:
--   Let $\mathcal C\subset\mathbb O_{\mathbb Q}$ be the chosen Cayley order: $x=a/2$ for $a\in\mathbb Z^8$, with the mask $\sum_{a_i\text{ odd}}2^i$ in $M=\{0,15,51,60,86,89,101,106,149,154,166,169,195,204,240,255\}$. Let $U$ consist of the sixteen signed coordinate vectors $\pm e_i$ and all vectors supported on a weight-four mask in $M$, with each supported coordinate independently equal to $\pm\tfrac12$. The later cardinality and classification theorems establish $$|U|=240,\qquad U=\{x\in\mathcal C:x\text{ has a two-sided inverse in }\mathcal C\}.$$ The definition itself is a finite enumeration with duplicates removed.
-- source:
--   Standard reference: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345. Relevant topics appear in Chapter 6 (composition algebras), Chapter 9 (octavian integers), and Section 10.1 (the 240 octavian units), as confirmed by the publisher's table of contents. Supporting exposition: John Baez, Integral Octonions (Part 6), September 17, 2013, https://math.ucr.edu/home/baez/octonions/integers/integers_6.html. These references concern the classical mathematics. This contribution supplies Lean definitions and machine-checked proofs in the stated coordinate convention; it does not claim new mathematical results or reproduce a particular proof from the book. The topic references do not assert that the exact Lean statement occurs there. Verification of the book references is limited to its table of contents, not a statement-by-statement comparison with the book; no page-specific or numbered theorem attribution is claimed. Local formalization: Basic/Def_Octonion_cayleyUnits.lean; SHA-256 85643aceb5e5c0fe6effe7c5604cd476624b8c233ed55c39ba8e9c7f347144bb.

import Definitions.Def_Octonion_cayleyIntegers
import Definitions.Def_Octonion_octonions
import Definitions.Def_Octonion_toRat8
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# The 240 units of the Cayley integers

The units of `cayleyIntegers` are exactly its norm-one elements (`normSq_mul` plus integrality of
the norm gives one direction, `x · conj x = 1` the other), so enumerating them means solving
`Σ aᵢ² = 4` for doubled coordinate vectors `a` with Hamming parity pattern. Odd coordinates
contribute at least `1` each and their count lies in `{0, 4, 8}`, so there are exactly three
cases:

* pattern `0`: all coordinates even — one coordinate `±2`, giving the 16 units `±basisVec k`;
* a weight-`4` pattern: four odd coordinates, each `±1`, giving `14 · 16 = 224` units;
* pattern `255`: eight odd coordinates already have norm `≥ 2` — no units.

Total `16 + 224 = 240`. The half-integral units are coded by two bit masks `(m, t)`:
the weight-four parity mask `m` and a sign mask `t` marking where the sign is `+`
(only `t` restricted to `m` is visible). The integral units are listed separately.
That this is *exactly* the set of invertible Cayley integers is `mem_cayleyUnits_iff`.
-/

open Quaternion

namespace Octonion

/-- The fourteen weight-`4` codewords of `cayleyMasks`: the parity patterns on which a unit can
have half-integral coordinates. The all-ones word is too heavy to carry norm one. -/
def weight4Masks : Finset ℕ :=
  cayleyMasks.filter fun m => ((Finset.univ : Finset (Fin 8)).filter fun i => Nat.testBit m i.val).card = 4

/-- Signed half-vector of a mask pair: coordinates `±1/2` on the bits of `m` (`+` where `t` has a
bit) and `0` elsewhere. Doubled, this is an integer vector with parity pattern `patOfMask m`. Only the
restriction of `t` to `m` matters; other sign bits are ignored. -/
def signedRep (m t : ℕ) : octonions ℚ :=
  halfOf fun i => if Nat.testBit m i.val then if Nat.testBit t i.val then 1 else -1 else 0

/-- The set of all 240 units of the Cayley integers: the 16 sign vectors `±eₖ` (mask `0`) and
the 224 half-vectors with four odd coordinates on a weight-`4` Hamming word. The sign mask `t`
ranges over all of `2⁸`; only its restriction to `m` is visible, so the enumeration lists each
unit several times and the `Finset` deduplicates. That this is *exactly* the set of invertible
Cayley integers is `mem_cayleyUnits_iff`. -/
def cayleyUnits : Finset (octonions ℚ) :=
  ((Finset.univ : Finset (Fin 8)).biUnion fun k => {basisVec k, -basisVec k}) ∪
    weight4Masks.biUnion fun m => (Finset.range 256).image (signedRep m)

end Octonion


