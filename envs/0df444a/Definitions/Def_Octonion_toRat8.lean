-- Prove2me | Definitions.Def_Octonion_toRat8
-- name    : Octonion_toRat8
-- status  : Definition
-- author  : @jawneeboy
-- created : 2026-09-23T13:25:27.464994+00:00
-- url     : https://prove2.me/theorems/03723fbf-31de-4b6a-9d0c-089d264bf124
-- title:
--   Rational octonion coordinate equivalence
-- statement:
--   The eight quaternion-pair coordinates define an equivalence $$\mathbb O_{\mathbb Q}\simeq(\mathbb Q^4)\times(\mathbb Q^4).$$ It supplies decidable equality for finite computations.
-- source:
--   Standard reference: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345. Relevant topics appear in Chapter 6 (composition algebras), Chapter 9 (octavian integers), and Section 10.1 (the 240 octavian units), as confirmed by the publisher's table of contents. Supporting exposition: John Baez, Integral Octonions (Part 6), September 17, 2013, https://math.ucr.edu/home/baez/octonions/integers/integers_6.html. These references concern the classical mathematics. This contribution supplies Lean definitions and machine-checked proofs in the stated coordinate convention; it does not claim new mathematical results or reproduce a particular proof from the book. The topic references do not assert that the exact Lean statement occurs there. Verification of the book references is limited to its table of contents, not a statement-by-statement comparison with the book; no page-specific or numbered theorem attribution is claimed. Local formalization: Basic/Def_Octonion_toRat8.lean; SHA-256 e98895ff542d2dd7bde6668e4c22b75a08d82cf3d834574be7bc9a620f8392d2.

import Definitions.Def_Octonion_octonions
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

namespace Octonion

/-- Coordinate equivalence over `ℚ`, used for decidable equality and computation. -/
def toRat8 : octonions ℚ ≃ (ℚ × ℚ × ℚ × ℚ) × (ℚ × ℚ × ℚ × ℚ) :=
  (toProd ℚ).trans ((Quaternion.equivProd ℚ).prodCongr (Quaternion.equivProd ℚ))

instance instDecidableEqRat : DecidableEq (octonions ℚ) := toRat8.decidableEq

end Octonion


