-- Prove2me | Definitions.Def_D1Bound5_PairResidueMaskNat_Definitions
-- name    : D1Bound5_PairResidueMaskNat_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:26:21.635465+00:00
-- url     : https://prove2.me/theorems/e5d783ed-9ee3-4e52-b2ce-cf0c3c8e0df8
-- title:
--   Pair Residue Mask Nat
-- statement:
--   The existing coordinate mask with natural-number polynomial arithmetic and one final reduction per coordinate. The two integer parameters are still represented by their exact residues. All natural inputs are permitted, even when they are not reduced or do not come from a valid cached signature. The named objects in this bundle include `pairResidueMaskNatBool`.
-- source:
--   D1Bound5/PairResidueMaskNat.lean, lines 5-15, SHA-256 f838a6119a4b84b5889032242bf1d0b6ceb9a78264fea0197c14bf45d2cae39f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

section
namespace D1Bound5

/-- The existing coordinate mask with natural-number polynomial arithmetic
and one final reduction per coordinate. The two integer parameters are still
represented by their exact residues. All natural inputs are permitted, even
when they are not reduced or do not come from a valid cached signature. -/
def pairResidueMaskNatBool (tau nu : ℤ) (k mask : ℕ) (u v : ℕ × ℕ) : Bool :=
  let p := k + 1
  let nn := (-(nu : ZMod p)).val
  let tt := (tau : ZMod p).val
  let real := (u.1 * v.1 + nn * u.2 * v.2 + 1) % p
  let imag := (u.1 * v.2 + u.2 * v.1 + tt * u.2 * v.2) % p
  mask.testBit (real * p + imag)



end D1Bound5
end


