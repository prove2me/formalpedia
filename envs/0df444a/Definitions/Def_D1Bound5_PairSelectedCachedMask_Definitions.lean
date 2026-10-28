-- Prove2me | Definitions.Def_D1Bound5_PairSelectedCachedMask_Definitions
-- name    : D1Bound5_PairSelectedCachedMask_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:35:18.466526+00:00
-- url     : https://prove2.me/theorems/551c25f8-f89d-49c9-a4b6-cc065ef3e927
-- title:
--   Pair Selected Cached Mask
-- statement:
--   Check one supplied rejecting position in the existing ordered cached sieve. The same index selects the mask and both cached residues. Missing or out-of-range entries reject the certificate; they never supply a default. The named objects in this bundle include `pairSelectedCachedMaskRejectBool`.
-- source:
--   D1Bound5/PairSelectedCachedMask.lean, lines 5-12, SHA-256 842d5e0cce863d3301c8c65c34a04d2d07c08d156761bf506cdbbebcdd0db1f4. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions

section
namespace D1Bound5

/-- Check one supplied rejecting position in the existing ordered cached
sieve. The same index selects the mask and both cached residues. Missing or
out-of-range entries reject the certificate; they never supply a default. -/
def pairSelectedCachedMaskRejectBool (tau nu : ℤ) (sieve : List (ℕ × ℕ))
    (xs ys : List (ℕ × ℕ)) (i : ℕ) : Bool :=
  match sieve[i]?, xs[i]?, ys[i]? with
  | some (k, mask), some u, some v => !pairResidueMaskBool tau nu k mask u v
  | _, _, _ => false



end D1Bound5
end


