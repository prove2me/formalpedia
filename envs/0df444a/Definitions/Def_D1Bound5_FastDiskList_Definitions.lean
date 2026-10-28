-- Prove2me | Definitions.Def_D1Bound5_FastDiskList_Definitions
-- name    : D1Bound5_FastDiskList_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:52:26.781466+00:00
-- url     : https://prove2.me/theorems/623322b6-3ffc-48bf-8ba6-aacf2c4f3b13
-- title:
--   Fast Disk List
-- statement:
--   The same complete normalized-coordinate disk as `disk`, computed as a list before quotienting by order. Kernel certificates can compare lists linearly without normalizing large finite-set duplicate-removal terms. The named objects in this bundle include `QuadInt.fastDiskCoordinates`, `QuadInt.fastDiskList`.
-- source:
--   D1Bound5/FastDiskList.lean, lines 7-8, SHA-256 60afd777700a3d6a319be0b0145eb86a6f1657a58e26c7947467097b7c482fed; D1Bound5/FastDiskList.lean, lines 19-28, SHA-256 60afd777700a3d6a319be0b0145eb86a6f1657a58e26c7947467097b7c482fed. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5
namespace QuadInt

def fastDiskCoordinates (r : ℤ) : List ℤ :=
  (List.range (2*r+1).toNat).map (fun n : ℕ => -r+(n : ℤ))



/-- The same complete normalized-coordinate disk as `disk`, computed as
a list before quotienting by order. Kernel certificates can compare lists
linearly without normalizing large finite-set duplicate-removal terms. -/
def fastDiskList (tau nu M : ℤ) : List (QuadInt tau nu) :=
  let r := Int.sqrt (4*M)
  let coords := fastDiskCoordinates r
  ((coords ×ˢ coords).filter (fun p : ℤ × ℤ =>
    decide (p.1 % 2 = (tau*p.2) % 2 ∧
      p.1^2+discriminant tau nu*p.2^2 ≤ 4*M))).map
    (fun p => (⟨(p.1-tau*p.2)/2,p.2⟩ : QuadInt tau nu))



end QuadInt
end D1Bound5
end


