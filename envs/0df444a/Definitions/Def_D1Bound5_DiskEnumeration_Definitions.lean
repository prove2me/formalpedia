-- Prove2me | Definitions.Def_D1Bound5_DiskEnumeration_Definitions
-- name    : D1Bound5_DiskEnumeration_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:54:51.111029+00:00
-- url     : https://prove2.me/theorems/9d7db350-4a2e-4692-9d40-199f2a511599
-- title:
--   Disk Enumeration
-- statement:
--   Enumerate the closed norm disk using doubled-real and imaginary integer coordinates. The square-root rectangle is a finite superset; the exact norm and parity filters select the disk. It includes zero and anchors. The named objects in this bundle include `QuadInt.disk`.
-- source:
--   D1Bound5/DiskEnumeration.lean, lines 20-28, SHA-256 d1d1de7efa3c474d4e36936ae73c743f9c42044bc9487e406a2818230fd2ca53. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5.QuadInt

variable {tau nu : ℤ}



/-- Enumerate the closed norm disk using doubled-real and imaginary integer
coordinates. The square-root rectangle is a finite superset; the exact
norm and parity filters select the disk. It includes zero and anchors. -/
def disk (tau nu M : ℤ) : Finset (QuadInt tau nu) :=
  let r := Int.sqrt (4*M)
  (((Finset.Icc (-r) r).product (Finset.Icc (-r) r)).filter
    (fun p : ℤ × ℤ => p.1 % 2 = (tau*p.2) % 2 ∧
      p.1^2+discriminant tau nu*p.2^2 ≤ 4*M)).image
    (fun p => (⟨(p.1-tau*p.2)/2,p.2⟩ : QuadInt tau nu))







end D1Bound5.QuadInt
end


