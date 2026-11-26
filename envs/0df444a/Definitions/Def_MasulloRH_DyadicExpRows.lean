-- Prove2me | Definitions.Def_MasulloRH_DyadicExpRows
-- name    : MasulloRH_DyadicExpRows
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-26T10:10:06.47283+00:00
-- url     : https://prove2.me/theorems/527253ae-c082-4362-9b93-f21fb390a83c
-- title:
--   A computable dyadic generator for rational exponential certificate rows
-- statement:
--   Given any rational \(t\), compute a row for the existing public exponential certificate format. Zero has the exact output \([1,1]\). For \(t\le-64\) the output is \([0,2^{-64}]\). Otherwise put \(p=\max(1,\lceil4|t|\rceil)\) and \(x=|t|/p\). Round the published order-nine Taylor lower and upper estimates outward to multiples of \(2^{-32}\). At positive arguments take the interval of their \(p\)-th powers. At negative arguments use inverses in reverse order. Round the final endpoints outward again.
-- source:
--   Developed for the central height-two certificate https://prove2.me/theorems/44743777-9b41-5194-84da-ff2782e96168 using the public row definitions https://prove2.me/definitions/55b584ef-23cf-4152-bb89-68f7cb944cd5 .

import Definitions.Def_MasulloRH_ThetaCertificate
import Mathlib.Data.Rat.Floor

open MasulloRH.HeightTwoScalar

namespace MasulloRH.DyadicExp

/-- The output unit for finite rational arithmetic on the height-two grid. -/
def scale : ℚ := 4294967296

def down (x : ℚ) : ℚ := (⌊x*scale⌋ : ℤ) / scale

def up (x : ℚ) : ℚ := (⌈x*scale⌉ : ℤ) / scale

/-- Generate a row in the existing public exponential certificate format. -/
def row (t : ℚ) : ExpRow :=
  if t = 0 then ⟨0,t,1,1,0,0,0,0,0,0⟩
  else if t ≤ -64 then ⟨3,t,0,1/(2:ℚ)^64,0,0,0,0,0,64⟩
  else
    let p := max 1 ⌈4*|t|⌉₊
    let x := |t| / (p:ℚ)
    let a := max (1/2) (down (taylorRat x 9 - remainderRat x 9))
    let b := up (taylorRat x 9 + remainderRat x 9)
    if 0 < t then ⟨1,t,down (a^p),up (b^p),x,a,b,p,9,0⟩
    else ⟨2,t,down (1/b^p),up (1/a^p),x,a,b,p,9,0⟩

end MasulloRH.DyadicExp


