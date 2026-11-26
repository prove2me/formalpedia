-- Prove2me | Definitions.Def_MasulloRH_HeightTwoComputedGrid
-- name    : MasulloRH_HeightTwoComputedGrid
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-26T10:22:41.063798+00:00
-- url     : https://prove2.me/theorems/b3a30ca4-39cc-42b4-af9e-c419ffe83506
-- title:
--   Computable rational disks and energy summands for the height-two theta grid
-- statement:
--   A deterministic rational table for the scale-two witness. The compact interval \([-4,4]\) is divided into 65,536 cells of width \(1/8192\). Pulse disks use rational bounds on \(3/\sqrt\pi\) and the extrema of \(|x|\). The weight uses an upper argument bound. Theta disks use the generated exponential rows, direct or reflected coordinates, a finite Gaussian polynomial with an explicit tail, and outward rounding. The truncation order is selected from \(2,3,5,6\) using the upper Gaussian parameter. Reflection multiplies by an interval for \(e^{-x}/2\). The outer translated cells use the proved disk centered at zero of radius \(2^{-64}\). The last function computes the rational signed-center and radius energy contribution of one compact cell.
-- source:
--   The height-two mission table and the eleven-term witness are https://prove2.me/theorems/44743777-9b41-5194-84da-ff2782e96168 and https://prove2.me/definitions/d1967a7a-bf7f-42bd-8ad5-820a7680a39d .

import Definitions.Def_MasulloRH_DyadicExpRows
import Definitions.Def_MasulloRH_HeightTwoWitness

open scoped BigOperators
open MasulloRH.HeightTwoScalar MasulloRH.DyadicExp

namespace MasulloRH.ComputedGrid

def edge (k : ℤ) : ℚ := -4 + k/8192

def shifts : Fin 11 → ℤ := ![-3072,-2048,1024,3072,6144,8192,11264,14336,16384,18432,19456]

structure Disk where
  center : ℚ
  radius : ℚ

def enclose (l u : ℚ) : Disk := ⟨(l+u)/2,(u-l)/2⟩

def amin (l u : ℚ) := max 0 (max l (-u))
def amax (l u : ℚ) := max (-l) u

def pulseDisk (l u : ℚ) : Disk :=
  enclose ((1692568/1000000)*(row (-9*(amax l u)^2)).lower)
    ((1692569/1000000)*(row (-9*(amin l u)^2)).upper)

def weightUpper (l u : ℚ) : ℚ := (row (3*u/2 + 11*amax l u/24)).upper

def innerLo (l u : ℚ) (reflected : Bool) : ExpRow :=
  row (if reflected then -2*u else 2*l)
def innerHi (l u : ℚ) (reflected : Bool) : ExpRow :=
  row (if reflected then -2*l else 2*u)
def divisor (reflected : Bool) : ℚ := if reflected then 16 else 1
def gaussianLo (l u : ℚ) (reflected : Bool) : ExpRow :=
  row (-piUpperQ*(innerHi l u reflected).upper / divisor reflected)
def gaussianHi (l u : ℚ) (reflected : Bool) : ExpRow :=
  row (-piLowerQ*(innerLo l u reflected).lower / divisor reflected)

def order (u : ℚ) : ℕ :=
  if u ≤ 1/16 then 2 else if u ≤ 1/4 then 3 else if u ≤ 1/2 then 5 else 6

def polynomial (K : ℕ) (a b : ℚ) : ℚ :=
  2 * ∑ n ∈ Finset.range K,
    (a^((n+1)^2) - 3*b^(4*(n+1)^2) + 2*a^(16*(n+1)^2))
def tail (K : ℕ) (u : ℚ) : ℚ := 12*u^((K+1)^2)/(1-u^(2*K+3))

def normalized (a b : ℚ) : Disk :=
  let K := order b
  enclose (down (polynomial K a b - tail K b))
    (up (polynomial K b a + tail K b))

def rescale (l u : ℚ) (v : Disk) : Disk :=
  ⟨(l+u)/2*v.center, u*v.radius + (u-l)/2*|v.center|⟩

def thetaDisk (l u : ℚ) (reflected : Bool) : Disk :=
  let v := normalized (gaussianLo l u reflected).lower (gaussianHi l u reflected).upper
  if reflected then rescale ((row (-u)).lower/2) ((row (-l)).upper/2) v else v

def central (k : ℤ) := thetaDisk (edge k) (edge (k+1)) (decide (k < 24576))
def fullTheta (k : ℤ) : Disk :=
  if k < 8192 ∨ 45056 ≤ k then ⟨0,1/(2:ℚ)^64⟩ else central k

def pulseAt (j : ℕ) := pulseDisk (edge j) (edge ((j:ℤ)+1))
def weightAt (j : ℕ) := weightUpper (edge j) (edge ((j:ℤ)+1))

def energyTerm (j : ℕ) : ℚ :=
  let p := pulseAt j
  let v (i : Fin 11) := fullTheta ((j:ℤ)-shifts i)
  let A := |p.center - ∑ i, HeightTwoWitness.coeffsQ i * (v i).center| +
    (p.radius + ∑ i, |HeightTwoWitness.coeffsQ i| * (v i).radius)
  (1/8192) * (weightAt j * A^2)

end MasulloRH.ComputedGrid


