-- Prove2me | Definitions.Def_MasulloRH_HeightTwoCurvature
-- name    : MasulloRH_HeightTwoCurvature
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-26T12:34:08.038377+00:00
-- url     : https://prove2.me/theorems/0bd03739-6175-4199-a56d-0cd93dae1953
-- title:
--   Six-term signed height-two surrogates, geometric tails and 256 group caps
-- statement:
--   This records the $1/128$ grid, direct and reflected six-term real Gaussian approximations, explicit geometric tails and 256 integer budgets. Each integer is an upper bound candidate in millionths for the weighted squared residual on four consecutive cells. The table itself makes no analytic assertion.
-- source:
--   Finite-height certificate for https://prove2.me/theorems/cc487734-5ed4-5457-b10a-df505d0aef9e with the rational witness https://prove2.me/definitions/d1967a7a-bf7f-42bd-8ad5-820a7680a39d .

import Definitions.Def_MasulloRH_HeightTwoWitness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MasulloRH.HeightTwoCurvature

/-- Upper bounds in millionths for the weighted squared residual on groups of four cells. -/
def capList : List ℕ :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 14, 27,
    50, 89, 148, 232, 343, 476, 622, 760, 864, 910, 913, 872,
    739, 532, 294, 92, 86, 371, 828, 1376, 1889, 2229, 2323, 2308,
    2057, 1532, 885, 313, 146, 711, 1590, 2570, 3387, 3811, 3868, 3744,
    3141, 2200, 1182, 376, 240, 965, 1987, 3035, 3838, 4181, 4218, 4010,
    3366, 2328, 1241, 390, 341, 1229, 2479, 3789, 4823, 5280, 5325, 5044,
    4174, 2743, 1293, 273, 914, 2403, 4134, 5581, 6577, 6772, 6611, 5581,
    3899, 2078, 659, 496, 1656, 3090, 4352, 5081, 5305, 5220, 4553, 3420,
    2127, 987, 239, 416, 1137, 1983, 2724, 3158, 3302, 3246, 2804, 2030,
    1134, 381, 302, 1126, 2342, 3611, 4626, 5122, 5203, 4997, 4177, 2946,
    1655, 602, 162, 747, 1521, 2174, 2471, 2504, 2329, 1748, 977, 305,
    296, 1083, 2185, 3310, 4150, 4514, 4539, 4258, 3454, 2358, 1263, 436,
    93, 471, 958, 1354, 1525, 1541, 1432, 1106, 683, 300, 59, 124,
    335, 563, 740, 828, 847, 831, 743, 608, 459, 322, 209, 127,
    72, 38, 19, 9, 4, 2, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1]

/-- Each cell has width 1/128. The cap is constant on four successive cells. -/
def cap (j : ℕ) : ℕ := capList.getD (j / 4) 0

def edgeQ (j : ℕ) : ℚ := -4 + (j : ℚ) / 128

noncomputable def edge (j : ℕ) : ℝ := -4 + (j : ℝ) / 128

/-- The branch is fixed for the entire cell, including its two endpoints. -/
def reflected (j : ℕ) (i : Fin 11) : Bool :=
  decide (edgeQ j - HeightTwoWitness.shiftsQ i < -1)

noncomputable def arg (b : Bool) (z : ℝ) := if b then -z - Real.log 4 else z

noncomputable def factor (b : Bool) (z : ℝ) : ℝ := if b then Real.exp (-z) / 2 else 1

/-- Six Gaussian terms evaluated on a fixed branch of the reflection identity. -/
noncomputable def thetaSix (b : Bool) (z : ℝ) : ℝ :=
  factor b z * (2 * ∑ k ∈ Finset.range 6,
    let t := ((k : ℝ) + 1) * Real.exp (arg b z)
    Real.exp (-Real.pi*t^2) - 3*Real.exp (-Real.pi*(2*t)^2) + 2*Real.exp (-Real.pi*(4*t)^2))

/-- The analytic geometric-tail estimate for this branch. -/
noncomputable def thetaTail (b : Bool) (z : ℝ) : ℝ :=
  let u := -Real.pi * (Real.exp (arg b z)) ^ 2
  factor b z * (12 * Real.exp (u*49) / (1 - Real.exp (u*15)))

/-- The signed real surrogate on one cell for the specified eleven-term witness. -/
noncomputable def surrogate (j : ℕ) (x : ℝ) : ℝ :=
  3 / Real.sqrt Real.pi * Real.exp (-9*x^2) -
    ∑ i : Fin 11, (HeightTwoWitness.coeffsQ i : ℝ) *
      thetaSix (reflected j i) (x - HeightTwoWitness.shifts i)

noncomputable def tail (j : ℕ) (x : ℝ) : ℝ :=
  ∑ i : Fin 11, |(HeightTwoWitness.coeffsQ i : ℝ)| *
    thetaTail (reflected j i) (x - HeightTwoWitness.shifts i)

end MasulloRH.HeightTwoCurvature


