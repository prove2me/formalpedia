-- Prove2me | Definitions.Def_NoHair_TwoCentreSpacetime
-- name    : NoHair_TwoCentreSpacetime
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-22T21:35:20.508894+00:00
-- url     : https://prove2.me/theorems/f4e20dfe-a372-4ce6-8ec9-983c3e9dafca
-- title:
--   A global Cartesian chart for the one-horizon two-centre spacetime
-- statement:
--   Global Cartesian coordinates $(v,X)$ for the spacetime with only its left horizon included. Write $a=x+e_1$, $r=|a|$, and take $X=(1+1/r)a$ and $v=t+9r/4+3\log r-1/r$ on the original exterior. The coordinate spacetime is the open set $|X|>3/4$, $X\ne3e_1$. Its candidate exterior is $|X|>1$ within this set and its horizon shell is $|X|=1$.
-- source:
--   J. B. Hartle and S. W. Hawking, Solutions of the Einstein-Maxwell equations with many black holes, Commun. Math. Phys. 26 (1972), 87–101, §II, equations (2.1)–(2.13), https://doi.org/10.1007/BF01645696. The shifted Cartesian radial coordinate and the chosen open submanifold are specified here.

import Definitions.Def_NoHair_TwoCentre

/-! A single open Cartesian chart for the extension through only the left
Majumdar–Papapetrou horizon. In this chart the horizon is the unit sphere in
each time slice. The other throat is omitted from the manifold. -/

open NoHair Set

namespace NoHair.TwoCentre.Cartesian

noncomputable section

abbrev E3 := EuclideanSpace ℝ (Fin 3)

def spatial (y : E4) : E3 := WithLp.toLp 2 (fun i : Fin 3 => y i.succ)
def coordinates (t : ℝ) (x : E3) : E4 := WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))
def unitAxis : E3 := EuclideanSpace.single 0 1

/-- Advanced time shift, with derivative (1 + 3r/2)²/r² on positive radii. -/
def timeShift (r : ℝ) := 9 * r / 4 + 3 * Real.log r - 1 / r
def expandRadius (a : E3) : E3 := (1 + ‖a‖⁻¹) • a
def contractRadius (a : E3) : E3 := (1 - ‖a‖⁻¹) • a

def toAdvanced (y : E4) : E4 :=
  let a := spatial y + unitAxis
  coordinates (y 0 + timeShift ‖a‖) (expandRadius a)

def toIsotropic (z : E4) : E4 :=
  coordinates (z 0 - timeShift (‖spatial z‖ - 1)) (contractRadius (spatial z) - unitAxis)

def spacetime : Set E4 := {z | 3 / 4 < ‖spatial z‖ ∧ spatial z ≠ (3 : ℝ) • unitAxis}
def outerRegion : Set E4 := {z | 1 < ‖spatial z‖ ∧ spatial z ≠ (3 : ℝ) • unitAxis}
def horizon : Set E4 := {z | ‖spatial z‖ = 1}

end
end NoHair.TwoCentre.Cartesian


