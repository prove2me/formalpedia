-- Prove2me | Definitions.Def_NoHair_TwoCentre
-- name    : NoHair_TwoCentre
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-22T21:21:35.50805+00:00
-- url     : https://prove2.me/theorems/6945be00-0bba-4e13-9699-03402e9e08f0
-- title:
--   The equal-mass two-centre electrostatic potential and Faraday field
-- statement:
--   In isotropic coordinates $(t,x)$, put unit masses at $b_-=(-1,0,0)$ and $b_+=(1,0,0)$. On the complement of their worldlines, the equal-mass Majumdar–Papapetrou potential and Faraday field are
--
--   $$
--   U=1+|x-b_-|^{-1}+|x-b_+|^{-1},\qquad \Phi=U^{-1},\qquad F=d(\Phi\,dt).
--   $$
--
--   The coordinate exterior is specified by strict positivity of both squared spatial distances. The derivative in the definition of $F$ uses the coordinate basis and convention of the no-hair mission.
-- source:
--   J. B. Hartle and S. W. Hawking, Solutions of the Einstein-Maxwell equations with many black holes, Commun. Math. Phys. 26 (1972), 87–101, §II, equations (2.1)–(2.13), https://doi.org/10.1007/BF01645696.

import Definitions.Def_NoHair_coordinates

/-! The electrostatic potential of the equal-mass Majumdar–Papapetrou exterior, with
centres at spatial coordinates (−1,0,0) and (1,0,0). Hartle and Hawking (1972), §II,
equations (2.1)–(2.8). The Maxwell two-form in this chart is d(Φ dt). -/

open NoHair Set

namespace NoHair.TwoCentre

noncomputable section

def axis (a : ℝ) : E4 := WithLp.toLp 2 ![0, a, 0, 0]
def squaredDistance (c : ℝ) (y : E4) : ℝ := (y 1 - c) ^ 2 + y 2 ^ 2 + y 3 ^ 2
def inverseDistance (c : ℝ) (y : E4) : ℝ := 1 / Real.sqrt (squaredDistance c y)
def harmonicPotential (y : E4) : ℝ := 1 + inverseDistance (-1) y + inverseDistance 1 y
def electricPotential (y : E4) : ℝ := 1 / harmonicPotential y
def field (y : E4) : Matrix (Fin 4) (Fin 4) ℝ := fun i j =>
  (if j = 0 then coordPartial electricPotential i y else 0) -
  (if i = 0 then coordPartial electricPotential j y else 0)

/-- Isotropic exterior coordinates at all spatial points except the two point sources. -/
def exterior : Set E4 := {y | 0 < squaredDistance (-1) y ∧ 0 < squaredDistance 1 y}

end
end NoHair.TwoCentre


