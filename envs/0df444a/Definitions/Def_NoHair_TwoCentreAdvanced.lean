-- Prove2me | Definitions.Def_NoHair_TwoCentreAdvanced
-- name    : NoHair_TwoCentreAdvanced
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-22T21:26:50.423499+00:00
-- url     : https://prove2.me/theorems/106c8f81-517f-4212-8e08-31e7cf377ce9
-- title:
--   Advanced coordinates at one pole of the two-centre electrovacuum
-- statement:
--   In the advanced chart at the left unit-mass pole of the two-centre Majumdar–Papapetrou exterior, let $r$ be signed radial distance and $c$ the first component of the unit angular direction. The distance to the other pole and the two regularizing factors are
--
--   $$d=\sqrt{4+r^2-4rc},\qquad H=1+r(1+1/d),\qquad H_0=1+3r/2.$$
--
--   The six functions give the three coefficients of the $(v,r)$ metric block, the factor multiplying the unit sphere metric, and the two components of a regular electromagnetic potential. No denominator in these expressions contains $r$.
-- source:
--   J. B. Hartle and S. W. Hawking, Solutions of the Einstein-Maxwell equations with many black holes, Commun. Math. Phys. 26 (1972), 87–101, §II, equations (2.1)–(2.13), https://doi.org/10.1007/BF01645696.

import Mathlib

/-! Advanced coordinates for the unit-mass two-centre Majumdar–Papapetrou metric
near its left pole. The argument is the signed radius and the first component of
the unit angular direction. The metric multiplies the unit sphere metric by H². -/

namespace NoHair.TwoCentre.Advanced

noncomputable section

def distanceToOther (p : ℝ × ℝ) : ℝ :=
  Real.sqrt (4 + p.1 ^ 2 - 4 * p.1 * p.2)

def H (p : ℝ × ℝ) : ℝ := 1 + p.1 * (1 + 1 / distanceToOther p)

def H₀ (p : ℝ × ℝ) : ℝ := 1 + (3 / 2 : ℝ) * p.1

/-- The analytic quotient of H − H₀ by r². -/
def gapCoeff (p : ℝ × ℝ) : ℝ :=
  (4 * p.2 - p.1) / (2 * distanceToOther p * (2 + distanceToOther p))

def gvv (p : ℝ × ℝ) : ℝ := -p.1 ^ 2 / H p ^ 2
def gvr (p : ℝ × ℝ) : ℝ := H₀ p ^ 2 / H p ^ 2
def grr (p : ℝ × ℝ) : ℝ :=
  gapCoeff p * (H p + H₀ p) * (H p ^ 2 + H₀ p ^ 2) / H p ^ 2
def angularScale (p : ℝ × ℝ) : ℝ := H p ^ 2

def potentialV (p : ℝ × ℝ) : ℝ := p.1 / H p
def potentialR (p : ℝ × ℝ) : ℝ := H₀ p * p.1 * gapCoeff p / H p

end
end NoHair.TwoCentre.Advanced


