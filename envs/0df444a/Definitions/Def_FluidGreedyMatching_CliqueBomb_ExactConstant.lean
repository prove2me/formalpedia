-- Prove2me | Definitions.Def_FluidGreedyMatching_CliqueBomb_ExactConstant
-- name    : FluidGreedyMatching_CliqueBomb_ExactConstant
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:56:25.543193+00:00
-- url     : https://prove2.me/theorems/5ead23eb-dd68-4ff1-b8dc-3df8fec69cf9
-- title:
--   The exact integral constant for the clique Double-Bomb
-- statement:
--   For $r\ge1$, set $\gamma(r)=r^2+3r+3$, $\theta(r)=\arctan((2r+3)/\sqrt3)$,
--   $$H(r)=r^{-2}\sqrt{\gamma(r)/7}\exp((\theta(r)-\theta(1))/\sqrt3),\qquad q_*=(\sqrt7)^{-1}\exp((\pi/2-\theta(1))/\sqrt3).$$
--   Define
--   $$\rho=\frac13\left(\int_1^\infty H(r)\frac{2(r+2)^2}{r\gamma(r)}\,dr+q_*^2\right).$$
--   This is Eq. (5.4) at $\sigma=1$, normalized by $2+\sigma=3$. It defines the constant independently of the stochastic limit and without assigning it a rounded decimal. The integral is a real Lebesgue integral on $[1,\infty)$; the goal separately asserts its integrability, so a nonintegrable default value cannot establish the target.
-- source:
--   Sayan Mukherjee, Fluid Limits and Upper Bounds for Randomized Greedy Matching, STOC 2027 submission #492 (October 2026), Eq. (5.4) and Section 5.4, p. 25

import Mathlib

set_option autoImplicit false

namespace FluidGreedyMatching.CliqueBomb

noncomputable section

/-- Eq. (5.4), p. 25, at sigma=1. The integral is not defined as a matching limit. -/
def gamma (r : ℝ) : ℝ := r^2 + 3 * r + 3

def theta (r : ℝ) : ℝ := Real.arctan ((2 * r + 3) / Real.sqrt 3)

def hubAsRatio (r : ℝ) : ℝ :=
  r⁻¹ ^ 2 * Real.sqrt (gamma r / 7) * Real.exp ((theta r - theta 1) / Real.sqrt 3)

def terminalSatellite : ℝ :=
  (Real.sqrt 7)⁻¹ * Real.exp ((Real.pi / 2 - theta 1) / Real.sqrt 3)

def exactIntegrand (r : ℝ) : ℝ := hubAsRatio r * (2 * (r + 2)^2 / (r * gamma r))

/-- The theorem explicitly asserts integrability on [1,infinity), preventing the
Bochner default value on a nonintegrable function from certifying the constant. -/
def rho : ℝ := ((∫ r in Set.Ici (1 : ℝ), exactIntegrand r) + terminalSatellite^2) / 3

end
end FluidGreedyMatching.CliqueBomb


