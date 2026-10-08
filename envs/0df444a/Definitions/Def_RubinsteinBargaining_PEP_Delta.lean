-- Prove2me | Definitions.Def_RubinsteinBargaining_PEP_Delta
-- name    : RubinsteinBargaining_PEP_Delta
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:12:48.260786+00:00
-- url     : https://prove2.me/theorems/b3db51a6-bb5e-4129-b4ca-4b865db3c30d
-- title:
--   Threshold correspondence Δ and its projections
-- statement:
--   A pair $(x,y)$ belongs to $\Delta$ when $y$ is the smallest partition at which player 1 weakly prefers immediate agreement at $y$ to agreement at $x$ one period later, and $x$ is the largest partition at which player 2 weakly prefers immediate agreement at $x$ to agreement at $y$ one period later. Both extrema range over the unit interval. Write $\Delta_1$ and $\Delta_2$ for the first- and second-coordinate projections.
--
--   This correspondence describes the one-period acceptance thresholds that the equilibrium characterization identifies with $A$ and $B$.
--
--   **Formalization Note** The extrema use `IsLeast` and `IsGreatest` on actual nonempty candidates, avoiding default values of real infima or suprema.
-- source:
--   Rubinstein, Perfect Equilibrium in a Bargaining Model, Econometrica 50 (1982), p. 104, Section 5, definition of Δ, https://doi.org/10.2307/1912531

import Definitions.Def_RubinsteinBargaining_PEP_Core

namespace RubinsteinBargaining.PEP

/-- The pairs satisfying both least/greatest one-period threshold conditions. -/
def Delta (p : Preferences) : Set (ℝ × ℝ) :=
  {q | ∃ (x y : Partition), q = (x.val, y.val) ∧
    IsLeast {y' : Partition |
      weak p .one (agreement y' 0) (agreement x 1)} y ∧
    IsGreatest {x' : Partition |
      weak p .two (agreement x' 0) (agreement y 1)} x}

def Delta1 (p : Preferences) : Set ℝ :=
  {x | ∃ y, (x, y) ∈ Delta p}

def Delta2 (p : Preferences) : Set ℝ :=
  {y | ∃ x, (x, y) ∈ Delta p}

end RubinsteinBargaining.PEP


