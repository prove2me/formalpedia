-- Prove2me | Definitions.Def_CirclePackingConstants_EightQuad
-- name    : CirclePackingConstants_EightQuad
-- status  : Definition
-- author  : @vebis
-- created : 2026-10-06T10:03:26.430552+00:00
-- url     : https://prove2.me/theorems/a8de4941-ff5e-4271-9231-143c4130dee2
-- title:
--   The quadrilateral $C N_2 R_2 H_2$ of Schaer–Meir
-- statement:
--   In coordinates $(u,v)$ centred at the centre $C$ of the unit square, let $s=(2-\sqrt3)/2$. Schaer and Meir (1965) use the points $N_2=(0,s)$, $H_2=(-s,s)$ and $R_2=(-\tfrac s2,\tfrac14)$, where $R_2$ is the intersection of the segments $O_2N_2$ and $K_2H_2$. `eightQuad p` states that $p$ lies in the closed convex quadrilateral $C\,N_2\,R_2\,H_2$, i.e.
--
--   $$
--   u\le0,\qquad u+v\ge0,\qquad v+\sqrt3\,u\le s,\qquad v-\sqrt3\,u\le \tfrac12-s .
--   $$
--
--   The four inequalities are the half-planes bounded by the lines $CN_2$, $H_2C$, $N_2R_2$ and $R_2H_2$ respectively.
-- source:
--   J. Schaer and A. Meir, On a geometric extremum problem, Canad. Math. Bull. 8 (1965), 21-27, https://doi.org/10.4153/CMB-1965-004-x, Proposition 3, step (iii), Figure 3.

import Definitions.Def_CirclePackingConstants
import Definitions.Def_CirclePackingConstants_Eight

noncomputable section

namespace CirclePackingConstants

/-- The quadrilateral `C N₂ R₂ H₂` of Schaer–Meir, in coordinates centred at the centre of the unit
square: `C = (0,0)`, `N₂ = (0, s)`, `R₂ = (-s/2, 1/4)`, `H₂ = (-s, s)` with `s = eightS`.  It is cut out
by the four half-planes `u ≤ 0`, `u + v ≥ 0`, `v + √3 u ≤ s` and `v - √3 u ≤ 1/2 - s`. -/
def eightQuad (p : Point) : Prop :=
  p.1 ≤ 0 ∧ 0 ≤ p.1 + p.2 ∧ p.2 + Real.sqrt 3 * p.1 ≤ eightS ∧
    p.2 - Real.sqrt 3 * p.1 ≤ 1 / 2 - eightS

end CirclePackingConstants


