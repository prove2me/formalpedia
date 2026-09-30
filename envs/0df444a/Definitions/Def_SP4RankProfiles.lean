-- Prove2me | Definitions.Def_SP4RankProfiles
-- name    : SP4RankProfiles
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-08T04:00:58.853323+00:00
-- url     : https://prove2.me/theorems/96c232b0-ddad-4ca2-b968-b8a7775c01fe
-- title:
--   Finite symmetric rank profiles and central cancellation levels
-- statement:
--   For a finitely supported function $r:\mathbb Z\to\mathbb N$, its mass is the sum of its values. Write $\delta_a$ for the function equal to one at $a$ and zero elsewhere. For arbitrary integers $g,h$ and natural numbers $o,c$, this interface defines
--
--   $$
--   T(g,o,c)=o\delta_{-g}+c\delta_0+o\delta_g,\qquad F(g,h)=2\delta_{-g}+2\delta_{-h}+\delta_0+2\delta_h+2\delta_g.
--   $$
--
--   When positions coincide, contributions are added. No positivity, ordering or adjacency of the parameters is built into these definitions. The bundle also defines the eight filtration levels $(g,g,0,0,0,0,-g,-g)$ used for the nonpermanent atoms of a central-rank-five profile. It does not define a knot, a genus or knot-Floer homology.
-- source:
--   Ryan Shin, corrected unpublished gt_e12_rank18_cube_attack.md, Section 2, equation (2.1) and Section 2.1; SHA-256 ac06bc38602b5eb920f798ed749c06e06f56430eb0151d213ca2650834ccb883. Only the indicated finite rank-profile and pairing arguments are formalized; no HFK construction or external genus-one classification theorem is supplied.

import Mathlib

set_option autoImplicit false

namespace SP4RankProfiles

/-- Total dimension of an arbitrary finite integer-indexed rank profile. -/
def mass (r : ℤ →₀ ℕ) : ℕ := r.sum fun _ n => n

/-- Three occupied symmetric levels, with independently specified outer and central ranks. -/
noncomputable def three (g : ℤ) (outer center : ℕ) : ℤ →₀ ℕ :=
  Finsupp.single (-g) outer + Finsupp.single 0 center + Finsupp.single g outer

/-- The five-level raw profile; no adjacency relation is built into the definition. -/
noncomputable def five (g h : ℤ) : ℤ →₀ ℕ :=
  Finsupp.single (-g) 2 + Finsupp.single (-h) 2 + Finsupp.single 0 1 +
    Finsupp.single h 2 + Finsupp.single g 2

/-- The nonpermanent atoms in the central-rank-five profile: the permanent
central atom is omitted, leaving two top, four central and two bottom atoms. -/
def centralFiveLevel (g : ℤ) : Fin 8 → ℤ := ![g, g, 0, 0, 0, 0, -g, -g]

end SP4RankProfiles


