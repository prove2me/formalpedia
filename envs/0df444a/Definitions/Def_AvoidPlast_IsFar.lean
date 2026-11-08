-- Prove2me | Definitions.Def_AvoidPlast_IsFar
-- name    : AvoidPlast_IsFar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:38:34.247586+00:00
-- url     : https://prove2.me/theorems/65721e11-0cf1-4053-969b-f2a1bd22eb85
-- title:
--   Far from a set of strings
-- statement:
--   A string $y$ is $d$-far from a set $S$ if every string of $S$ of the same length is at relative distance more than $d$ from $y$. This holds vacuously if $S$ has no string of that length, as the soundness of a PCPP requires.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 4.1, p.17 ([BGH+05])

import Mathlib
import Definitions.Def_AvoidPlast_relHamming

namespace AvoidPlast

/-- `y` is `d`-far from a set `S` of strings (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §4.1, p.17, proximity parameter, reading of
[BGH+05]): every string of `S` of the same length is at relative distance greater than `d` from `y`.
This holds vacuously if `S` has no string of that length. -/
def IsFar (d : ℝ) (S : List Bool → Prop) (y : List Bool) : Prop :=
  ∀ y' : List Bool, y'.length = y.length → S y' → d < relHamming y y'

end AvoidPlast


