-- Prove2me | Definitions.Def_JailletLu_sA
-- name    : JailletLu_sA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:25:01.513622+00:00
-- url     : https://prove2.me/theorems/45f2bee1-36a8-4953-803c-f5bf3c648c7f
-- title:
--   $s_a=\sum_{a_1\in A^*_a}m_{a,a_1}$
-- statement:
--   For an advertiser $a$,
--   $$
--   s_a=\sum_{a_1\in A^*_a}m_{a,a_1},
--   $$
--   the expected number of lists that start with $a$ and have a different second entry (possibly the dummy).
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, p. 15

import Mathlib
import Definitions.Def_JailletLu_m
import Definitions.Def_JailletLu_Astar

namespace JailletLu

/-- **`s_a = Σ_{a1 ∈ A*_a} m_{a,a1}`.**
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, p. 15: "s_a = Σ_{a1∈A*_a} m_{a,a1}".

The expected number of lists with `a` first and a different advertiser (possibly the dummy)
second. -/
noncomputable def sA {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] (r : I → ℝ)
    (f : A → I → ℝ) (ord : I → List (Option A)) (a : A) : ℝ :=
  ∑ b ∈ Astar a, m r f ord (some a) b

end JailletLu


