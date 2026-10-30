-- Prove2me | Definitions.Def_JailletLu_m
-- name    : JailletLu_m
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:22:42.925411+00:00
-- url     : https://prove2.me/theorems/715ed685-0091-48cd-9c14-680369e6868a
-- title:
--   List numbers $m_{b,c}=\sum_i m^i_{b,c}$
-- statement:
--   For $b,c\in A^*$,
--   $$
--   m_{b,c}=\sum_{i\in I}m^i_{b,c}
--   $$
--   is the expected number of lists equal to $\langle b,c\rangle$, irrespective of the impression types they are associated with.
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.3, p. 13

import Mathlib
import Definitions.Def_JailletLu_mi

namespace JailletLu

/-- **The list numbers `m_{b,c}`.**
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.3, p. 13: "Then, m_{a_j,a_k} ≜ Σ_{i∈I} m^i_{a_j,a_k} is the expected number of lists that
are ⟨a_j, a_k⟩, irrespective of the impression types which they are associated with."

`m r f ord b c = Σ_{i ∈ I} mi r f ord i b c`, for `b, c ∈ A* = Option A` (`none` = `a_d`). -/
noncomputable def m {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] (r : I → ℝ)
    (f : A → I → ℝ) (ord : I → List (Option A)) (b c : Option A) : ℝ :=
  ∑ i, mi r f ord i b c

end JailletLu


