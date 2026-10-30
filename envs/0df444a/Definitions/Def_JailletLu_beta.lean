-- Prove2me | Definitions.Def_JailletLu_beta
-- name    : JailletLu_beta
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:24:01.244234+00:00
-- url     : https://prove2.me/theorems/f10f42ff-cf34-4518-9d5f-51b7bfcaa73e
-- title:
--   $\beta_a=\max_{a_1\in A^*_a}m_{a,a_1}$
-- statement:
--   For an advertiser $a$,
--   $$
--   \beta_a=\max_{a_1\in A^*_a}m_{a,a_1},
--   $$
--   the largest expected number of lists $\langle a,a_1\rangle$ with a second entry $a_1\ne a$. The maximum is over the nonempty finite set $A^*_a$.
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, p. 15

import Mathlib
import Definitions.Def_JailletLu_m
import Definitions.Def_JailletLu_Astar

namespace JailletLu

/-- **`β_a = max_{a1 ∈ A*_a} m_{a,a1}`.**
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, p. 15: "Let β_a = max_{a1∈A*_a} m_{a,a1} ≜ m_{a,a1*}".

The maximum is over the nonempty finite set `A*_a` (it contains the dummy `none`). -/
noncomputable def beta {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] (r : I → ℝ)
    (f : A → I → ℝ) (ord : I → List (Option A)) (a : A) : ℝ :=
  (Astar a).sup' ⟨none, Finset.mem_erase.mpr ⟨by simp, Finset.mem_univ _⟩⟩
    (fun b => m r f ord (some a) b)

end JailletLu


