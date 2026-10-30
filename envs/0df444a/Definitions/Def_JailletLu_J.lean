-- Prove2me | Definitions.Def_JailletLu_J
-- name    : JailletLu_J
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:20:39.582988+00:00
-- url     : https://prove2.me/theorems/95907cbd-a3dc-4fc1-897a-841b4d29ecb2
-- title:
--   The interval $J_i(a_j)$ of an advertiser for type $i$
-- statement:
--   For type $i$ and an advertiser $a_j$ in the order $a_1,\dots,a_k$,
--   $$
--   J_i(a_j)=\Big[\sum_{l=1}^{j-1}f_{a_l,i},\ \sum_{l=1}^{j}f_{a_l,i}\Big],
--   $$
--   and $J_i(b)=\emptyset$ for an advertiser not interested in $i$. If the uniform point $x\in[0,r_i]$ falls in $J_i(a_j)$, then $a_j$ is the first advertiser of the list. For feasible $f$ the intervals tile $[0,r_i]$ and overlap only at endpoints.
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.3, p. 13

import Mathlib
import Definitions.Def_JailletLu_fA
import Definitions.Def_JailletLu_lo

namespace JailletLu

/-- **The interval of an advertiser for impression type `i`.**
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.3, p. 13: "[Σ_{l=1}^{j−1} f_{a_l,i}, Σ_{l=1}^{j} f_{a_l,i}]".

`J r f ord i b = [lo, lo + fA b i]` (closed) if `b` occurs in `ord i`, and `∅` otherwise (an
advertiser not interested in `i` carries no flow on `i`). For an admissible order and a feasible
flow these intervals tile `[0, r_i]` and overlap only at endpoints. -/
noncomputable def J {A I : Type*} [Fintype A] [DecidableEq A] (r : I → ℝ) (f : A → I → ℝ)
    (ord : I → List (Option A)) (i : I) (b : Option A) : Set ℝ :=
  if b ∈ ord i then Set.Icc (lo r f ord i b) (lo r f ord i b + fA r f b i) else ∅

end JailletLu


