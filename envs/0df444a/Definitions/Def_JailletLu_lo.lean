-- Prove2me | Definitions.Def_JailletLu_lo
-- name    : JailletLu_lo
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:19:55.310758+00:00
-- url     : https://prove2.me/theorems/b00c79ba-1285-4e26-90f3-9342ebd07a5a
-- title:
--   Left endpoint $\sum_{l<j}f_{a_l,i}$ of an advertiser's interval
-- statement:
--   For the order $a_1,\dots,a_k$ of the advertisers interested in type $i$, the left endpoint of the interval of $a_j$ is
--   $$
--   \mathrm{lo}_i(a_j)=\sum_{l=1}^{j-1}f_{a_l,i},
--   $$
--   the sum of the extended flows of the advertisers listed before $a_j$.
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.3, p. 13

import Mathlib
import Definitions.Def_JailletLu_fA

namespace JailletLu

/-- **Left endpoint of an advertiser's interval in the list construction.**
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.3, p. 13: "If x ∈ [Σ_{l=1}^{j−1} f_{a_l,i}, Σ_{l=1}^{j} f_{a_l,i}], then a_j is the first
advertiser in the list to be considered".

For the order `ord i = [a_1, …, a_k]` of the advertisers interested in `i` (dummy included),
`lo r f ord i a_j = Σ_{l<j} f_{a_l,i}`, the sum of the extended flows `fA` of the entries before
`a_j` in `ord i`. -/
noncomputable def lo {A I : Type*} [Fintype A] [DecidableEq A] (r : I → ℝ) (f : A → I → ℝ)
    (ord : I → List (Option A)) (i : I) (b : Option A) : ℝ :=
  (((ord i).takeWhile (fun c => decide (c ≠ b))).map (fun c => fA r f c i)).sum

end JailletLu


