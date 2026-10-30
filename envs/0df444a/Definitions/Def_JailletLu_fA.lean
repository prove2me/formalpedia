-- Prove2me | Definitions.Def_JailletLu_fA
-- name    : JailletLu_fA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:18:12.745138+00:00
-- url     : https://prove2.me/theorems/1ec632b6-5dac-4deb-aab5-f221203cda91
-- title:
--   Flows extended by the dummy advertiser $a_d$
-- statement:
--   The algorithm of §5.3 adds a **dummy advertiser** $a_d$ adjacent to every impression type, carrying the flow left over by $f$:
--   $$
--   f_{a_d,i}=r_i-\sum_{a\in A}f_{a,i}.
--   $$
--   The advertisers together with the dummy form $A^*=A\cup\{a_d\}$; $f_{b,i}$ for $b\in A^*$ is the extended flow. With it, the flows on each type $i$ add up to $r_i$, so the intervals of the list construction tile $[0,r_i]$.
--
--   **Formalization Note** $A^*$ is `Option A`, with `none` the dummy.
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.3, p. 13

import Mathlib

namespace JailletLu

/-- **Flows extended by the dummy advertiser `a_d`.**
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.3, p. 13: "let us again first add a dummy advertiser a_d with f_{a_d} ≜ 1, and dummy
edges (a_d, i) for all i with f_{a_d,i} ≜ r_i − Σ_{a∈A} f_{a,i}."

The advertisers together with the dummy are `Option A`, with `none` the dummy `a_d`.
`fA r f (some a) i = f a i` and `fA r f none i = r_i − Σ_{a∈A} f_{a,i}`. -/
noncomputable def fA {A I : Type*} [Fintype A] (r : I → ℝ) (f : A → I → ℝ) :
    Option A → I → ℝ
  | none, i => r i - ∑ a, f a i
  | some a, i => f a i

end JailletLu


