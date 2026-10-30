-- Prove2me | Definitions.Def_JailletLu_fTot
-- name    : JailletLu_fTot
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:18:27.534094+00:00
-- url     : https://prove2.me/theorems/f8f427a8-2a71-4a82-b374-00fe639951ed
-- title:
--   Total flow $f_a$ of an advertiser
-- statement:
--   For an advertiser $a$, $f_a=\sum_{i\sim a}f_{a,i}$ is the total flow into $a$; for the algorithm it is the expected number of requests whose list starts with $a$.
--
--   **Formalization Note** The sum runs over all $i$; it equals the sum over $i\sim a$ because feasible flows vanish off the edges.
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §3.4, p. 9 (notation used in §5)

import Mathlib

namespace JailletLu

/-- **Total flow `f_a` of an advertiser.**
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §3.4, p. 9: "For notational simplicity, define f_a ≜ Σ_{i∼a} f_{a,i}" (used in §5).

`fTot f a = Σ_i f a i`; the sum over `i ∼ a` is the sum over all `i` for flows vanishing off the
edges (see `LP4Feasible`). -/
noncomputable def fTot {A I : Type*} [Fintype I] (f : A → I → ℝ) (a : A) : ℝ :=
  ∑ i, f a i

end JailletLu


