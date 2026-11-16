-- Prove2me | Definitions.Def_DecDynMatch_Supplement_UnitUtilities
-- name    : DecDynMatch_Supplement_UnitUtilities
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:23:30.860921+00:00
-- url     : https://prove2.me/theorems/d09419d9-f2f3-4dbc-93d0-d4eec004181d
-- title:
--   Utilities in $[0,1]$
-- statement:
--   For a dynamic matching instance $I$ with player utilities $\mu_{i,k}$ and arm utilities $\pi_{k,i}$, the predicate says
--   $$
--   \mu_{i,k}\in[0,1]\quad\text{and}\quad \pi_{k,i}\in[0,1]\qquad\text{for every player } i \text{ and arm } k .
--   $$
--   The base instance does not impose this range, which the paper fixes in §2.1; it matters for the lower bounds (where the class of instances in the convergence-speed requirement is the paper's) and for two-sided learning, where $\mu,\pi$ are means of $[0,1]$-valued observations.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), §2.1, p.4

import Mathlib
import Definitions.Def_DecDynMatch_Instance

namespace DecDynMatch.Supplement

variable {K : ℕ} {ι : Type*} [Fintype ι]

/-- **Utilities in `[0, 1]`.** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912
(held version, sha256 6a27277e…), §2.1, p.4: "For each player i, the utility of arm k is
μ_{i,k} ∈ [0, 1]; for each arm k, the utility of player i is π_{k,i} ∈ [0, 1]."

The base `Instance` does not impose this range; `UnitUtilities I` adds it. In the two-sided
learning setting (§5.1, p.12) these are the mean utilities. -/
def UnitUtilities (I : Instance K ι) : Prop :=
  ∀ i k, I.μ i k ∈ Set.Icc (0 : ℝ) 1 ∧ I.π k i ∈ Set.Icc (0 : ℝ) 1

end DecDynMatch.Supplement


