-- Prove2me | Definitions.Def_ReusableMatching_matchedPairs
-- name    : ReusableMatching_matchedPairs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:32:13.858601+00:00
-- url     : https://prove2.me/theorems/4af856a8-3c90-45c4-86aa-05e828bf54c5
-- title:
--   The matching $\mathrm{PR}(Y)$ output by Periodic Reranking
-- statement:
--   For a seed vector $Y$, $\mathrm{PR}(Y)$ is the set of pairs $(i,t)$ such that Periodic Reranking matches arrival $t$ to resource $i$. The main theorem asserts that this set is always a feasible reusable matching.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, proof of Lemma 2, p.8

import Mathlib
import Definitions.Def_ReusableMatching_PeriodicReranking

namespace ReusableMatching

/-- **The matching `PR(Y)` output by Periodic Reranking** (arXiv:2110.07084v2, proof of Lemma 2,
p.8: "Let `PR(Y)` denote the matching output by PR given seed vector `Y`"): the set of pairs
`(i, t)` such that PR matches arrival `t` to resource `i`. -/
noncomputable def matchedPairs {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
    (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) : Finset (V × Fin n) := by
  classical
  exact Finset.univ.filter (fun p : V × Fin n => PeriodicReranking I β Y p.2 = some p.1)

end ReusableMatching


