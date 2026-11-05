-- Prove2me | Definitions.Def_ReusableMatching_MatchedInPrevPeriod
-- name    : ReusableMatching_MatchedInPrevPeriod
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:32:49.701014+00:00
-- url     : https://prove2.me/theorems/b5b5e9b9-f10f-400f-935e-96b319c78780
-- title:
--   Resource $i$ is matched in period $k(j)-1$
-- statement:
--   In the run of Periodic Reranking with seed vector $Y$, resource $i$ is **matched in period $k(j)-1$** if some arrival of the period immediately before the period of $j$ is matched to $i$. Lemmas 6 and 7 split the values of the seed $y^1$ according to this property.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, Lemmas 6 and 7, pp.10–11

import Mathlib
import Definitions.Def_ReusableMatching_PeriodicReranking

namespace ReusableMatching

/-- **"`i` is matched to some arrival in period `k(j) − 1`"** (arXiv:2110.07084v2, Lemmas 6 and 7,
pp.10–11) in the run of Periodic Reranking with seed vector `Y`: some arrival `t` of the period
before the period of `j` is matched to `i`. -/
def MatchedInPrevPeriod {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
    (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (i : V) (j : Fin n) : Prop :=
  ∃ t : Fin n, period I t = prevPeriod I j ∧ PeriodicReranking I β Y t = some i

end ReusableMatching


