-- Prove2me | Definitions.Def_CombOpt_TJoin_Graph_minPerfectMatchingWeight
-- name    : CombOpt_TJoin_Graph_minPerfectMatchingWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:33.927617+00:00
-- url     : https://prove2.me/theorems/bb7a991a-4802-4a95-93b4-39949eb703f7
-- title:
--   Minimum weight of a perfect matching
-- statement:
--   For weights $c\in\mathbb R^E$, the **minimum weight of a perfect matching** is $\min\{c(M):\ M \text{ a perfect matching of } G\}$.
--
--   **Formalization Note** Taken in the extended reals: the real minimum when $G$ has a perfect matching, $+\infty$ otherwise.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.3, Theorem 5.13, p. 148 (PDF p. 156)

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph
import Definitions.Def_CombOpt_TJoin_Graph_IsPerfectMatching

namespace CombOpt.TJoin

/-- **Minimum weight of a perfect matching.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.3, p. 148 (PDF p. 156), Theorem 5.13: "the minimum weight of a perfect matching".

The infimum in `EReal` of `c(M) = ∑_{e ∈ M} c e` over all perfect matchings `M` of `G`.

**Formalization Note.** A finite minimum when `G` has a perfect matching, `⊤` otherwise. -/
noncomputable def Graph.minPerfectMatchingWeight {V E : Type*} [Fintype E] [DecidableEq V]
    (G : Graph V E) (c : E → ℝ) : EReal :=
  ⨅ (M : Finset E) (_ : G.IsPerfectMatching M), ((∑ e ∈ M, c e : ℝ) : EReal)

end CombOpt.TJoin


