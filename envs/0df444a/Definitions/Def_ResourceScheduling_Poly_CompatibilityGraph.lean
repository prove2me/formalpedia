-- Prove2me | Definitions.Def_ResourceScheduling_Poly_CompatibilityGraph
-- name    : ResourceScheduling_Poly_CompatibilityGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:30:54.410422+00:00
-- url     : https://prove2.me/theorems/5ba4c37a-6ffd-470b-976b-582ebda8d250
-- title:
--   The graph G of pairs of jobs that can be executed simultaneously (proof of Theorem 1)
-- statement:
--   Given an instance with jobs $J_1,\dots,J_n$ and resources $R_1,\dots,R_l$ of sizes $s_h$ and requirements $r_{hj}$, the proof of Theorem 1 constructs "a graph $G$ with vertices $1,\dots,n$ and edges $\{j,k\}$ whenever $r_{hj}+r_{hk}\le s_h$ ($h=1,\dots,l$)": two distinct jobs $j\ne k$ are adjacent when
--   $$r_{hj}+r_{hk}\le s_h\qquad\text{for every } h=1,\dots,l.$$
--   "Thus, the vertices correspond to the jobs and the edges to pairs of jobs that can be executed simultaneously."
--
--   A maximum matching of $G$ determines the optimal makespan on two identical machines (Theorem 1).
--
--   **Formalization Note** The graph is a Mathlib `SimpleGraph` on `Fin n`, so it has no loops: adjacency requires $j\ne k$.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), pp. 13–15, proof of Theorem 1

import Mathlib
import Definitions.Def_ResourceScheduling_Poly_Model

/-!
# The graph `G` of the proof of Theorem 1

Błażewicz, Lenstra & Rinnooy Kan, Discrete Appl. Math. 5 (1983), pp. 13–15, proof of Theorem 1:
"construct a graph G with vertices 1, ..., n and edges {j, k} whenever r_hj + r_hk ≤ s_h
(h = 1, ..., l)."
-/

namespace ResourceScheduling.Poly

/-- The graph on the jobs with an edge `{j, k}` (`j ≠ k`) whenever `r_{hj} + r_{hk} ≤ s_h` for
every resource `R_h`: the pairs of jobs that can be executed simultaneously. -/
def Instance.compatGraph (I : Instance) : SimpleGraph (Fin I.n) where
  Adj j k := j ≠ k ∧ ∀ h, I.r h j + I.r h k ≤ I.s h
  symm := ⟨fun j k hjk => ⟨hjk.1.symm, fun h => by rw [Nat.add_comm]; exact hjk.2 h⟩⟩
  loopless := ⟨fun j hjj => hjj.1 rfl⟩

end ResourceScheduling.Poly


