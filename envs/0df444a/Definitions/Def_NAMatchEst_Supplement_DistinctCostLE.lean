-- Prove2me | Definitions.Def_NAMatchEst_Supplement_DistinctCostLE
-- name    : NAMatchEst_Supplement_DistinctCostLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:35:52.366662+00:00
-- url     : https://prove2.me/theorems/5da2475f-48ed-49e1-86ed-b41532cf5f16
-- title:
--   Worst-case number of distinct queries of a non-adaptive algorithm
-- statement:
--   For a randomized non-adaptive algorithm $A$ in the adjacency-list model and a real number $q$, $A$ **makes at most $q$ distinct queries in the worst case** if, for every outcome $\omega$ of its internal randomness that has positive probability, the number of distinct queries among those $A$ issues under $\omega$ is at most $q$.
--
--   This is the cost measure of the paper's lower bounds (Theorems 4, 9, 13 and 14): identical oracle queries may be answered once, and the worst case ranges over the outcomes the algorithm can actually produce. A lower bound "$c\,f\le q$ for every such $q$" is at least as strong as the same bound for the cost measure of the base mission (`RandAlg.CostLE`: every seed, every repetition charged).
--
--   **Formalization Note** The count is `(A.queries ω).toFinset.card`; seeds of weight zero are ignored.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §2.1, p.13 (PDF 17) and §3.2, p.20 (PDF 24); used in Theorems 4, 9, 13, 14

import Mathlib
import Definitions.Def_NAMatchEst_RandAlg

namespace NAMatchEst.Supplement

/-- The algorithm `A` makes **at most `q` distinct queries in the worst case**: under every seed
of positive probability, the number of distinct queries in its query list is at most `q`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §2.1, p.13 (PDF 17)
(the query model) and §3.2, p.20 (PDF 24) ("identical oracle queries may be answered once"). Used
as the cost measure of the lower bounds, Theorems 4, 9, 13 and 14 (pp.32, 91, 154, 198; PDF 36, 95,
158, 202).

**Formalization Note**
1. Repeated queries are counted once (`List.toFinset`), the paper's measure in its lower bounds.
2. Only seeds of positive weight count: the worst case is over the outcomes the algorithm can
   actually produce. A lower bound `c·f ≤ q` for every such `q` is therefore at least as strong
   as one for the published `RandAlg.CostLE` (every seed, repetitions charged). -/
def DistinctCostLE {n : ℕ} {β : Type} (A : RandAlg n β) (q : ℝ) : Prop :=
  ∀ ω, 0 < A.dist.prob ω → (((A.queries ω).toFinset.card : ℕ) : ℝ) ≤ q

end NAMatchEst.Supplement


