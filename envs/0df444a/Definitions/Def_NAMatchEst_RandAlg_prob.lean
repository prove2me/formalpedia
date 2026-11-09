-- Prove2me | Definitions.Def_NAMatchEst_RandAlg_prob
-- name    : NAMatchEst_RandAlg_prob
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:54:11.403404+00:00
-- url     : https://prove2.me/theorems/c10e4a00-3bd6-4d74-ad01-28bc157883d5
-- title:
--   Success probability of an algorithm on a graph
-- statement:
--   For an algorithm $A$, a graph $G$ and a property $P$ of outputs,
--
--   $$
--   \Pr[P(A(G))]=\sum_{\omega\in\Omega} w(\omega)\,\mathbf 1\{P(\text{output of $A$ on $G$ under $\omega$})\},
--   $$
--
--   the probability over the internal randomness that the output satisfies $P$.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 3, p.17 (PDF 21) and Lemma 3.1, p.19 (PDF 23)

import Mathlib
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_run

namespace NAMatchEst

/-- The probability that the output of `A` on the graph `G` satisfies the predicate `P`: the total
weight of the seeds `ω` with `P (A.run G ω)`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 3, p.17 (PDF 21) and Lemma 3.1, p.19 (PDF 23) ("with probability at least …").

**Formalization Note** The indicator uses classical decidability of `P`. -/
noncomputable def RandAlg.prob {n : ℕ} {β : Type} (A : RandAlg n β) (G : AdjList n)
    (P : β → Prop) : ℝ :=
  open Classical in ∑ ω, A.dist.prob ω * if P (A.run G ω) then 1 else 0

end NAMatchEst


