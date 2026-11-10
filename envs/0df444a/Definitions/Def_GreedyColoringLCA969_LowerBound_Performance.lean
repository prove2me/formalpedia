-- Prove2me | Definitions.Def_GreedyColoringLCA969_LowerBound_Performance
-- name    : GreedyColoringLCA969_LowerBound_Performance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T09:47:07.056509+00:00
-- url     : https://prove2.me/theorems/7a99ac6a-f727-411f-bcb9-20929e0ee2ee
-- title:
--   Global success and the expected-query efficient vertex fraction
-- statement:
--   For a rule $A$, represented graph $R$ and vertex $v$, let $q_r(A,R,v)$ be the extended cost of the actual run. Its expected query count is the nonnegative Lebesgue integral
--
--   $$q(A,R,v)=\int q_r(A,R,v)\,d\mathbb P(r)\in[0,+\infty].$$
--
--   The rule is $(q,\varepsilon)$-efficient on $R$ when $|\{v:q(A,R,v)\le q\}|\ge\varepsilon n$. For a deterministic seed fixing, the same condition uses its actual fixed-tape cost instead of averaging. Global success probability is the tape probability that all outputs constitute one greedy coloring. Uniform efficiency at degree bound $\Delta$ ranges over every size, every graph of maximum degree at most $\Delta$, and every ordering of every adjacency list.
--
--   At a negative real budget, no vertex is counted as efficient: the comparison includes a nonnegative-budget guard so conversion to nonnegative extended reals cannot replace a negative budget by zero. All budgets in the target results are positive. These definitions permit infinite expected costs and let the efficient subset depend on the input. They never average success separately for different vertices. **Formalization Note** Nonnegative extended integrals preserve infinite values. Cost and success measurability are established in the separate verification module, without adding regularity hypotheses to an algorithm.
--
--   Differences from the source:
--   - encoding: expectations of the number of graph queries and global success probabilities → nonnegative extended query costs integrated against the independent fair-bit product law; reason: finite costs agree exactly; divergent expectations remain infinite, and all cost and success events are measurable
-- source:
--   Zi Song Yeoh, Krzysztof Onak, Dragos-Florian Ristache, STOC 2027 submission #969 (October 2026), Definitions 2.6–2.7 and 2.9, pp.8–10 (PDF 9–11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/969.pdf

import Definitions.Def_GreedyColoringLCA969_LowerBound_Execution
import Definitions.Def_GreedyColoringLCA969_LowerBound_RandomTape

open scoped ENNReal
open MeasureTheory
open Classical

namespace GreedyColoringLCA969.LowerBound

/-- Definition 2.7: nonnegative extended expectation; infinite costs remain infinite. -/
noncomputable def expectedQueries {m : OracleMode} {n : ℕ} (A : Algorithm m)
    (R : Representation n) (v : Fin n) : ℝ≥0∞ :=
  ∫⁻ r, queryCost A R r v ∂tapeLaw

/-- Definition 2.9; the efficient subset can depend on the represented graph.
The sign guard keeps a negative real budget from being rounded up to zero by `ofReal`. -/
noncomputable def Efficient {m : OracleMode} {n : ℕ} (A : Algorithm m)
    (R : Representation n) (q ε : ℝ) : Prop :=
  ε * (n : ℝ) ≤ ((Finset.univ.filter
    (fun v => 0 ≤ q ∧ expectedQueries A R v ≤ ENNReal.ofReal q)).card : ℝ)

noncomputable def DeterministicEfficient {m : OracleMode} {n : ℕ}
    (B : DeterministicLCA m) (R : Representation n) (q ε : ℝ) : Prop :=
  ε * (n : ℝ) ≤ ((Finset.univ.filter
    (fun v => 0 ≤ q ∧ queryCost B.1 R B.2 v ≤ ENNReal.ofReal q)).card : ℝ)

noncomputable def successProbability {m : OracleMode} {n : ℕ} (A : Algorithm m)
    (R : Representation n) : ℝ≥0∞ := tapeLaw (successEvent A R)

/-- Uniform over every size, graph, and ordering of neighbor lists. -/
def UniformlyEfficient {m : OracleMode} (A : Algorithm m) (Δ : ℕ) (q ε : ℝ) : Prop :=
  ∀ (n : ℕ) (R : Representation n),
    MaxDegreeAtMost R.graph (Δ : ℝ) → Efficient A R q ε

end GreedyColoringLCA969.LowerBound


