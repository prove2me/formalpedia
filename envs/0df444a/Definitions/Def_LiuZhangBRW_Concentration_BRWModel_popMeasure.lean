-- Prove2me | Definitions.Def_LiuZhangBRW_Concentration_BRWModel_popMeasure
-- name    : LiuZhangBRW_Concentration_BRWModel_popMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:18.174833+00:00
-- url     : https://prove2.me/theorems/68799f2a-1566-4708-a974-5187ba95086a
-- title:
--   Population measure $P^{(M)}$ of a branching random walk, (6.5)
-- statement:
--   Let $P$ be the random-walk path law of a BRW and $M\ge0$ a horizon. The **population weight** of a lineage is $\prod_{j=1}^M a_j(u_{j-1})$, the normalizer is
--   $$
--   Z_M=\int\prod_{j=1}^M a_j(u_{j-1})\,P(dX_1\cdots dX_M),
--   $$
--   and the **population measure** $P^{(M)}$ is defined by (6.5):
--   $$
--   \mathbb E^{(M)}[\,\cdot\,]=\frac{\int(\cdot)\prod_{j=1}^M a_j\,P(dX_1\cdots dX_M)}{\int\prod_{j=1}^M a_j\,P(dX_1\cdots dX_M)},\qquad a_j=a_j(u_{j-1}).
--   $$
--   It is the proportion of lineages of the whole forest, weighted by the expected number of descendants, and the BRW concentration inequalities are stated under it.
--
--   **Formalization Note** `popMeasure M` is $Z_M^{-1}$ times $P$ with density $\prod_{j\le M}a_j(u_{j-1})$; $Z_M$ is an extended nonnegative real. It is a probability measure exactly when $0<Z_M<\infty$, which the theorems assume through `IsProbabilityMeasure (B.popMeasure M)`; otherwise it is the zero measure. The weight does not depend on coordinates after $M$.
-- source:
--   Liu, Zhang, Concentration Inequalities for Branching Random Walks with Applications to Phase Transitions in CSPs, arXiv:1601.04794 (artifact sha256 7499631b9d550f66e791c0b3df0879f26102f111fee3052e363ebbff0c72bdcb; no version stamp), (6.5), p. 22; (6.2)–(6.3), p. 21

import Mathlib
import Definitions.Def_LiuZhangBRW_Concentration_BRWModel

open MeasureTheory ProbabilityTheory

namespace LiuZhangBRW.Concentration

namespace BRWModel

/-- The population weight `∏_{j=1}^M a_j(u_{j−1})` of a lineage up to generation `M` (Liu,
Zhang, *Concentration Inequalities for Branching Random Walks with Applications to Phase
Transitions in CSPs*, arXiv:1601.04794, artifact sha256 7499631b…bdcb, (6.5), p. 22, "where
`a_i = a_i(u_{i−1})`"). -/
noncomputable def weight (B : BRWModel) (M : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ∏ j ∈ Finset.Icc 1 M, B.rate j (B.pos (j - 1) ω)

/-- The normalizer `Z_M = ∫ ∏_{j=1}^M a_j P(dX_1 ⋯ dX_M)` of (6.5) (p. 22), the denominator of
the population average, as an extended nonnegative real. -/
noncomputable def normalizer (B : BRWModel) (M : ℕ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (B.weight M ω) ∂B.rwLaw

/-- The population measure `P^(M)` of a branching random walk (Liu, Zhang, arXiv:1601.04794,
artifact sha256 7499631b…bdcb, (6.5), p. 22):
`E^(M)[·] = ∫(·) ∏_{j=1}^M a_j P(dX_1 ⋯ dX_M) / ∫ ∏_{j=1}^M a_j P(dX_1 ⋯ dX_M)`, with
`a_j = a_j(u_{j−1})`; it is the law of a lineage weighted by the expected number of
descendants, the "proportion of spines in the whole forest" of (6.2)–(6.3), p. 21.

**Formalization Note** `popMeasure M = Z_M⁻¹ • (rwLaw with density ∏ a_j(u_{j−1}))`. It is a
probability measure exactly when `0 < Z_M < ∞` (for `Z_M = 0` or `Z_M = ∞` it is the zero
measure), and the statements assume `IsProbabilityMeasure (B.popMeasure M)`, i.e. that (6.5)
is well defined. `Measure.tilted` is not used since a birth rate may vanish. -/
noncomputable def popMeasure (B : BRWModel) (M : ℕ) : Measure (ℕ → ℝ) :=
  (B.normalizer M)⁻¹ • B.rwLaw.withDensity (fun ω => ENNReal.ofReal (B.weight M ω))

end BRWModel

end LiuZhangBRW.Concentration


