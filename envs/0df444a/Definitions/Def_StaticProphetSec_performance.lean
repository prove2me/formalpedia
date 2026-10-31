-- Prove2me | Definitions.Def_StaticProphetSec_performance
-- name    : StaticProphetSec_performance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:58.90614+00:00
-- url     : https://prove2.me/theorems/a5bdeb8f-242b-412f-8cc0-30418de560b0
-- title:
--   Performance of the policy $(t,p)$: the expected sum of accepted values
-- statement:
--   Let the values $V_1,\dots,V_n$ be independent with laws $\mu_1,\dots,\mu_n$, let the arrival order $\sigma$ be uniform on the $n!$ permutations, and let the coins $B$ be independent with heads probability $p$, all three independent of one another. The **performance** of $(t,p)$ with $k$ items is
--
--   $$\mathcal{ST}^t_k(F)=\mathbb E\Big[\sum_{i\ \mathrm{accepted}} V_i\Big].$$
--
--   This is the sequential meaning of the policy. Formula (5) of the paper is the theorem `StaticProphetSec.acceptance_probability`, not the definition.
--
--   **Formalization Note** Expectations of non-negative quantities are computed in $[0,\infty]$, so no integrability assumption is needed and the value may be $+\infty$.
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, p.16 ("the expected sum of values of accepted applicants"), Remark 1 p.5

import Mathlib
import Definitions.Def_StaticProphetSec_accepted
import Definitions.Def_StaticProphetSec_coinProb

open MeasureTheory
open scoped ENNReal Nat

namespace StaticProphetSec

/-- The performance of the static threshold policy `(t, p)` with `k` items: the expected sum of
the values of the accepted applicants, when the values `V` have independent coordinates with
laws `μ i`, the arrival order `σ` is uniform on the `n!` permutations, the coins `B` are
independent with probability `p` of heads, and `V`, `σ`, `B` are independent (Arnosti & Ma,
arXiv:2108.12893v2: "the expected sum of values of accepted applicants", p.16; Remark 1, p.5).

**Formalization Note.** This is the operational meaning of the policy, not formula (5), which is
stated as a theorem (`StaticProphetSec.acceptance_probability`). An instance is
`μ : Fin n → Measure ℝ` of probability measures with `μ i (Set.Iio 0) = 0`, so
`ENNReal.ofReal (V i) = V i` almost surely. The value lies in `ℝ≥0∞` through `lintegral`, so the
paper's values with infinite mean need no integrability assumption and no junk value arises. -/
noncomputable def performance {n : ℕ} (k : ℕ) (μ : Fin n → Measure ℝ) (t p : ℝ) : ℝ≥0∞ :=
  ∫⁻ V, ∑ B : Fin n → Bool, coinProb p B * ((n ! : ℝ≥0∞)⁻¹ *
    ∑ σ : Equiv.Perm (Fin n), ∑ i ∈ accepted k t V B σ, ENNReal.ofReal (V i)) ∂Measure.pi μ

end StaticProphetSec


