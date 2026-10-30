-- Prove2me | Definitions.Def_SeqPostedPricing_MatroidSPM_allocProb
-- name    : SeqPostedPricing_MatroidSPM_allocProb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:32:37.888774+00:00
-- url     : https://prove2.me/theorems/ba901c33-8652-48c7-b5f4-793a3fc75d54
-- title:
--   Allocation probability $q_i^M=\Pr_{\mathbf v}[i\in M(\mathbf v)]$
-- statement:
--   For independent values $v_i\sim\mu_i$ and a mechanism $M$, the **allocation probability** of agent $i$ is
--
--   $$
--   q_i^M=\Pr_{\mathbf v}\big[i\in M(\mathbf v)\big],
--   $$
--
--   the probability over $v_1,\dots,v_n$ with which $M$ serves agent $i$. In §4 these numbers, for Myerson's mechanism, define the prices of the sequential posted-price mechanism.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, Lemma 2, p. 5

import Mathlib
import Definitions.Def_SeqPostedPricing_MatroidSPM_Mechanism
open MeasureTheory

namespace SeqPostedPricing.MatroidSPM

/-- **Allocation probability `q_i^M`.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, Lemma 2, p. 5 (PDF p. 7): "q_i^M is the probability (over v1, · · · , vn) with which M
allocates to agent i".

`allocProb μ M i = Pr_v[i ∈ M(v)]` under the product law `Measure.pi μ`. -/
noncomputable def allocProb {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (M : Mechanism n) (i : Fin n) : ℝ :=
  (Measure.pi μ {v | i ∈ M.alloc v}).toReal

end SeqPostedPricing.MatroidSPM


