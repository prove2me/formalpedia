-- Prove2me | Definitions.Def_SecondBestMatch_Supplement_HasDeficitAtMost
-- name    : SecondBestMatch_Supplement_HasDeficitAtMost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:40:10.601062+00:00
-- url     : https://prove2.me/theorems/e5412cbe-70d5-4eec-9097-1bebbd4f7491
-- title:
--   Expected deficit at most $s$
-- statement:
--   For $s \ge 0$, a mechanism $(q,p,r)$ has **expected deficit at most $s$** if
--
--   $$
--   \sum_{i\in B}\mathbb E_{\boldsymbol t}[p_i(\boldsymbol t)]-\sum_{j\in S}\mathbb E_{\boldsymbol t}[r_j(\boldsymbol t)]\ \ge\ -s,
--   $$
--
--   the expectations taken under the product prior $\pi$ of all buyer values and seller costs. An outside party covering at most $s$ units of money in expectation can then fund the mechanism. For $s=0$ the condition is ex-ante weak budget balance.
--
--   This is the budget condition of the subsidized second best $\mathrm{SB}_s$ (Definition 5.1), used in Theorem 5.2.
--
--   **Formalization Note** The predicate is defined for every real $s$ and is applied only with $s \ge 0$. The integrals are genuine because the mission's standing assumption `IsAdmissible` makes every payment and receipt integrable.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea7cce1bbfc7757c56937ec4ac13847b6d0025758a63fa8d6a25314385), Section 5.1, p.22

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_Mechanism

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch.Supplement

/-- A mechanism `(q, p, r)` has **expected deficit at most `s`** (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §5.1, p.22):
`Σ_{i ∈ B} E_t[pᵢ(t)] − Σ_{j ∈ S} E_t[rⱼ(t)] ≥ −s`, the expectations under the product prior.
For `s = 0` this is ex-ante weak budget balance (`IsExAnteWBB`).

**Formalization Note** The paper uses the notion for `s ≥ 0`; the predicate is defined for every
real `s` and is only applied with `s ≥ 0`. The integrals are genuine whenever the transfers are
integrable, which `IsAdmissible` (the paper's standing assumption, p.8) supplies. -/
def HasDeficitAtMost {B S : Type*} [Fintype B] [Fintype S] (m : Market B S) (A : Mechanism B S)
    (s : ℝ) : Prop :=
  -s ≤ ∑ i, ∫ t, A.pay t i ∂typeMeasure m - ∑ j, ∫ t, A.recv t j ∂typeMeasure m

end SecondBestMatch.Supplement


