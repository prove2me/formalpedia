-- Prove2me | Definitions.Def_SecondBestMatch_qAlpha
-- name    : SecondBestMatch_qAlpha
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:19:19.127723+00:00
-- url     : https://prove2.me/theorems/47bca722-a9ff-4ca7-b552-096f1c205ddd
-- title:
--   Allocation rule $q^\alpha$ of Eq. (3)
-- statement:
--   The allocation rule $q^\alpha$ retains each edge $e\in M^*(\boldsymbol t)$ independently with probability $\lambda^\alpha_e(\boldsymbol t)$:
--   $$
--   q^\alpha_M(\boldsymbol t) := \begin{cases}\displaystyle\prod_{e\in M}\lambda^\alpha_e(\boldsymbol t)\prod_{e\in M^*(\boldsymbol t)\setminus M}\big(1-\lambda^\alpha_e(\boldsymbol t)\big), & M\subseteq M^*(\boldsymbol t),\\[1ex] 0, & M\not\subseteq M^*(\boldsymbol t).\end{cases}
--   $$
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 4.3, p.16, Eq. (3)

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_retainProb

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- The allocation rule `q^α` of Eq. (3) (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §4.3, p.16): retain each edge `e ∈ M*(t)`
independently with probability `λ^α_e(t)`, so that
`q^α_M(t) = Π_{e ∈ M} λ^α_e(t) · Π_{e ∈ M*(t) \ M} (1 − λ^α_e(t))` if `M ⊆ M*(t)` and `0` otherwise. -/
noncomputable def qAlpha {B S : Type*} [DecidableEq B] [DecidableEq S] (m : Market B S)
    (rank : Finset (B × S) → ℕ) (α : ℝ) (t : Profile B S) (M : Finset (B × S)) : ℝ :=
  if M ⊆ firstBest m rank t then
    (∏ e ∈ M, retainProb m rank α e t) * ∏ e ∈ firstBest m rank t \ M, (1 - retainProb m rank α e t)
  else 0

end SecondBestMatch


