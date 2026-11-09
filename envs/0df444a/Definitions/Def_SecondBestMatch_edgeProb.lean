-- Prove2me | Definitions.Def_SecondBestMatch_edgeProb
-- name    : SecondBestMatch_edgeProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:01.305205+00:00
-- url     : https://prove2.me/theorems/5ffc5400-c344-4b6c-9bba-292e36f7bd81
-- title:
--   Edge marginal $q_{ij}(\boldsymbol t)$
-- statement:
--   For an allocation function $q$ and a report profile $\boldsymbol t$, the **edge marginal** of $e = (i,j)$ is the probability that $e$ is traded,
--   $$
--   q_{ij}(\boldsymbol t) := \sum_{M\in\mathcal F,\ (i,j)\in M} q_M(\boldsymbol t).
--   $$
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 2.1, p.7

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- The edge marginal `q_ij(t) := Σ_{M ∈ ℱ, (i,j) ∈ M} q_M(t)` of an allocation function `q`
(Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §2.1, p.7). -/
def edgeProb {B S : Type*} [DecidableEq B] [DecidableEq S] (m : Market B S)
    (q : Profile B S → Finset (B × S) → ℝ) (t : Profile B S) (e : B × S) : ℝ :=
  ∑ M ∈ m.family with e ∈ M, q t M

end SecondBestMatch


