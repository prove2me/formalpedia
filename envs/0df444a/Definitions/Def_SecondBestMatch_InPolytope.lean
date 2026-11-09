-- Prove2me | Definitions.Def_SecondBestMatch_InPolytope
-- name    : SecondBestMatch_InPolytope
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:19:42.955193+00:00
-- url     : https://prove2.me/theorems/1bb45aeb-7a74-40ba-9bf0-df32501714e6
-- title:
--   The polytope $\mathcal P$ of monotone allocation rules
-- statement:
--   For finite-support priors, $\mathcal P$ is the polytope of randomized allocation rules on the finite type space such that
--
--   1. at every type profile, the allocation is a probability distribution over $\mathcal F$;
--   2. every buyer's interim service $x_i$ is nondecreasing in her value;
--   3. every seller's interim service $y_j$ is nonincreasing in her cost.
--
--   **Formalization Note** The finite type space is the support product: item 1 is asked at every profile of the support product and items 2–3 between support points. Values of $q$ off the support product carry no probability, are unconstrained and never change any quantity. No measurability is asked: under a finite-support prior every function is almost everywhere strongly measurable, so the interim integrals are the paper's finite sums.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 3.2, pp.10–11

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_atoms
import Definitions.Def_SecondBestMatch_IsSupportProfile
import Definitions.Def_SecondBestMatch_interimBuyerService
import Definitions.Def_SecondBestMatch_interimSellerService

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- The polytope `𝒫` of randomized allocation rules on the finite type space (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §3.2,
pp.10–11): (i) at every type profile the allocation is a probability distribution over `ℱ`;
(ii) every buyer's interim service is nondecreasing in her value; (iii) every seller's interim
service is nonincreasing in her cost.

**Formalization Note** The finite type space is the support product: (i) is asked at every
support profile, (ii) and (iii) between support points. Values of `q` off the support product are
unconstrained; they carry no probability and never change any quantity. No measurability is
asked: for a finite-support prior every function is almost everywhere strongly measurable, so
the interim integrals are the finite sums of the paper (see the sanity file). -/
structure InPolytope {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]
    (m : Market B S) (q : Profile B S → Finset (B × S) → ℝ) : Prop where
  nonneg : ∀ t, IsSupportProfile m t → ∀ M, 0 ≤ q t M
  feasible : ∀ t, IsSupportProfile m t → ∀ M, M ∉ m.family → q t M = 0
  sum_one : ∀ t, IsSupportProfile m t → ∑ M ∈ m.family, q t M = 1
  buyer_mono : ∀ i, ∀ v ∈ atoms (m.buyerLaw i), ∀ v' ∈ atoms (m.buyerLaw i), v ≤ v' →
    interimBuyerService m q i v ≤ interimBuyerService m q i v'
  seller_anti : ∀ j, ∀ c ∈ atoms (m.sellerLaw j), ∀ c' ∈ atoms (m.sellerLaw j), c ≤ c' →
    interimSellerService m q j c' ≤ interimSellerService m q j c

end SecondBestMatch


