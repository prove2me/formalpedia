-- Prove2me | Definitions.Def_SecondBestMatch_Supplement_InReducedForms
-- name    : SecondBestMatch_Supplement_InReducedForms
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:42:17.60223+00:00
-- url     : https://prove2.me/theorems/f70d2336-50e1-4c18-b819-e995d24d4f02
-- title:
--   Reduced-form set $\mathcal R$
-- statement:
--   Let $(x,y)$ consist of a function $x_i$ for every buyer $i$ and a function $y_j$ for every seller $j$. Then $(x,y)\in\mathcal R$ if there is a Borel allocation kernel $q$ that selects only feasible matchings at every report profile and whose interim service rules agree with $(x,y)$ almost everywhere:
--
--   1. for each matching $M$, $\boldsymbol t\mapsto q_M(\boldsymbol t)$ is Borel measurable;
--   2. at every report profile $\boldsymbol t\in[0,1]^K$, $q(\boldsymbol t)$ is a probability distribution on $\mathcal F$ (nonnegative, zero off $\mathcal F$, summing to one);
--   3. $x_i(v)=\mathbb E_{\boldsymbol t_{-i}}[q_i(v,\boldsymbol t_{-i})]$ for $F_i$-almost every $v$, and $y_j(c)=\mathbb E_{\boldsymbol t_{-j}}[q_j(c,\boldsymbol t_{-j})]$ for $G_j$-almost every $c$.
--
--   Here $q_i$ and $q_j$ are the probabilities that buyer $i$, respectively seller $j$, is matched. $\mathcal R\subseteq\prod_i L^\infty(F_i)\times\prod_j L^\infty(G_j)$ contains no incentive, participation or budget condition.
--
--   **Formalization Note** The allocation conditions are exactly those of the mission's `IsAdmissible`. Identifying reduced forms that agree almost everywhere is built in through the almost-everywhere equalities with the published interim service rules.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea7cce1bbfc7757c56937ec4ac13847b6d0025758a63fa8d6a25314385), Appendix A.1, p.27

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_InUnitCube
import Definitions.Def_SecondBestMatch_interimBuyerService
import Definitions.Def_SecondBestMatch_interimSellerService

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch.Supplement

/-- Membership in the **reduced-form set `ℛ`** (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Appendix A.1, p.27):
`(x, y) ∈ ℛ ⊆ Πᵢ L∞(Fᵢ) × Πⱼ L∞(Gⱼ)` iff `(x, y)` is, prior-almost everywhere, the pair of
interim service rules of a Borel allocation kernel that selects only feasible matchings at every
report profile.

**Formalization Note** The kernel `q` satisfies exactly the allocation conditions of the
published `IsAdmissible`: measurable in the profile for each matching, nonnegative, zero off `ℱ`
and summing to one over `ℱ` at every profile of `[0, 1]^K`. The paper identifies reduced forms
that agree almost everywhere; here `xᵢ` and `yⱼ` are functions `ℝ → ℝ` and the identification is
the `=ᵐ[Fᵢ]`, `=ᵐ[Gⱼ]` equalities with the interim service rules `interimBuyerService`,
`interimSellerService` of `q`. No incentive, participation or budget condition is part of `ℛ`. -/
def InReducedForms {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]
    (m : Market B S) (x : B → ℝ → ℝ) (y : S → ℝ → ℝ) : Prop :=
  ∃ q : Profile B S → Finset (B × S) → ℝ,
    (∀ M, Measurable fun t => q t M) ∧
    (∀ t, InUnitCube t → ∀ M, 0 ≤ q t M) ∧
    (∀ t, InUnitCube t → ∀ M, M ∉ m.family → q t M = 0) ∧
    (∀ t, InUnitCube t → ∑ M ∈ m.family, q t M = 1) ∧
    (∀ i, x i =ᵐ[m.buyerLaw i] interimBuyerService m q i) ∧
    (∀ j, y j =ᵐ[m.sellerLaw j] interimSellerService m q j)

end SecondBestMatch.Supplement


