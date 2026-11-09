-- Prove2me | Definitions.Def_SecondBestMatch_retainProb
-- name    : SecondBestMatch_retainProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:18:08.31606+00:00
-- url     : https://prove2.me/theorems/c16e5fbe-a673-4f60-b4aa-38894f4f9903
-- title:
--   Retention probability $\lambda^\alpha_e(\boldsymbol t)$
-- statement:
--   Fix $\alpha>0$, a profile $\boldsymbol t$ of the support product and an edge $e=(i,j)$. If $e\in M^*(\boldsymbol t)$, the **retention probability** $\lambda^\alpha_e(\boldsymbol t)$ is the probability that the local Beta-contraction rule retains $e$: draw $Z\sim\mathrm{Beta}\big(\tfrac1{1+\alpha},\tfrac1{1+\alpha}\big)$, draw independent uniform hidden ranks $(\rho,\sigma)$ in the rank rectangle of the reported pair, $(\Pr[v_i>v_i^{\rm rep}],\Pr[v_i\ge v_i^{\rm rep}]]\times(\Pr[c_j<c_j^{\rm rep}],\Pr[c_j\le c_j^{\rm rep}]]$, and retain $e$ iff $(\rho,\sigma)\in\mathcal D_Z$, where $\mathcal D$ is the selection region of $e$ for $\boldsymbol t_{-ij}$. If $e\notin M^*(\boldsymbol t)$, $\lambda^\alpha_e(\boldsymbol t) = 0$.
--
--   **Formalization Note** The uniform hidden ranks are the Lebesgue measure on the rank rectangle normalized by its area $\Pr[v_i = v_i^{\rm rep}]\Pr[c_j = c_j^{\rm rep}]$.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 4.3, p.16 (with the Remark on p.16)

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_betaExpect
import Definitions.Def_SecondBestMatch_contractRegion
import Definitions.Def_SecondBestMatch_edgeRankRegion

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- The retention probability `λ^α_e(t)` of the edge `e = (i, j)` at the support profile `t`
(Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §4.3, p.16, with the Remark on p.16): if `e ∈ M*(t)`, the probability that the local
Beta-contraction rule retains `e`, where `Z ∼ Beta(1/(1+α), 1/(1+α))` and the reported pair
`(vᵢ, cⱼ)` is replaced by independent uniform hidden ranks in its rank rectangle
`(P(vᵢ > v), P(vᵢ ≥ v)] × (P(cⱼ < c), P(cⱼ ≤ c)]`; `λ^α_e(t) = 0` if `e ∉ M*(t)`.

**Formalization Note** The hidden uniform ranks are the normalized Lebesgue measure on the rank
rectangle, whose area is `P(vᵢ = v) P(cⱼ = c)`; the rule retains `e` at the rank pair `(ρ, σ)` iff
`(ρ, σ) ∈ 𝒟_Z`. -/
noncomputable def retainProb {B S : Type*} [DecidableEq B] [DecidableEq S] (m : Market B S)
    (rank : Finset (B × S) → ℕ) (α : ℝ) (e : B × S) (t : Profile B S) : ℝ :=
  if e ∈ firstBest m rank t then
    betaExpect (1 / (1 + α)) (1 / (1 + α)) fun z =>
      (volume (contractRegion α z (edgeRankRegion m rank e t) ∩
        (Ioc ((m.buyerLaw e.1).real (Ioi (t.1 e.1))) ((m.buyerLaw e.1).real (Ici (t.1 e.1))) ×ˢ
          Ioc ((m.sellerLaw e.2).real (Iio (t.2 e.2))) ((m.sellerLaw e.2).real (Iic (t.2 e.2)))))).toReal /
        ((m.buyerLaw e.1).real {t.1 e.1} * (m.sellerLaw e.2).real {t.2 e.2})
  else 0

end SecondBestMatch


