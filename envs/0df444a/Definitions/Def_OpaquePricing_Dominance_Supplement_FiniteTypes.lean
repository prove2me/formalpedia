-- Prove2me | Definitions.Def_OpaquePricing_Dominance_Supplement_FiniteTypes
-- name    : OpaquePricing_Dominance_Supplement_FiniteTypes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:33:31.42607+00:00
-- url     : https://prove2.me/theorems/26428124-e047-427d-990a-5c1e2226aed2
-- title:
--   Finite valuation laws, weighted revenue, and item choice
-- statement:
--   A finite law has valuation vectors $v_j\in\mathbb R_{\ge0}^N$, positive weights $w_j$ and $\sum_jw_j=1$. Its expected item-pricing revenue and cheaper-index outside utility are
--   $$R_F(p)=\sum_jw_j\operatorname{rev}_{DP}(p;v_j),\qquad U_{>i}(v,p)=\max\left(\{0\}\cup\{(v_k-p_k)^+:k>i\}\right).$$
--   The general finite-type problem builds on the published finite-menu revenue, with no opaque-specific assumptions and no exchangeability. For item identity only, the predicate “buys $i$” refines the source's arbitrary equal-price ties by choosing the smallest index among highest-price utility maximizers. This is necessary for Lemma 10's item-specific statement and leaves every price vector's revenue unchanged. DISPROOF.md records a counterexample to the arbitrary-tie interpretation. If the cheaper-index set is empty, its outside utility is zero.
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), Appendix D, p. 37; Appendix J, Lemma 10, p. 54; §2, p. 8

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting

open MeasureTheory

namespace OpaquePricing.Dominance.Supplement

/-- A finite probability law of valuation vectors; its types all have positive mass. -/
structure FiniteTypes (N m : ℕ) where
  values : Fin m → Fin N → ℝ
  weight : Fin m → ℝ
  nonneg : ∀ j i, 0 ≤ values j i
  weight_pos : ∀ j, 0 < weight j
  total : ∑ j, weight j = 1

noncomputable def finiteRevenue {N m : ℕ} (F : FiniteTypes N m) (p : Fin N → ℝ) : ℝ :=
  ∑ j, F.weight j * dpRevenue p (F.values j)

/-- Highest utility, then highest price, then smallest index among equal-price ties. -/
def buys {N : ℕ} (p v : Fin N → ℝ) (i : Fin N) : Prop :=
  0 ≤ v i - p i ∧
  (∀ k, v k - p k ≤ v i - p i) ∧
  (∀ k, v k - p k = v i - p i → p k ≤ p i) ∧
  (∀ k, v k - p k = v i - p i → p k = p i → i ≤ k)

/-- Cheaper-index utility, including the outside option even for the last item. -/
noncomputable def cheaperUtility {N : ℕ} (p v : Fin N → ℝ) (i : Fin N) : ℝ :=
  ((Finset.univ.filter (fun k => i < k)).image (fun k => max (v k - p k) 0) ∪ {0}).max'
    (by simp)

end OpaquePricing.Dominance.Supplement


