-- Prove2me | Definitions.Def_BundleSearch_MatureNew_Model
-- name    : BundleSearch_MatureNew_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:25:22.977093+00:00
-- url     : https://prove2.me/theorems/a21b9a7b-dd47-4fac-b725-8f966dfea717
-- title:
--   §§3–5.2 — uniform-valuation search, separate selling, and bundle revenue
-- statement:
--   A zero-cost seller faces a unit mass of customers with independent valuations $V_1,V_2\sim U[0,1]$. Product 1 is mature, so its value is known; product 2 is new and can be inspected at cost $c\ge0$. Prices $p_1,p_2,p_B$ are nonnegative when optimized. The new product can be bought without inspection, searched and bought conditional on its realized value, or left. A bundle can likewise be bought immediately, searched and bought conditional on $v_1+v_2\ge p_B$, or left. The choice uses the separate footnote-10 tie rule.
--
--   Writing $D_N(c,p_2)$ for new-product demand and $D_B(c,p_B)$ for bundle demand, the revenue functions are
--
--   $$R_S(c,p_1,p_2)=p_1\Pr(V_1\ge p_1)+p_2D_N(c,p_2),\qquad R_B(c,p_B)=p_BD_B(c,p_B).$$
--
--   Expectations are integrals over $[0,1]$; bundle demand integrates each customer's conditional purchase probability over $v_1$. These definitions are the economic objects optimized by the propositions and compared in Theorem 1.
--
--   **Formalization Note** The tail probability intersects the valuation event with $[0,1]$. The conditional bundle demand counts a customer once at payoff ties, including when $c=0$. At zero search cost and a price beyond the largest attainable value, searching ties leaving at zero payoff; the choice rule selects leaving, as in Lemma 1(ii) and the high-price bundle regime.
-- source:
--   Wu, Jin & Chen, Managing Customer Search via Product Bundling, SSRN working paper 3692871 (version of 2022-01-17), pp. 7–13, §§3–5.2, equations (1)–(2)

import Mathlib
import Definitions.Def_BundleSearch_MatureNew_Choice

namespace BundleSearch.MatureNew
open MeasureTheory

/-- The mean of a uniform valuation on [0, 1]. -/
noncomputable def meanVal : ℝ := ∫ v in (0 : ℝ)..1, v

/-- The probability that a uniform valuation on [0, 1] is at least `t`. -/
noncomputable def probGe (t : ℝ) : ℝ :=
  (volume {v : ℝ | v ∈ Set.Icc (0 : ℝ) 1 ∧ t ≤ v}).toReal

/-- Payoff from buying the new product without search. -/
noncomputable def nsPayoffNew (p : ℝ) : ℝ := meanVal - p

/-- Expected payoff from searching the new product at cost `c`, then buying only when
the realized valuation covers price `p`. -/
noncomputable def searchPayoffNew (c p : ℝ) : ℝ :=
  (∫ v in (0 : ℝ)..1, max (v - p) 0) - c

/-- At a zero-payoff tie between search and leaving, leave when no valuation in
the support can exceed the price. The boundary price 1 remains in Lemma 1's
search band. -/
noncomputable def SearchesNew (c p : ℝ) : Prop :=
  Searches (nsPayoffNew p) (searchPayoffNew c p) ∧ p ≤ 1

/-- The probability of buying the new product under the three-option choice rule. -/
noncomputable def demandNew (c p : ℝ) : ℝ := by
  classical
  exact if BuysWithoutSearch (nsPayoffNew p) (searchPayoffNew c p) then 1
    else if SearchesNew c p then probGe p else 0

/-- Revenue from the new product under separate selling. -/
noncomputable def revenueNew (c p : ℝ) : ℝ := p * demandNew c p

/-- Revenue from the mature product under separate selling. -/
noncomputable def revenueMature (p : ℝ) : ℝ := p * probGe p

/-- The sum of the two revenues when the products are sold separately. -/
noncomputable def sepRevenue (c p1 p2 : ℝ) : ℝ :=
  revenueMature p1 + revenueNew c p2

/-- Payoff from buying the bundle without searching the new product. -/
noncomputable def nsPayoffB (pB v1 : ℝ) : ℝ := v1 + meanVal - pB

/-- Expected payoff from searching the new product at cost `c`, given the mature
valuation `v1`, then buying the bundle only if its value covers price `pB`. -/
noncomputable def searchPayoffB (c pB v1 : ℝ) : ℝ :=
  (∫ v2 in (0 : ℝ)..1, max (v1 + v2 - pB) 0) - c

/-- The bundle analogue of `SearchesNew`: search is not selected when the
highest possible bundle value falls strictly below its price. -/
noncomputable def SearchesB (c pB v1 : ℝ) : Prop :=
  Searches (nsPayoffB pB v1) (searchPayoffB c pB v1) ∧ pB - v1 ≤ 1

/-- Bundle purchase probability conditional on the mature valuation `v1`. -/
noncomputable def buyProbB (c pB v1 : ℝ) : ℝ := by
  classical
  exact if BuysWithoutSearch (nsPayoffB pB v1) (searchPayoffB c pB v1) then 1
    else if SearchesB c pB v1 then
      probGe (pB - v1) else 0

/-- Bundle demand, integrating the conditional purchase probability over a uniform
mature-product valuation. Each customer is counted once, including at payoff ties. -/
noncomputable def demandB (c pB : ℝ) : ℝ :=
  ∫ v1 in (0 : ℝ)..1, buyProbB c pB v1

/-- Bundle revenue at price `pB`. -/
noncomputable def bundleRevenue (c pB : ℝ) : ℝ := pB * demandB c pB

end BundleSearch.MatureNew


