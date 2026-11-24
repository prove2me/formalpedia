-- Prove2me | Definitions.Def_CrossSell_Pricing_Supplement_PricingPolicy
-- name    : CrossSell_Pricing_Supplement_PricingPolicy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:50:51.256065+00:00
-- url     : https://prove2.me/theorems/d7b0eb1c-de9d-48b0-8fe4-5f7cc4841056
-- title:
--   Problems (7), (11)–(12), Definition 2 — disjointness and constructed pricing policies
-- statement:
--   Let S be a finite main assortment, T a finite secondary assortment, u_i the main utility, c_i and s_l the two costs, and v_il the secondary utility following outcome i, including outside outcome 0. The auxiliary utility w_l is chosen between the smallest and largest v_il over S+.
--
--   The auxiliary secondary profit and the subsequent main objective are
--   $$A(r)=\frac{\sum_{l\in T}(r_l-s_l)e^{w_l-r_l}}{1+\sum_{l\in T}e^{w_l-r_l}},\qquad B(p;t)=\sum_{i\in S^+}d_i(S,p)(p_i-c_i+t),$$
--   where the outside main margin is zero. A constructed pair globally maximizes A over all real secondary prices, then globally maximizes B(p;A(r)) over all real main prices. This definition assumes neither equal markups nor an approximation guarantee.
--
--   The file also supplies pairwise disjointness on S+, common markups within each offered category, the admissibility of w, the valuation-spread bound, and alpha-optimality as comparison with every true competing price vector. The latter uses the published true sequential profit, with the identical T offered after every outcome. These interfaces keep auxiliary and true profits distinct. The pairwise spread formulation is equivalent to max minus min on the finite nonempty S+. No maximizer is selected using a default value.
-- source:
--   Ke & Wang, Cross-Category Retailing Management: Substitution and Complementarity, accepted manuscript (SSRN 3383023), pp. 14, 17–18, eq. (7), Definition 2, eqs. (11)–(12), alpha-optimality paragraph

import Mathlib
import Definitions.Def_CrossSell_Pricing_Model

namespace CrossSell.Pricing.Supplement
open Finset
variable {ι κ : Type*}

/-- Disjointness in (7), including the first-stage outside outcome. -/
def DisjointSecondary [DecidableEq ι] (S : Finset ι) (T : Option ι → Finset κ) : Prop :=
  ∀ i ∈ S.insertNone, ∀ j ∈ S.insertNone, i ≠ j → Disjoint (T i) (T j)

/-- Auxiliary secondary objective (11); no true conditional valuation is substituted for w. -/
noncomputable def auxSec (T : Finset κ) (s w r : κ → ℝ) : ℝ :=
  (∑ l ∈ T, (r l - s l) * Real.exp (w l - r l)) /
    (1 + ∑ l ∈ T, Real.exp (w l - r l))

/-- Auxiliary main objective (12), with outside main margin zero. -/
noncomputable def auxMain [DecidableEq ι] (S : Finset ι) (u c p : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ S.insertNone, (mainMargin c p i + t) * mainProb S u p i

/-- The actual two successive unrestricted price maximizations (11) and (12). -/
def Constructed [DecidableEq ι] (S : Finset ι) (T : Finset κ)
    (u c : ι → ℝ) (s w : κ → ℝ) (p : ι → ℝ) (r : κ → ℝ) : Prop :=
  (∀ r', auxSec T s w r' ≤ auxSec T s w r) ∧
  (∀ p', auxMain S u c p' (auxSec T s w r) ≤ auxMain S u c p (auxSec T s w r))

/-- Definition 2, restricted to actually offered products. -/
def SameMarkups (S : Finset ι) (T : Finset κ) (c p : ι → ℝ) (s r : κ → ℝ) : Prop :=
  (∃ a : ℝ, ∀ i ∈ S, p i - c i = a) ∧
  (∃ b : ℝ, ∀ l ∈ T, r l - s l = b)

/-- Bounds between the minimum and maximum over the nonempty S+, without real infima. -/
def Admissible [DecidableEq ι] (S : Finset ι) (T : Finset κ)
    (v : Option ι → κ → ℝ) (w : κ → ℝ) : Prop :=
  ∀ l ∈ T, (∃ i ∈ S.insertNone, v i l ≤ w l) ∧
    (∃ i ∈ S.insertNone, w l ≤ v i l)

/-- Equivalent pairwise formulation of max v minus min v ≤ delta on S+. -/
def Spread [DecidableEq ι] (S : Finset ι) (T : Finset κ)
    (v : Option ι → κ → ℝ) (δ : ℝ) : Prop :=
  ∀ l ∈ T, ∀ i ∈ S.insertNone, ∀ j ∈ S.insertNone, v i l - v j l ≤ δ

/-- Comparison with every true competing price vector: no unguarded supremum. -/
def AlphaOptimal (S : Finset ι) (T : Finset κ) (u c : ι → ℝ) (s : κ → ℝ)
    (v : Option ι → κ → ℝ) (p : ι → ℝ) (r : κ → ℝ) (α : ℝ) : Prop :=
  ∀ p' r', α * profit S (fun _ => T) u c s v p' r' ≤
    profit S (fun _ => T) u c s v p r

end CrossSell.Pricing.Supplement


