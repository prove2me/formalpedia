-- Prove2me | Definitions.Def_MinBuying_Regularity
-- name    : MinBuying_Regularity
-- status  : Definition
-- author  : @mikeh
-- created : 2026-10-30T16:13:28.203054+00:00
-- url     : https://prove2.me/theorems/692420a6-7d68-46a4-95bd-4e2ce1adbfc3
-- title:
--   Quantile regularity and continuous regular instances
-- statement:
--   Defines the lower generalized quantile by an infimum over nonnegative values. Revenue-quantile concavity is imposed on $0<q<1$, equivalent for nonnegative curves to the zero-endpoint convention on $[0,1]$. Continuous regular marginals are nonnegative probability laws absolutely continuous with respect to Lebesgue measure, with no strict positivity or smoothness condition on their densities. An instance has positive finite item count and the source's well-posed optimization conditions.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . Section 2 p.7; Section 4.1 p.16.

import Definitions.Def_MinBuying_Model

noncomputable section
open MeasureTheory Set

namespace MinBuying

/-- The lower generalized quantile at an interior probability. On the domain
used below, the defining set is nonempty and bounded below for a nonnegative
probability law. Values at u=0 and u=1 are not used for regularity. -/
def quantile (F : Measure ℝ) (u : ℝ) : ℝ :=
  sInf {x : ℝ | 0 ≤ x ∧ u ≤ cdf F x}

def revenueQuantile (F : Measure ℝ) (q : ℝ) : ℝ :=
  q * quantile F (1 - q)

/-- Interior concavity avoids the expression 0 times an infinite upper
quantile. For nonnegative curves it is equivalent to concavity on [0,1]
after assigning zero at both endpoints. -/
def Regular (F : Measure ℝ) : Prop :=
  ConcaveOn ℝ (Ioo (0 : ℝ) 1) (revenueQuantile F)

/-- Absolute continuity is the source's standing meaning of continuous
valuation distributions; strict positivity or smoothness of density is not added. -/
def ContinuousRegular (F : Measure ℝ) : Prop :=
  ValidMarginal F ∧ F ≪ volume ∧ Regular F

def RegularInstance {n : ℕ} (F : Fin n → Measure ℝ) : Prop :=
  0 < n ∧ (∀ i, ContinuousRegular (F i)) ∧ WellPosed (productLaw F)

end MinBuying


