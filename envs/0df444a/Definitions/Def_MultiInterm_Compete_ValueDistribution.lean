-- Prove2me | Definitions.Def_MultiInterm_Compete_ValueDistribution
-- name    : MultiInterm_Compete_ValueDistribution
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:40:08.295507+00:00
-- url     : https://prove2.me/theorems/2de133f5-38a8-4c0c-a45d-d2b00695a5d3
-- title:
--   Value distributions, the reserve function $g$, and second-price revenue $R$
-- statement:
--   Let $\nu$ be an atomless regular probability distribution on the nonnegative reals with support exactly $[0,\bar v]$, where $0<\bar v\le\infty$. Regularity is the published positive-density, nondecreasing-virtual-value definition. No finite first moment is assumed. The general value law is
--   $$D=p\delta_0+(1-p)\nu,\qquad 0\le p<1.$$
--   All results except the explicit extension of Lemma 6.8 impose $p=0$. The mixture represents precisely the possible atom at zero in that extension; it has no atoms elsewhere. The law is proved to have mass one. Let $F(x)=D([0,x])$ and put $g(x)=xF(x)^{n-1}$.
--
--   The second-price revenue function is the displayed closed form
--   $$R(\tau)=n\tau(1-F(\tau))F(\tau)^{n-1}+n(n-1)\int_{(\tau,\infty)}v(1-F(v))F(v)^{n-2}\,dD(v).$$
--   This is the paper's density formula because the positive part of $D$ has density $f$ and $D$ vanishes beyond its support. The possible atom at zero contributes zero. The identity between this formula and the composite game's total payments is a theorem, not an assumption.
--
--   **Formalization Note** Values and finite thresholds use nonnegative reals; $\bar v$ and nonnegative expectations use extended nonnegative reals. Full support means every open interval intersecting the interior has positive probability. The integral is a nonnegative Lebesgue integral, so divergent integrals retain value $+\infty$.
-- source:
--   Ganesh, Moallemi, Weinberg, On the Power and Limitations of Multiple Intermediaries for Single-Item Auctions, STOC 2027 submission (sha256 bdc0557e98c014301646135a34b1532361d0f6133aa7832c59b68394fa2a81dc), p. 8 (PDF 9), regularity; p. 9 (PDF 10), §3.1; pp. 16–17 (PDF 17–18), Definition 6.5 and Lemma 6.8 extension

import Definitions.Def_DSICCompComp_IsRegular

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MultiInterm.Compete

/-- The atomless regular component has exactly interval support starting at zero.
An optional atom at zero accommodates the explicit extension following Lemma 6.8. -/
structure ValueDistribution where
  continuousLaw : Measure ℝ≥0
  regular : DSICCompComp.IsRegular continuousLaw
  atomless : ∀ v : ℝ≥0, continuousLaw {v} = 0
  upper : ℝ≥0∞
  upper_pos : 0 < upper
  supported : ∀ᵐ (v : ℝ≥0) ∂continuousLaw, (v : ℝ≥0∞) ≤ upper
  full_support : ∀ a b : ℝ≥0, a < b → (a : ℝ≥0∞) < upper →
    0 < continuousLaw (Set.Ioo a b)
  zeroMass : ℝ≥0
  zeroMass_lt_one : zeroMass < 1

instance (D : ValueDistribution) : IsProbabilityMeasure D.continuousLaw := D.regular.1

noncomputable def ValueDistribution.law (D : ValueDistribution) : Measure ℝ≥0 :=
  (D.zeroMass : ℝ≥0∞) • Measure.dirac 0 +
    ((1 - D.zeroMass : ℝ≥0) : ℝ≥0∞) • D.continuousLaw

instance (D : ValueDistribution) : IsProbabilityMeasure D.law := by
  constructor
  simp [ValueDistribution.law, add_tsub_cancel_of_le
    (ENNReal.coe_le_one_iff.mpr D.zeroMass_lt_one.le)]

/-- Type domain includes the endpoints of a finite support. -/
def ValueDistribution.Types (D : ValueDistribution) : Set ℝ≥0 :=
  {v | (v : ℝ≥0∞) ≤ D.upper}

noncomputable def ValueDistribution.F (D : ValueDistribution) (x : ℝ≥0) : ℝ≥0 :=
  (D.law (Set.Iic x)).toNNReal

/-- g(x) = x F(x)^(n-1). -/
noncomputable def g (D : ValueDistribution) (n : ℕ) (x : ℝ≥0) : ℝ≥0 :=
  x * D.F x ^ (n - 1)

/-- The displayed closed form of R, written as a nonnegative Lebesgue--Stieltjes
integral. On (τ, v̄] the law has density f; the atom at zero contributes zero.
No nonintegrable real integral is silently replaced by zero. -/
noncomputable def R (D : ValueDistribution) (n : ℕ) (τ : ℝ≥0) : ℝ≥0∞ :=
  (n : ℝ≥0∞) * τ * (1 - (D.F τ : ℝ≥0∞)) * (D.F τ : ℝ≥0∞) ^ (n - 1) +
  (n : ℝ≥0∞) * (n - 1 : ℕ) *
    ∫⁻ v in Set.Ioi τ, (v : ℝ≥0∞) * (1 - (D.F v : ℝ≥0∞)) *
      (D.F v : ℝ≥0∞) ^ (n - 2) ∂D.law

end MultiInterm.Compete


