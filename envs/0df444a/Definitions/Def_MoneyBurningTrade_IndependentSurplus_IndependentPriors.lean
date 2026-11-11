-- Prove2me | Definitions.Def_MoneyBurningTrade_IndependentSurplus_IndependentPriors
-- name    : MoneyBurningTrade_IndependentSurplus_IndependentPriors
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:47:44.545859+00:00
-- url     : https://prove2.me/theorems/6f281970-2615-4f2e-be1d-40d7fea95da9
-- title:
--   Section 4.2 — continuous independent mixture construction
-- statement:
--   For $k\ge2$ and the symmetric grid, choose $0<\tau\le\delta L/100$, $0<\eta<\tau$ and $R>1$ satisfying (21). For $1\le\ell<k$, let $\Delta_\ell=q_{2\ell+1}-q_{2\ell-1}$, $S_\ell=[q_{2\ell-1},q_{2\ell-1}+\eta]$, $B_\ell=[q_{2\ell+1}-\eta,q_{2\ell+1}]$, and
--
--   $$\alpha_\ell=R^\ell/\sqrt{\Delta_\ell},\qquad\beta_\ell=R^{-\ell}/\sqrt{\Delta_\ell},\qquad C=\big((\sum_\ell\alpha_\ell)(\sum_\ell\beta_\ell)\big)^{-1}.$$
--
--   The seller prior mixes continuous uniform laws on $S_\ell$ with weights $\alpha_\ell/\sum\alpha$; the buyer prior mixes uniform laws on $B_\ell$ with weights $\beta_\ell/\sum\beta$. Their joint prior is the product. Each uniform law is restricted Lebesgue measure divided by its positive length $\eta$. Equation (21) uses the signed exponent $\ell-r$. Input validity contains only these numeric parameter conditions. Probability normalization, support in $[0,1]$, incentive validity and performance are conclusions of the subsequent theorems.
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), §4.2, equations (20)–(21), printed p. 26–28 (PDF p. 27–29); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Definitions.Def_MoneyBurningTrade_IndependentSurplus_SymmetricGrid
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_SeparationGrid
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_NormalizedMechanism

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus

/-- Raw parameters for §4.2. Conditions below constrain inputs only. -/
structure IndependentParameters where
  k : ℕ
  τ : ℝ
  η : ℝ
  R : ℝ

/-- The source's component index set ℓ=1,...,k-1; empty when k<2. -/
def componentIndices (A : IndependentParameters) : Finset ℕ := Finset.Icc 1 (A.k - 1)

/-- The source's Δ_ℓ. -/
noncomputable def componentGap (A : IndependentParameters) (ℓ : ℕ) : ℝ :=
  (symmetricGrid A.k).q (2 * ℓ + 1) - (symmetricGrid A.k).q (2 * ℓ - 1)

/-- Seller component S_ℓ, with the closed endpoints of §4.2. -/
noncomputable def sellInterval (A : IndependentParameters) (ℓ : ℕ) : Set ℝ :=
  Set.Icc ((symmetricGrid A.k).q (2 * ℓ - 1))
    ((symmetricGrid A.k).q (2 * ℓ - 1) + A.η)

/-- Buyer component B_ℓ. -/
noncomputable def buyInterval (A : IndependentParameters) (ℓ : ℕ) : Set ℝ :=
  Set.Icc ((symmetricGrid A.k).q (2 * ℓ + 1) - A.η)
    ((symmetricGrid A.k).q (2 * ℓ + 1))

/-- Equation (21); the exponent ℓ-r is an integer and is negative on every
nonzero summand. No natural-number subtraction is used for this exponent. -/
noncomputable def crossContribution (A : IndependentParameters) : ℝ :=
  ∑ ℓ ∈ componentIndices A, ∑ r ∈ componentIndices A,
    if ℓ < r then A.R ^ ((ℓ : ℤ) - (r : ℤ)) *
      ((symmetricGrid A.k).q (2 * r + 1) - (symmetricGrid A.k).q (2 * ℓ - 1)) /
      Real.sqrt (componentGap A ℓ * componentGap A r)
    else 0

/-- Exactly the parameter choices of §4.2, before the theorem's ε-size choice.
Grid validity, probability normalization, DSIC, and all surplus inequalities
are deliberately not fields of these input conditions. -/
def ValidIndependentParameters (A : IndependentParameters) : Prop :=
  2 ≤ A.k ∧ 0 < A.τ ∧
  A.τ ≤ symmetricDelta A.k * minGap (symmetricGrid A.k) / 100 ∧
  0 < A.η ∧ A.η < A.τ ∧ 1 < A.R ∧ crossContribution A ≤ 1

/-- The source's α_ℓ. -/
noncomputable def sellerWeight (A : IndependentParameters) (ℓ : ℕ) : ℝ :=
  A.R ^ (ℓ : ℤ) / Real.sqrt (componentGap A ℓ)

/-- The source's β_ℓ, with negative integer exponent. -/
noncomputable def buyerWeight (A : IndependentParameters) (ℓ : ℕ) : ℝ :=
  A.R ^ (-(ℓ : ℤ)) / Real.sqrt (componentGap A ℓ)

/-- The normalizing constant C in §4.2. -/
noncomputable def normalizingConstant (A : IndependentParameters) : ℝ :=
  1 / ((∑ ℓ ∈ componentIndices A, sellerWeight A ℓ) *
    (∑ ℓ ∈ componentIndices A, buyerWeight A ℓ))

/-- Seller mixture of continuous uniform laws. For valid parameters each interval
has positive length η. Normalization and [0,1] support are theorem conclusions. -/
noncomputable def sellerPrior (A : IndependentParameters) : Measure ℝ :=
  ∑ ℓ ∈ componentIndices A,
    ENNReal.ofReal (sellerWeight A ℓ / (∑ r ∈ componentIndices A, sellerWeight A r)) •
      (ENNReal.ofReal A.η)⁻¹ • volume.restrict (sellInterval A ℓ)

/-- Buyer mixture, sampled independently using sellerPrior.prod buyerPrior. -/
noncomputable def buyerPrior (A : IndependentParameters) : Measure ℝ :=
  ∑ ℓ ∈ componentIndices A,
    ENNReal.ofReal (buyerWeight A ℓ / (∑ r ∈ componentIndices A, buyerWeight A r)) •
      (ENNReal.ofReal A.η)⁻¹ • volume.restrict (buyInterval A ℓ)

/-- The common WBB mechanism in this independent construction. -/
noncomputable def independentMechanism (A : IndependentParameters) : SecondBestBT.Mechanism :=
  normalizedMechanism (symmetricGrid A.k) A.τ

end MoneyBurningTrade.IndependentSurplus


