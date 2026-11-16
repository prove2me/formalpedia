-- Prove2me | Definitions.Def_ZCDPtoGDP_Sharp_Supplement_Privacy
-- name    : ZCDPtoGDP_Sharp_Supplement_Privacy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:09:37.498051+00:00
-- url     : https://prove2.me/theorems/478f8b6a-8d36-4384-b5d1-9a17982d0e15
-- title:
--   Bounded range and logistic differential privacy (Definitions 10 and 12)
-- statement:
--   For a mechanism $M$ on arbitrary measurable spaces and a symmetric neighboring relation, write $P=M(x)$ and $Q=M(x')$ for each neighboring pair. The pair has **bounded range** of width $\varepsilon$ when $P\ll Q$, $Q\ll P$, and there exists a real number $\ell$, allowed to depend on the pair, such that
--   $$\ell\le\log\frac{dQ}{dP}\le\ell+\varepsilon\quad P\text{-almost surely}.$$
--   The mechanism is $\varepsilon$-BR when every neighboring pair has this property. For $\varepsilon\ge0$, define
--   $$L_\varepsilon(\alpha)=\frac{1-\alpha}{1+(e^\varepsilon-1)\alpha},\qquad 0\le\alpha\le1.$$
--   The mechanism is **$\varepsilon$-logistic DP** when $T(P,Q)(\alpha)\ge L_\varepsilon(\alpha)$ for every neighboring pair and every $\alpha\in[0,1]$, using the published trade-off over all randomized tests. The endpoint values of $L_\varepsilon$ are one and zero, and its denominator is at least one on this domain.
--
--   These are the two source classes of Theorem 13. The pairwise predicate is separate from the mechanism wrapper, so it can also be reused for experiments given directly by two probability measures.
--
--   **Formalization Note** The RN derivative is extended nonnegative real valued. The almost-sure clause explicitly records that it is finite and positive before applying its real logarithm. For probability measures this follows from mutual absolute continuity, so this guard excludes no source instance. Markov normalization and symmetric adjacency are supplied at use sites. No centering of $\ell$ is imposed.
-- source:
--   Yu-Wei Chen, Aaradhya Pandey, Jordan Awan, Optimal Conversion from Zero-Concentrated to Gaussian Differential Privacy, STOC 2027 submission #235 (October 2026), Definitions 10 and 12, p. 8. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/235.pdf

import Mathlib
import Definitions.Def_ZCDPtoGDP_Sharp_Privacy

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ZCDPtoGDP.Sharp.Supplement

/-! Source: Chen–Pandey–Awan, STOC 2027 submission #235 (October 2026),
Definitions 10 and 12, p. 8, with the measurable-space mechanism convention of §2, p. 4. -/

/-- Definition 10 for one pair of measures. In uses on probability measures,
mutual absolute continuity already implies a finite positive RN derivative almost
everywhere. Recording that locus explicitly guards `toReal` and `Real.log` without
excluding any pair allowed by the source. The interval location is pair-dependent. -/
def HasBoundedRange {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) (ε : ℝ) : Prop :=
  P ≪ Q ∧ Q ≪ P ∧ ∃ ℓ : ℝ, ∀ᵐ ω ∂P,
    0 < Q.rnDeriv P ω ∧ Q.rnDeriv P ω ≠ ⊤ ∧
    ℓ ≤ Real.log ((Q.rnDeriv P ω).toReal) ∧
    Real.log ((Q.rnDeriv P ω).toReal) ≤ ℓ + ε

/-- A mechanism has bounded range of width `ε` for every ordered neighboring pair.
The theorem using this predicate supplies `IsMarkovKernel` and symmetric adjacency. -/
def IsBR {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (adj : X → X → Prop) (M : Kernel X Ω) (ε : ℝ) : Prop :=
  ∀ x x', adj x x' → HasBoundedRange (M x) (M x') ε

/-- Definition 12: the logistic trade-off formula. For `ε ≥ 0` and `α ∈ [0,1]`,
the denominator is at least one; the endpoint values are one and zero. -/
noncomputable def logisticTradeOff (ε α : ℝ) : ℝ :=
  (1 - α) / (1 + (Real.exp ε - 1) * α)

/-- Definition 12, using the published trade-off over all randomized measurable tests.
The full closed testing interval, including both endpoints, is required. -/
def IsLogisticDP {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (adj : X → X → Prop) (M : Kernel X Ω) (ε : ℝ) : Prop :=
  ∀ x x', adj x x' → ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
    logisticTradeOff ε α ≤ tradeOff (M x) (M x') α

end ZCDPtoGDP.Sharp.Supplement


