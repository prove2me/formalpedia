-- Prove2me | Definitions.Def_IndependentInfoPricing_Main_Analysis
-- name    : IndependentInfoPricing_Main_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:10.762792+00:00
-- url     : https://prove2.me/theorems/177dfce9-1193-4f4d-bd33-11f49eb923f8
-- title:
--   Conditional classical optima, core quantities and product-sign expectations
-- statement:
--   A sign vector is identified with its positive-coordinate set $S$. Its probability is the product of positive branch probabilities on $S$ and negative branch probabilities outside $S$. Conditional laws are built from the corresponding independent branch laws. The classical optima $C_+(S)$ and $C_-(S)$ optimize operational classical mechanisms on the actual positive and negative index subtypes, including empty blocks.
--
--   The module computes $\bar a,\bar b,U_+,U_-,A,B,\varphi=\min(\bar a,\bar b)$, $\varphi_-=\min(\bar a,U_-)$, and $\varphi_4=\min(\bar a,4t)$ from these laws and thresholds. It also computes $\lambda=\sum_{j:b_j>0}\beta_j$, capped total means and the global reflection of laws and mechanisms. None of the upper-bound estimates is assumed by a definition.
--
--   $$\mathbb E_\xi f(\xi)=\sum_{S\subseteq[Q]}\Pr(\xi=S)f(S).$$
--
--   A real finite-sum version handles arbitrary Bernoulli probabilities and the published submodularity predicate without assuming monotonicity or normalization. Weighted shielding integrates the censored negative sum conditional on each sign set, then averages using the product-sign probabilities. It therefore retains the correlation between that sum's threshold event and the set function of the signs. This is the independent joint sign/magnitude construction, not an independence assumption on the final event.
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), §§2–4.5, starting printed p.40 (PDF p.42); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Laws
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Sign vectors are their positive-coordinate finite sets. -/
def signWeight (F : Marginals ι) (S : Finset ι) : ℝ≥0∞ :=
  ∏ i, if i ∈ S then F i (Set.Ioi 0) else F i (Set.Iio 0)

def signExpectation (F : Marginals ι) (f : Finset ι → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ S ∈ (Finset.univ : Finset ι).powerset, signWeight F S * f S

def orthant (S : Finset ι) : Set (Values ι) :=
  {v | ∀ i, if i ∈ S then 0 < v i else v i < 0}

def orthantLaw (F : Marginals ι) (S : Finset ι) : Measure (Values ι) :=
  productLaw (fun i => if i ∈ S then positiveBranch (F i) else
    Measure.map (fun x : ℝ => -x) (negativeBranch (F i)))

def positiveClassical (F : Marginals ι) (S : Finset ι) : ℝ≥0∞ :=
  optClassical (productLaw (fun i : S => positiveBranch (F i)))

def negativeClassical (F : Marginals ι) (S : Finset ι) : ℝ≥0∞ :=
  optClassical (productLaw (fun i : (Finset.univ \ S : Finset ι) => negativeBranch (F i)))

def aBar (F : Marginals ι) (S : Finset ι) : ℝ≥0∞ := ∑ i ∈ S, branchRevenue (F i) true

def bBar (F : Marginals ι) (S : Finset ι) : ℝ≥0∞ :=
  ∑ i ∈ Finset.univ \ S, branchRevenue (F i) false

def uPlus (F : Marginals ι) (Θ : ℝ) (S : Finset ι) : ℝ≥0∞ :=
  ∑ i ∈ S, coreMean (positiveBranch (F i)) Θ

def uMinus (F : Marginals ι) (t : ℝ) (S : Finset ι) : ℝ≥0∞ :=
  ∑ i ∈ Finset.univ \ S, coreMean (negativeBranch (F i)) t

def tailsPlus (F : Marginals ι) (Θ : ℝ) (S : Finset ι) : ℝ≥0∞ :=
  ∑ i ∈ S, tailProbability (positiveBranch (F i)) Θ

def tailsMinus (F : Marginals ι) (t : ℝ) (S : Finset ι) : ℝ≥0∞ :=
  ∑ i ∈ Finset.univ \ S, tailProbability (negativeBranch (F i)) t

def phi (F : Marginals ι) (S : Finset ι) : ℝ≥0∞ := min (aBar F S) (bBar F S)

def phiMinus (F : Marginals ι) (t : ℝ) (S : Finset ι) : ℝ≥0∞ := min (aBar F S) (uMinus F t S)

def phiFour (F : Marginals ι) (t : ℝ) (S : Finset ι) : ℝ≥0∞ := min (aBar F S) (ENNReal.ofReal (4*t))

def lambda (F : Marginals ι) : ℝ :=
  ∑ i, if 0 < branchRevenue (F i) false then negativeProbability (F i) else 0

def negativeCappedMean (F : Marginals ι) (t : ℝ) : ℝ≥0∞ :=
  ∑ i, F i (Set.Iio 0) * cappedMean (negativeBranch (F i)) t

def censoredTotal (positive : Bool) (Θ : ℝ) (v : Values ι) : ℝ :=
  ∑ i, min (max (if positive then v i else -v i) 0) Θ

def censoredExpectation (F : Marginals ι) (positive : Bool) (Θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ v, ENNReal.ofReal (censoredTotal positive Θ v) ∂productLaw F

def reflectMechanism (m : DirectMechanism ι) : DirectMechanism ι :=
  ⟨fun v => 1 - m.allocation (-v), fun v => m.price (-v)⟩

def reflectDomain (T : Set (Values ι)) : Set (Values ι) := {v | -v ∈ T}

def reflectedMarginals (F : Marginals ι) : Marginals ι :=
  fun i => Measure.map (fun x : ℝ => -x) (F i)

/-- Finite product Bernoulli expectation, including probabilities 0 and 1. -/
def cubeExpectation (α : ι → ℝ) (f : Finset ι → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset ι).powerset,
    (∏ i, if i ∈ S then α i else 1 - α i) * f S

def countPositive (w : ι → ℝ) (S : Finset ι) : ℝ := ∑ i ∈ S, w i

def countNegative (w : ι → ℝ) (S : Finset ι) : ℝ := ∑ i ∈ Finset.univ \ S, w i

/-- The joint sign/magnitude product model, retaining all dependence of shielding on signs. -/
def shieldingExpectation (α : ι → ℝ) (D : Marginals ι) (t : ℝ) (f : Finset ι → ℝ) : ℝ≥0∞ :=
  ∑ S ∈ (Finset.univ : Finset ι).powerset,
    ENNReal.ofReal ((∏ i, if i ∈ S then α i else 1 - α i) * f S) *
      productLaw D {w | t ≤ ∑ i ∈ Finset.univ \ S, min (w i) t}

end IndependentInfoPricing.Main


