-- Prove2me | Definitions.Def_IndependentInfoPricing_Main_Laws
-- name    : IndependentInfoPricing_Main_Laws
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:05.740846+00:00
-- url     : https://prove2.me/theorems/f76c484c-0f37-46b5-8871-9921dfe7e5ea
-- title:
--   Product payoff laws, conditional magnitudes and half-tail scope
-- statement:
--   Independent real payoff coordinates are represented by arbitrary Borel probability marginals and their product measure. An occurring positive branch is the law conditional on $v_i>0$; an occurring negative branch is the reflected law conditional on $v_i<0$. Absent branches are zero measures and carry weight zero, with no monopoly-price or shape assumption.
--
--   For a magnitude law $D$, write
--
--   $$\operatorname{Rev}(D)=\sup_{p\ge0}p\Pr(D\ge p),\qquad \Pr(D\ge\operatorname{Rev}(D))\ge\tfrac12.$$
--
--   The latter is the half-tail property. A finite monopoly price means attainment of this supremum at a finite nonnegative price, rather than an assumed finite first moment. The positive theorem's scope requires marginal densities continuously differentiable on the interior of their topological support, and finite monopoly-price attainment plus half-tail only for occurring branches. Interval support and strictly positive interior density are not required. Density representatives may be assigned finite values on null boundary sets without changing the law; endpoint extended limits are not evaluated by these definitions.
--
--   Core means integrate $D1_{D\le t}$ and tails use the strict event $D>t$. Capped means instead integrate $\min(D,t)$; these are distinct. All means, revenue suprema and bundle revenues use nonnegative extended reals. A separate intermediate scope keeps probability, absence of zero atoms and finite monopoly-price attainment without imposing differentiability or half-tail.
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), §§2–4.5, starting printed p.10 (PDF p.12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Menus

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

abbrev Marginals (ι : Type) := ι → Measure ℝ

def ProbabilityMarginals {ι : Type} (F : Marginals ι) : Prop := ∀ i, IsProbabilityMeasure (F i)

def productLaw {ι : Type} [Fintype ι] (F : Marginals ι) : Measure (Values ι) := Measure.pi F

def nonnegativeLaws {ι : Type} (F : Marginals ι) : Prop :=
  ProbabilityMarginals F ∧ ∀ i, F i (Set.Iio 0) = 0

def scalarRevenue (D : Measure ℝ) : ℝ≥0∞ :=
  ⨆ (p : ℝ) (_ : 0 ≤ p), ENNReal.ofReal p * D (Set.Ici p)

def FiniteMonopolyPrice (D : Measure ℝ) : Prop :=
  ∃ p : ℝ, 0 ≤ p ∧ scalarRevenue D = ENNReal.ofReal p * D (Set.Ici p)

/-- The extended threshold makes sense even for a law of infinite revenue. -/
def HalfTail (D : Measure ℝ) : Prop :=
  (1 / 2 : ℝ≥0∞) ≤ D {x | scalarRevenue D ≤ ENNReal.ofReal x}

def conditionalLaw (D : Measure ℝ) (A : Set ℝ) : Measure ℝ := (D A)⁻¹ • D.restrict A

def positiveBranch (D : Measure ℝ) : Measure ℝ := conditionalLaw D (Set.Ioi 0)

def negativeBranch (D : Measure ℝ) : Measure ℝ :=
  Measure.map (fun x : ℝ => -x) (conditionalLaw D (Set.Iio 0))

def positiveProbability (D : Measure ℝ) : ℝ := (D (Set.Ioi 0)).toReal

def negativeProbability (D : Measure ℝ) : ℝ := (D (Set.Iio 0)).toReal

/-- Absent branches are zero measures and receive zero weight, without shape assumptions. -/
def branchRevenue (D : Measure ℝ) (positive : Bool) : ℝ≥0∞ :=
  if positive then scalarRevenue (positiveBranch D) else scalarRevenue (negativeBranch D)

/-- A topological support defined without an interval or positivity assumption. -/
def lawSupport (D : Measure ℝ) : Set ℝ :=
  {x | ∀ r : ℝ, 0 < r → 0 < D (Set.Ioo (x-r) (x+r))}

def SmoothDensity (D : Measure ℝ) : Prop :=
  ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Measurable f ∧
    D = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
    ContDiffOn ℝ 1 f (interior (lawSupport D))

def HalfTailScope {ι : Type} (F : Marginals ι) : Prop :=
  ProbabilityMarginals F ∧ (∀ i, SmoothDensity (F i)) ∧
  ∀ i, (F i (Set.Ioi 0) ≠ 0 → FiniteMonopolyPrice (positiveBranch (F i)) ∧ HalfTail (positiveBranch (F i))) ∧
    (F i (Set.Iio 0) ≠ 0 → FiniteMonopolyPrice (negativeBranch (F i)) ∧ HalfTail (negativeBranch (F i)))

/-- Useful scope for probabilistic intermediate results: no differentiability is built in. -/
def BranchScope {ι : Type} (F : Marginals ι) : Prop :=
  ProbabilityMarginals F ∧ (∀ i, F i {0} = 0) ∧
  ∀ i, (F i (Set.Ioi 0) ≠ 0 → FiniteMonopolyPrice (positiveBranch (F i))) ∧
    (F i (Set.Iio 0) ≠ 0 → FiniteMonopolyPrice (negativeBranch (F i)))

def BranchHalfTail {ι : Type} (F : Marginals ι) : Prop :=
  ∀ i, (F i (Set.Ioi 0) ≠ 0 → HalfTail (positiveBranch (F i))) ∧
    (F i (Set.Iio 0) ≠ 0 → HalfTail (negativeBranch (F i)))

def coreMean (D : Measure ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (if x ≤ t then x else 0) ∂D

def cappedMean (D : Measure ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (min x t) ∂D

def tailProbability (D : Measure ℝ) (t : ℝ) : ℝ≥0∞ := D (Set.Ioi t)

def bundleRevenue {ι : Type} [Fintype ι] (F : Marginals ι) : ℝ≥0∞ :=
  ⨆ (p : ℝ) (_ : 0 ≤ p), ENNReal.ofReal p * productLaw F {v | p ≤ ∑ i, v i}

end IndependentInfoPricing.Main


