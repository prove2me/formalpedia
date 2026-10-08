-- Prove2me | Definitions.Def_CoulombCounterexample
-- name    : CoulombCounterexample
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:05.679199+00:00
-- url     : https://prove2.me/theorems/ddab18d9-7e6d-47ce-8943-e8a42777ee39
-- statement:
--   In three-dimensional real Euclidean space, the Coulomb cost of a triple (x₁,x₂,x₃) is the sum of the three reciprocal pairwise distances, valued in the extended nonnegative reals, with coincident points contributing infinity. A three-coupling of a measure μ is a probability measure on triples whose three coordinate marginals all equal μ. The Kantorovich value K(μ) is the infimum of the integrals of this cost over such couplings. A map preserves μ when it is measurable and its pushforward of μ equals μ. For two such maps T₂ and T₃, their graph cost is the integral of the Coulomb cost of (x,T₂(x),T₃(x)) against μ; the Monge value M(μ) is the infimum over all these pairs of maps. For a real function ρ, its density measure is Lebesgue measure weighted by max(ρ,0). A smooth compact probability density means that ρ is nonnegative, both ρ and √ρ are infinitely differentiable and compactly supported, and the Lebesgue integral of ρ is one. Kantorovich attainment means that a three-coupling has cost exactly K(μ). The absence of a Monge optimizer is defined by the strict inequality K(μ) < graph cost for every pair of preserving maps. Finite Monge approximation means that, for every real ε > 0, some pair of preserving maps has finite graph cost at most K(μ)+ε. The defined Coulomb-counterexample proposition for ρ requires the stated density conditions, a probability density measure μ, finite K(μ), Kantorovich attainment, and absence of a Monge optimizer. The full-conclusion proposition additionally requires M(μ)=K(μ) and finite Monge approximation; these are definitions of propositions, not assertions that such a density exists.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoulombCounterexample.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CoulombCounterexample.lean; bytes 16..3010
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

abbrev E3 := EuclideanSpace ℝ (Fin 3)

abbrev Triple := E3 × (E3 × E3)

def tripleFst (t : Triple) : E3 := t.1

def tripleSnd (t : Triple) : E3 := t.2.1

def tripleThd (t : Triple) : E3 := t.2.2

def invDistance (x y : E3) : ℝ≥0∞ :=
  (ENNReal.ofReal ‖x - y‖)⁻¹

def coulombCost (t : Triple) : ℝ≥0∞ :=
  invDistance (tripleFst t) (tripleSnd t) +
    invDistance (tripleFst t) (tripleThd t) +
    invDistance (tripleSnd t) (tripleThd t)

def IsThreeCoupling (mu : Measure E3) (pi : Measure Triple) : Prop :=
  IsProbabilityMeasure pi ∧
    Measure.map tripleFst pi = mu ∧
    Measure.map tripleSnd pi = mu ∧
    Measure.map tripleThd pi = mu

def densityMeasure (rho : E3 → ℝ) : Measure E3 :=
  Measure.withDensity (volume : Measure E3) (fun x => ENNReal.ofReal (rho x))

def Preserves (mu : Measure E3) (T : E3 → E3) : Prop :=
  Measurable T ∧ Measure.map T mu = mu

def graphCost (mu : Measure E3) (T2 T3 : E3 → E3) : ℝ≥0∞ :=
  ∫⁻ x, coulombCost (x, (T2 x, T3 x)) ∂mu

def kantorovichValue (mu : Measure E3) : ℝ≥0∞ :=
  ⨅ (pi : Measure Triple), ⨅ (_h : IsThreeCoupling mu pi),
    ∫⁻ t, coulombCost t ∂pi

def mongeValue (mu : Measure E3) : ℝ≥0∞ :=
  ⨅ (T2 : E3 → E3), ⨅ (T3 : E3 → E3),
    ⨅ (_h2 : Preserves mu T2), ⨅ (_h3 : Preserves mu T3),
      graphCost mu T2 T3

def IsSmoothCompactProbabilityDensity (rho : E3 → ℝ) : Prop :=
  (∀ x, 0 ≤ rho x) ∧
    ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) rho ∧
    HasCompactSupport rho ∧
    ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) (fun x : E3 => Real.sqrt (rho x)) ∧
    HasCompactSupport (fun x : E3 => Real.sqrt (rho x)) ∧
    (∫ x : E3, rho x ∂(volume : Measure E3)) = 1

def KantorovichAttained (mu : Measure E3) : Prop :=
  ∃ pi : Measure Triple,
    IsThreeCoupling mu pi ∧
      (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu

def NoMongeOptimizer (mu : Measure E3) : Prop :=
  ∀ T2 T3 : E3 → E3,
    Preserves mu T2 → Preserves mu T3 →
      kantorovichValue mu < graphCost mu T2 T3

def FiniteMongeApproximation (mu : Measure E3) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ T2 T3 : E3 → E3,
      Preserves mu T2 ∧
      Preserves mu T3 ∧
      graphCost mu T2 T3 < ⊤ ∧
      graphCost mu T2 T3 ≤
        kantorovichValue mu + ENNReal.ofReal epsilon

def HasCoulombCounterexample (rho : E3 → ℝ) : Prop :=
  IsSmoothCompactProbabilityDensity rho ∧
    IsProbabilityMeasure (densityMeasure rho) ∧
    kantorovichValue (densityMeasure rho) < ⊤ ∧
    KantorovichAttained (densityMeasure rho) ∧
    NoMongeOptimizer (densityMeasure rho)

def HasFullCoulombConclusion (rho : E3 → ℝ) : Prop :=
  HasCoulombCounterexample rho ∧
    mongeValue (densityMeasure rho) =
      kantorovichValue (densityMeasure rho) ∧
    FiniteMongeApproximation (densityMeasure rho)



end Problem356
end
end OAI


