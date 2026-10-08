-- Prove2me | Definitions.Def_Brenier
-- name    : Brenier
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:02.671292+00:00
-- url     : https://prove2.me/theorems/530e8a99-0541-4096-91f2-f2a4522f408e
-- statement:
--   For each nonnegative integer d, E(d) is real d-dimensional Euclidean space. The uniform measure on a set S is its restricted Lebesgue measure scaled by the reciprocal of its Lebesgue volume; this definition imposes no positivity or finiteness condition on that volume. A measure is supported in a set C when it assigns zero mass to the complement. A coupling of measures μ and ν is a probability measure on E(d) × E(d) with first marginal μ and second marginal ν. Its quadratic cost is the extended nonnegative integral of ‖x−y‖². The defined Wasserstein distance wasserstein2(μ,ν) is the square root of the real conversion of the infimum of these coupling costs; because this conversion sends infinity to zero, the formula also gives zero when the infimum is infinite, including when no coupling exists. The graph plan of T is the pushforward of μ by x ↦ (x,T(x)). A quadratic optimal map T must be measurable, push μ forward to ν, and have graph-plan cost at most that of every coupling. The uniqueness predicate additionally requires every coupling whose cost is at most this graph-plan cost to equal the graph plan, thus expressing uniqueness of the optimal plan. The map distance is the square root of the real integral of ‖T(x)−U(x)‖², without an integrability hypothesis. The cube consists of points with every coordinate in [−1,1]. Having exactly three atoms in C means being a sum of Dirac measures at three distinct points of C with strictly positive extended nonnegative weights summing to one.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Brenier.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/Brenier.lean; bytes 16..2930
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem358

abbrev E (dimension : ℕ) := EuclideanSpace ℝ (Fin dimension)

def uniformMeasure {dimension : ℕ} (source : Set (E dimension)) : Measure (E dimension) :=
  (volume source)⁻¹ • volume.restrict source

def IsSupported {dimension : ℕ} (measure : Measure (E dimension))
    (container : Set (E dimension)) : Prop :=
  measure (containerᶜ) = 0

def IsCoupling {dimension : ℕ} (source target : Measure (E dimension))
    (plan : Measure (E dimension × E dimension)) : Prop :=
  IsProbabilityMeasure plan ∧
    Measure.map Prod.fst plan = source ∧
    Measure.map Prod.snd plan = target

def quadraticPlanCost {dimension : ℕ} (plan : Measure (E dimension × E dimension)) :
    ℝ≥0∞ :=
  ∫⁻ pair, ENNReal.ofReal (‖pair.1 - pair.2‖ ^ 2) ∂plan

def wasserstein2 {dimension : ℕ} (source target : Measure (E dimension)) : ℝ :=
  Real.sqrt
    (ENNReal.toReal
      (sInf {cost : ℝ≥0∞ |
        ∃ plan : Measure (E dimension × E dimension),
          IsCoupling source target plan ∧ quadraticPlanCost plan = cost}))

def graphPlan {dimension : ℕ} (source : Measure (E dimension))
    (transport : E dimension → E dimension) : Measure (E dimension × E dimension) :=
  Measure.map (fun point => (point, transport point)) source

def IsQuadraticOptimalMap {dimension : ℕ} (source target : Measure (E dimension))
    (transport : E dimension → E dimension) : Prop :=
  Measurable transport ∧
    Measure.map transport source = target ∧
    ∀ plan : Measure (E dimension × E dimension),
      IsCoupling source target plan →
        quadraticPlanCost (graphPlan source transport) ≤ quadraticPlanCost plan

def IsUniqueQuadraticOptimalMap {dimension : ℕ} (source target : Measure (E dimension))
    (transport : E dimension → E dimension) : Prop :=
  IsQuadraticOptimalMap source target transport ∧
    ∀ plan : Measure (E dimension × E dimension),
      IsCoupling source target plan →
        quadraticPlanCost plan ≤ quadraticPlanCost (graphPlan source transport) →
          plan = graphPlan source transport

def mapL2Dist {dimension : ℕ} (source : Measure (E dimension))
    (first second : E dimension → E dimension) : ℝ :=
  Real.sqrt (∫ point, ‖first point - second point‖ ^ 2 ∂source)

def cube (dimension : ℕ) : Set (E dimension) :=
  {point | ∀ index, |point index| ≤ 1}

def HasExactlyThreeAtoms {dimension : ℕ} (measure : Measure (E dimension))
    (container : Set (E dimension)) : Prop :=
  ∃ atoms : Fin 3 → E dimension, Function.Injective atoms ∧
    (∀ index, atoms index ∈ container) ∧
    ∃ weights : Fin 3 → ℝ≥0∞, (∀ index, 0 < weights index) ∧
      (∑ index, weights index) = 1 ∧
      measure = ∑ index, weights index • Measure.dirac (atoms index)



end Problem358
end
end OAI


