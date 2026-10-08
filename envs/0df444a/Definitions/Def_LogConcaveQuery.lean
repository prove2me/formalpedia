-- Prove2me | Definitions.Def_LogConcaveQuery
-- name    : LogConcaveQuery
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:17.786836+00:00
-- url     : https://prove2.me/theorems/83a67880-65dd-4f51-abaa-153a5dd62ca7
-- statement:
--   In dimension d, points are vectors in Euclidean space R^d, a reply is a pair (real number, point), and a transcript of q replies is a function from Fin q to replies. A potential V is Admissible if it is twice continuously differentiable, satisfies V(0)=0 and gradient V(0)=0, and its Hessian is sandwiched between the identity and twice the identity: |v|^2 ≤ ⟨v, Hess V(x) v⟩ ≤ 2|v|^2 for all x and v. The Gibbs measure of V is the probability law with density proportional to exp(−V) with respect to Lebesgue measure, normalized by the partition function (the lower integral of exp(−V)). TVAtMost(μ,ν,ε) says |μ(s)−ν(s)| ≤ ε for every measurable set s. A first-order oracle replies to a query x with the pair (V(x), ∇V(x)). An OracleAlgorithm with private randomness space Ω makes q adaptive queries, where the ith query is a measurable function of the randomness and the transcript, and then outputs a point by a measurable function of the randomness and the final transcript; its history fills in oracle replies one query at a time, and run gives the output. CanSample(d,q) is the defined proposition that there exist a probability space Ω and a q-query algorithm such that, for every admissible V, the output is measurable and the law of the output is within total variation 1/10 of the Gibbs measure of V. queryComplexity(d) is the least q with CanSample(d,q), as an extended natural number (infinity if none exists). ExponentBound(γ) means γ ≥ 0 and, for every ε>0, queryComplexity(d) ≤ d^(γ+ε) for all sufficiently large d. Finally gammaStar is the infimum of all γ satisfying ExponentBound. These are definitions only; no value or bound for gammaStar is asserted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/LogConcaveQuery.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/LogConcaveQuery.lean; bytes 16..3314
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace LogConcaveSampling

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Reply (d : ℕ) := ℝ × Point d
abbrev Transcript (d q : ℕ) := Fin q → Reply d

/-- Normalized twice continuously differentiable potentials with Hessian between the identity and twice the identity. -/
structure Admissible {d : ℕ} (V : Point d → ℝ) : Prop where
  smooth : ContDiff ℝ 2 V
  value_zero : V 0 = 0
  gradient_zero : gradient V 0 = 0
  hessian_bounds : ∀ x v : Point d,
    ‖v‖ ^ 2 ≤ inner ℝ v (fderiv ℝ (gradient V) x v) ∧
    inner ℝ v (fderiv ℝ (gradient V) x v) ≤ 2 * ‖v‖ ^ 2

/-- The unnormalized Gibbs density relative to Euclidean volume. -/
def gibbsDensity {d : ℕ} (V : Point d → ℝ) (x : Point d) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-V x))

def partition {d : ℕ} (V : Point d → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, gibbsDensity V x ∂volume

/-- The Gibbs probability law, normalized by its partition function. -/
def gibbs {d : ℕ} (V : Point d → ℝ) : Measure (Point d) :=
  (partition V)⁻¹ • volume.withDensity (gibbsDensity V)

def TVAtMost {E : Type*} [MeasurableSpace E]
    (μ ν : Measure E) (ε : ℝ) : Prop :=
  ∀ s : Set E, MeasurableSet s → |μ.real s - ν.real s| ≤ ε

def firstOrderReply {d : ℕ} (V : Point d → ℝ) (x : Point d) : Reply d :=
  (V x, gradient V x)

/-- Measurable adaptive queries and output, parametrized by private randomness. -/
structure OracleAlgorithm (Ω : Type*) [MeasurableSpace Ω] (d q : ℕ) where
  query : Fin q → Ω × Transcript d q → Point d
  query_measurable : ∀ i, Measurable (query i)
  output : Ω × Transcript d q → Point d
  output_measurable : Measurable output

def OracleAlgorithm.history {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (V : Point d → ℝ) (ω : Ω) : ℕ → Transcript d q
  | 0 => 0
  | n + 1 =>
      let h := A.history V ω n
      if hn : n < q then
        Function.update h ⟨n, hn⟩ (firstOrderReply V (A.query ⟨n, hn⟩ (ω, h)))
      else h

def OracleAlgorithm.run {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) (V : Point d → ℝ) (ω : Ω) : Point d :=
  A.output (ω, A.history V ω q)

/-- A uniform sampler with a deterministic query budget on every execution and total-variation error at most one tenth. -/
def CanSample (d q : ℕ) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
    (_ : IsProbabilityMeasure μ) (A : OracleAlgorithm Ω d q),
    ∀ V : Point d → ℝ, Admissible V →
      Measurable (A.run V) ∧ TVAtMost (μ.map (A.run V)) (gibbs V) (1 / 10)

/-- The smallest feasible integer query budget, or infinity when no budget is feasible. -/
def queryComplexity (d : ℕ) : ℕ∞ :=
  sInf ((fun q : ℕ => (q : ℕ∞)) '' {q | CanSample d q})

/-- The quantified dimension-exponent upper bound with every positive exponent slack. -/
def ExponentBound (γ : ℝ) : Prop :=
  0 ≤ γ ∧ ∀ ε : ℝ, 0 < ε → ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    (queryComplexity d).toENNReal ≤ ENNReal.ofReal ((d : ℝ) ^ (γ + ε))

def gammaStar : ℝ := sInf {γ : ℝ | ExponentBound γ}



end LogConcaveSampling
end
end OAI


