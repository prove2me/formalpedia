-- Prove2me | Definitions.Def_IndependentProducts
-- name    : IndependentProducts
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:14.92804+00:00
-- url     : https://prove2.me/theorems/9deec5af-48b5-4547-ab6e-7ae83e4d8c39
-- statement:
--   The vertices of the tree are finite lists of positive integers, and the edges are the nonroot vertices; a sample is a real-valued function on edges, and productMeasure(μ) is the infinite product law making all edge coordinates independent copies of a real law μ (the multiplier). For a vertex v and position j, pathPrefix is the nonroot prefix of v of length j+1, and pathProduct(v,ω) is the product of the sample values along these prefixes, equal to 1 at the root. productSpan(μ) is the topological closure, in the real L1 space of the product measure, of the linear span of the almost-everywhere classes of all path products. MultiplierHypotheses(μ) requires that μ be a probability measure, almost surely positive, not almost surely constant, of mean 1, and with finite second moment (the identity is in L2). For a real normed space X, CofiniteSubspaces(X) are the closed subspaces F with finite-dimensional quotient X/F. For a seminorm N and t, averagedMidpointModulus is the infimum over x with N(x)=1 of the supremum over cofinite F of the infimum over y in F with N(y)≥1 of (N(x+ty)+N(x−ty))/2 − 1, while oneSidedModulus is the analogous quantity using directions with N(y)=1 and the value N(x+ty) − 1. IsEquivalentNorm(N) says there are constants 0<a≤b with a‖x‖≤N(x)≤b‖x‖ for all x, and IsAUC(N) says oneSidedModulus(N,t)>0 for every t>0. Finally, gaussianTail(r) is the real-valued standard Gaussian probability that |x|≥r, excessConstant(K) is (1/16) times the standard Gaussian expectation of max(|x|−2K,0), exponentialLaw is the measure with density e^{−w} on the positive half-line (expMeasure 1), and gaussianSquareLaw is the law of the square of a standard Gaussian. These are definitions only, with no theorem asserted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/IndependentProducts.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/IndependentProducts.lean; bytes 16..3535
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

universe uX

namespace IndependentProducts

/-- The tree of finite sequences of positive integers. -/
abbrev Vertex := List ℕ+
/-- Coordinates are attached only to nonroot vertices. -/
abbrev Edge := {v : Vertex // v ≠ []}
abbrev Sample := Edge → ℝ

/-- The product law of independent copies of the multiplier. -/
def productMeasure (μ : Measure ℝ) : Measure Sample :=
  Measure.infinitePi (fun _ : Edge => μ)

/-- The nonroot prefix ending at position `j`. -/
def pathPrefix (v : Vertex) (j : Fin v.length) : Edge :=
  ⟨v.take (j.val + 1), by
    intro h
    have hl := congrArg List.length h
    simp only [List.length_take, List.length_nil] at hl
    have := j.isLt
    omega⟩

/-- Root product is the empty product 1; every other product uses the path prefixes. -/
def pathProduct (v : Vertex) (ω : Sample) : ℝ :=
  ∏ j : Fin v.length, ω (pathPrefix v j)

/-- The closed real L1 span of the path products. -/
def productSpan (μ : Measure ℝ) : Submodule ℝ (Lp ℝ 1 (productMeasure μ)) :=
  (Submodule.span ℝ {f : Lp ℝ 1 (productMeasure μ) | ∃ v : Vertex,
    (f : Sample → ℝ) =ᵐ[productMeasure μ] pathProduct v}).topologicalClosure

/-- Positivity, nonconstancy, mean one, and finite second moment of the multiplier law. -/
structure MultiplierHypotheses (μ : Measure ℝ) : Prop where
  probability : IsProbabilityMeasure μ
  positive : ∀ᵐ w ∂μ, 0 < w
  nonconstant : ∀ c : ℝ, ¬ (∀ᵐ w ∂μ, w = c)
  mean_one : ∫ w, w ∂μ = 1
  second_moment : MemLp (fun w : ℝ => w) 2 μ

variable (X : Type uX) [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Closed subspaces of finite codimension, with respect to the inherited topology. -/
def CofiniteSubspaces : Set (Submodule ℝ X) :=
  {F | IsClosed (F : Set X) ∧ FiniteDimensional ℝ (X ⧸ F)}

/-- The averaged asymptotic midpoint modulus, with directions of norm at least 1. -/
def averagedMidpointModulus (N : Seminorm ℝ X) (t : ℝ) : ℝ :=
  sInf {r | ∃ x : X, N x = 1 ∧ r =
    sSup {a | ∃ F ∈ CofiniteSubspaces X, a =
      sInf {b | ∃ y : X, y ∈ F ∧ 1 ≤ N y ∧
        b = (N (x + t • y) + N (x - t • y)) / 2 - 1}}}

/-- The usual one-sided modulus, whose directions have norm exactly 1. -/
def oneSidedModulus (N : Seminorm ℝ X) (t : ℝ) : ℝ :=
  sInf {r | ∃ x : X, N x = 1 ∧ r =
    sSup {a | ∃ F ∈ CofiniteSubspaces X, a =
      sInf {b | ∃ y : X, y ∈ F ∧ N y = 1 ∧ b = N (x + t • y) - 1}}}

/-- A seminorm with these bounds is a genuine norm equivalent to the original norm. -/
def IsEquivalentNorm (N : Seminorm ℝ X) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ x, a * ‖x‖ ≤ N x ∧ N x ≤ b * ‖x‖

def IsAUC (N : Seminorm ℝ X) : Prop := ∀ t : ℝ, 0 < t → 0 < oneSidedModulus X N t

/-- Gaussian-tail probability, in real rather than extended-nonnegative-real notation. -/
def gaussianTail (r : ℝ) : ℝ :=
  (gaussianReal 0 1 {x : ℝ | r ≤ |x|}).toReal

/-- The Gaussian excess constant at threshold twice the parameter. -/
def excessConstant (K : ℝ) : ℝ :=
  (1 / 16 : ℝ) * ∫ x : ℝ, max (|x| - 2 * K) 0 ∂gaussianReal 0 1

/-- The density exp(-w) on the positive half-line. -/
def exponentialLaw : Measure ℝ := expMeasure 1

/-- The law of the square of a standard real Gaussian. -/
def gaussianSquareLaw : Measure ℝ := (gaussianReal 0 1).map (fun x : ℝ => x ^ 2)



end IndependentProducts
end
end OAI


