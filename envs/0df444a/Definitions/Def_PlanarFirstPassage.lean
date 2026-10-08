-- Prove2me | Definitions.Def_PlanarFirstPassage
-- name    : PlanarFirstPassage
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:04.107667+00:00
-- url     : https://prove2.me/theorems/4e3faed7-37cb-424e-b0c0-87dff6cd35ab
-- statement:
--   This block sets up planar first-passage percolation on the square lattice ℤ². A vertex is a pair of integers, and an edge is a vertex p paired with a Boolean: false denotes the horizontal edge from p to p+(1,0) and true the vertical edge from p to p+(0,1). A Step is east, west, north or south, with the corresponding unit displacement, and Step.edge(p) gives the edge crossed when stepping from p in that direction (west and south use the edge based at the neighbouring vertex). The displacement of a list of steps is the sum of its unit displacements, and pathCost for an edge-weight function τ is the sum of the weights of the edges crossed along the path from p. passageTime(τ,p,q) is the infimum, over all step lists from p ending at q, of their costs. Plane is ℝ² with Euclidean structure, and latticeFloor takes coordinatewise integer parts. TimeConstantNorm(μ) is a structure asserting that μ: Plane → ℝ is nonnegative, vanishes exactly at 0, is subadditive, and satisfies μ(av)=|a|μ(v) for all real a. ExponentialEnvironment(P,τ) says P is a probability measure and the family of random edge weights τ(e) is measurable, independent across edges, and each has the exponential distribution of rate 1. IsTimeConstant(P,τ,μ) says that for each v in the plane, almost surely, passageTime from (0,0) to latticeFloor(tv), divided by t, converges to μ(v) as real t tends to infinity. Further defined regularity properties of μ are: Fréchet differentiability at every nonzero point; every point v with μ(v)=1 having a unique continuous linear functional ℓ with ℓ(v)=1 and ℓ≤μ everywhere; a local C¹ description of the unit level set {μ=1} as the zero set of a C¹ function whose derivative is nonzero there; and HasC1CurveChart(S,v), meaning that near v the set S is parametrized by a C¹ curve γ: ℝ → S with nowhere-vanishing derivative, together with a continuous inverse coordinate θ on an open neighbourhood U of v satisfying θ(γ(t))=t and γ(θ(z))=z for z in S∩U. These are definitions only, with no theorem asserted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PlanarFirstPassage.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PlanarFirstPassage.lean; bytes 424..3261
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.Basic

namespace OAI

namespace PlanarFPP

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

abbrev Vertex := ℤ × ℤ

abbrev Edge := Vertex × Bool

inductive Step where
  | east | west | north | south
  deriving DecidableEq

def Step.delta : Step → Vertex
  | .east => (1, 0)
  | .west => (-1, 0)
  | .north => (0, 1)
  | .south => (0, -1)

def Step.edge (p : Vertex) : Step → Edge
  | .east => (p, false)
  | .west => (p + (-1, 0), false)
  | .north => (p, true)
  | .south => (p + (0, -1), true)

def displacement (ds : List Step) : Vertex := (ds.map Step.delta).sum

def pathCost (τ : Edge → ℝ) (p : Vertex) : List Step → ℝ
  | [] => 0
  | d :: ds => τ (d.edge p) + pathCost τ (p + d.delta) ds

abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable def latticeFloor (v : Plane) : Vertex := (⌊v 0⌋, ⌊v 1⌋)

noncomputable def passageTime (τ : Edge → ℝ) (p q : Vertex) : ℝ :=
  sInf {t | ∃ ds : List Step, p + displacement ds = q ∧ pathCost τ p ds = t}

structure TimeConstantNorm (μ : Plane → ℝ) : Prop where
  nonneg : ∀ v, 0 ≤ μ v
  zero_iff : ∀ v, μ v = 0 ↔ v = 0
  triangle : ∀ v w, μ (v + w) ≤ μ v + μ w
  homogeneous : ∀ (a : ℝ) v, μ (a • v) = |a| * μ v

structure ExponentialEnvironment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (τ : Edge → Ω → ℝ) : Prop where
  probability : IsProbabilityMeasure P
  measurable : ∀ e, Measurable (τ e)
  independent : iIndepFun τ P
  marginal : ∀ e, Measure.map (τ e) P = expMeasure 1

def IsTimeConstant {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (τ : Edge → Ω → ℝ) (μ : Plane → ℝ) : Prop :=
  ∀ v : Plane, ∀ᵐ ω ∂P,
    Tendsto (fun t : ℝ => passageTime (fun e => τ e ω) (0, 0)
      (latticeFloor (t • v)) / t) atTop (𝓝 (μ v))

def DifferentiableAwayFromOrigin (μ : Plane → ℝ) : Prop :=
  ∀ v : Plane, v ≠ 0 → ∃ ℓ : Plane →L[ℝ] ℝ, HasFDerivAt μ ℓ v

def UniqueNormalizedSupports (μ : Plane → ℝ) : Prop :=
  ∀ v : Plane, μ v = 1 → ∃! ℓ : Plane →L[ℝ] ℝ,
    ℓ v = 1 ∧ ∀ w, ℓ w ≤ μ w

def C1UnitSphere (μ : Plane → ℝ) : Prop :=
  ∀ v : Plane, μ v = 1 → ∃ U : Set Plane, IsOpen U ∧ v ∈ U ∧
    ∃ g : Plane → ℝ, ContDiffOn ℝ 1 g U ∧
      (∀ w ∈ U, μ w = 1 ↔ g w = 0) ∧
      ∀ w ∈ U, g w = 0 → ∃ ℓ : Plane →L[ℝ] ℝ,
        HasFDerivAt g ℓ w ∧ ℓ ≠ 0

def HasC1CurveChart (S : Set Plane) (v : Plane) : Prop :=
  ∃ U : Set Plane, IsOpen U ∧ v ∈ U ∧ v ∈ S ∧ ∃ γ : ℝ → Plane, ∃ θ : Plane → ℝ,
    ContDiff ℝ 1 γ ∧ ContinuousOn θ U ∧
    (∀ t, γ t ∈ S ∩ U) ∧ (∀ t, θ (γ t)=t) ∧
    (∀ z ∈ S ∩ U, γ (θ z)=z) ∧
    (∀ t, ∃ d : Plane, HasDerivAt γ d t ∧ d ≠ 0)



end PlanarFPP
end OAI


