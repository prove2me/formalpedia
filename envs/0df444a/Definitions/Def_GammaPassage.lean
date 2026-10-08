-- Prove2me | Definitions.Def_GammaPassage
-- name    : GammaPassage
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:12.279183+00:00
-- url     : https://prove2.me/theorems/740553f1-8b05-49ce-a61c-a89ac284193a
-- statement:
--   This block sets up nearest-neighbour first-passage percolation on the square lattice ℤ² and defines a target proposition about Gamma-distributed edge times. Vertices are pairs of integers; an edge is a vertex together with a Boolean saying whether it is the horizontal edge to the east (false) or the vertical edge to the north (true). A path is a list of unit steps east, west, north or south; its displacement is the sum of the step vectors, and its cost is the sum of the edge weights τ it traverses. The passage time between two vertices is the infimum of costs over all step lists with that displacement. latticeFloor takes coordinatewise integer parts of a point of the Euclidean plane ℝ². A TimeConstantNorm μ is a function on the plane that is nonnegative, vanishes only at 0, is subadditive, and is absolutely homogeneous, so it is a norm. IsTimeConstant says that for every v, almost surely the passage time from the origin to latticeFloor(tv), divided by t, tends to μ(v) as t→∞. DifferentiableAwayFromOrigin asks for Fréchet differentiability of μ at every nonzero point. An IidEnvironment for a law ν on ℝ consists of a probability measure P and measurable, mutually independent edge times τ_e each with law ν; a GammaEnvironment uses the Gamma law with the given shape and rate. HasC1CurveChart for a set S at v asks for an open neighbourhood U of v with v in S, a C¹ map γ:ℝ→ℝ² with nowhere-zero derivative, and a continuous inverse θ on U, such that γ maps onto S∩U bijectively with inverse θ. GammaDifferentiabilityTarget is a defined proposition, not an established theorem: for every shape>0 and rate>0, every probability space and every Gamma iid environment, there exists a norm μ that is the almost-sure time constant, is differentiable away from the origin, and whose unit-ball boundary, the frontier of {μ≤1}, has a C¹ chart at each of its points. No shape theorem, norm or absence-of-corners assumption is supplied; these are all conclusions.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/GammaPassage.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/GammaPassage.lean; bytes 366..3897
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Distributions.Gamma
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

def IsTimeConstant {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (τ : Edge → Ω → ℝ) (μ : Plane → ℝ) : Prop :=
  ∀ v : Plane, ∀ᵐ ω ∂P,
    Tendsto (fun t : ℝ => passageTime (fun e => τ e ω) (0, 0)
      (latticeFloor (t • v)) / t) atTop (𝓝 (μ v))

def DifferentiableAwayFromOrigin (μ : Plane → ℝ) : Prop :=
  ∀ v : Plane, v ≠ 0 → ∃ ℓ : Plane →L[ℝ] ℝ, HasFDerivAt μ ℓ v

end PlanarFPP

namespace GammaFPP

open Set MeasureTheory ProbabilityTheory PlanarFPP

structure IidEnvironment {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure ℝ) (P : Measure Ω) (τ : PlanarFPP.Edge → Ω → ℝ) : Prop where
  probability : IsProbabilityMeasure P
  measurable : ∀ e, Measurable (τ e)
  independent : iIndepFun τ P
  marginal : ∀ e, Measure.map (τ e) P = ν


abbrev GammaEnvironment {Ω : Type*} [MeasurableSpace Ω]
    (shape rate : ℝ) (P : Measure Ω) (τ : PlanarFPP.Edge → Ω → ℝ) :=
  IidEnvironment (gammaMeasure shape rate) P τ


/-- A regular C¹ parametrization of the curve near a point, with a continuous inverse. -/
def HasC1CurveChart (S : Set Plane) (v : Plane) : Prop :=
  ∃ U : Set Plane, IsOpen U ∧ v ∈ U ∧ v ∈ S ∧ ∃ γ : ℝ → Plane, ∃ θ : Plane → ℝ,
    ContDiff ℝ 1 γ ∧ ContinuousOn θ U ∧
    (∀ t, γ t ∈ S ∩ U) ∧ (∀ t, θ (γ t)=t) ∧
    (∀ z ∈ S ∩ U, γ (θ z)=z) ∧
    (∀ t, ∃ d : Plane, HasDerivAt γ d t ∧ d ≠ 0)

/-- The Gamma theorem: an actual deterministic passage-time limit norm exists
for every positive shape and rate and every iid environment with that law.
Its Frechet differentiability and literal unit-ball boundary charts are
conclusions. No shape theorem, norm, or no-corner hypothesis is supplied. -/
def GammaDifferentiabilityTarget : Prop :=
  ∀ (shape rate : ℝ), 0 < shape → 0 < rate →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (τ : PlanarFPP.Edge → Ω → ℝ),
      GammaEnvironment shape rate P τ →
        ∃ μ : Plane → ℝ,
          TimeConstantNorm μ ∧ IsTimeConstant P τ μ ∧
          DifferentiableAwayFromOrigin μ ∧
          ∀ v ∈ frontier {z : Plane | μ z ≤ 1},
            HasC1CurveChart (frontier {z : Plane | μ z ≤ 1}) v



end GammaFPP
end OAI


