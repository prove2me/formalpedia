-- Prove2me | Definitions.Def_WeakMTWGlobalSupport
-- name    : WeakMTWGlobalSupport
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:38.56781+00:00
-- url     : https://prove2.me/theorems/493e8c1b-6d7c-4e0c-96e1-4c9e5f7111a7
-- statement:
--   Work on an n-dimensional smooth Riemannian manifold M, modeled on Euclidean space ℝⁿ, which is also a metric space whose metric is required to be the Riemannian distance. CompleteGeodesicWithInitialData(x,v,γ) says that γ:ℝ→M is smooth, γ(0)=x, its velocity at time 0 is v, and every time t has a neighborhood on which dist(γ(s),γ(r)) = ‖v‖·|s−r|, so γ is a locally distance-realizing curve of constant speed ‖v‖ defined on all of ℝ. ExpEndpoint(x,v,y) means such a γ exists with γ(1)=y, and exp(x,v) is a chosen such endpoint if one exists and is x otherwise. The injectivityDomain at x is the set of tangent vectors v for which some a>1 satisfies dist(x, exp(x,a v)) = a‖v‖. The cost is c(x,y)=dist(x,y)²/2. For v, ξ, η tangent at x, mtw(x,v,ξ,η) is −3/2 times the mixed fourth derivative at the origin of (t,s) ↦ c(exp(x,tξ), exp(x,v+sη)), taken twice in t and twice in s. HasWeakMTW is the defined proposition that mtw(x,v,ξ,η) ≥ 0 for every x, every v in the injectivity domain at x, and all tangent vectors ξ, η at x that are orthogonal for the Riemannian inner product. MainConvexity is the defined proposition that the injectivity domain at every point x is a convex subset of the tangent space at x. Both are defined propositions, not established results.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/WeakMTWGlobalSupport.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/WeakMTWGlobalSupport.lean; bytes 16..2013
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace WeakMTWGlobalSupport

open scoped Manifold ContDiff Topology
open Set Filter Manifold Bundle

namespace WeakMTW

noncomputable section

abbrev Model (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev model (n : ℕ) := 𝓘(ℝ, Model n)

variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M]

def CompleteGeodesicWithInitialData (x : M) (v : TangentSpace (model n) x)
    (γ : ℝ → M) : Prop :=
  ContMDiff 𝓘(ℝ, ℝ) (model n) ∞ γ ∧
  ∃ h : γ 0 = x,
    (h ▸ mfderiv 𝓘(ℝ, ℝ) (model n) γ 0 (1 : ℝ)) = v ∧
    ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ s ∈ Metric.ball t ε, ∀ r ∈ Metric.ball t ε,
        dist (γ s) (γ r) = ‖v‖ * |s - r|

def ExpEndpoint (x : M) (v : TangentSpace (model n) x) (y : M) : Prop :=
  ∃ γ : ℝ → M, CompleteGeodesicWithInitialData x v γ ∧ γ 1 = y

noncomputable def exp (x : M) (v : TangentSpace (model n) x) : M :=
  by
    classical
    exact if h : ∃ y, ExpEndpoint x v y then Classical.choose h else x

def injectivityDomain (x : M) : Set (TangentSpace (model n) x) :=
  {v | ∃ a : ℝ, 1 < a ∧ dist x (exp x (a • v)) = a * ‖v‖}

def cost (x y : M) : ℝ := dist x y ^ 2 / 2

noncomputable def mtw (x : M) (v ξ η : TangentSpace (model n) x) : ℝ :=
  -(3 / 2 : ℝ) * deriv (fun s : ℝ =>
    deriv (fun s' : ℝ => deriv (fun t : ℝ =>
      deriv (fun t' : ℝ => cost (exp x (t' • ξ)) (exp x (v + s' • η))) t) 0) s) 0

def HasWeakMTW : Prop :=
  ∀ (x : M) (v : TangentSpace (model n) x), v ∈ injectivityDomain x →
    ∀ ξ η : TangentSpace (model n) x, inner ℝ ξ η = 0 → 0 ≤ mtw x v ξ η

def MainConvexity : Prop :=
  ∀ x : M, Convex ℝ (injectivityDomain (n := n) x)

end

end WeakMTW



end WeakMTWGlobalSupport
end OAI


