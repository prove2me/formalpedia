-- Prove2me | Definitions.Def_TamingCompatibility
-- name    : TamingCompatibility
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:29.118121+00:00
-- url     : https://prove2.me/theorems/de87d160-c0bf-45d1-9cd9-9f42ff11a478
-- statement:
--   Working on ℝ⁴ (Space is 4-dimensional Euclidean space with its standard model with corners), X is a smooth manifold charted over this space, and a TwoForm on X assigns to each point x an alternating continuous real-linear 2-form on the tangent space at x, with no regularity imposed a priori. An AlmostComplexStructure on X is a family of continuous linear endomorphisms J_x of the tangent spaces satisfying J_x(J_x v) = −v for all x and v, and whose induced map on the tangent bundle, sending (x,v) to (x,J_x v), is smooth (C^∞). The evaluation eval(α,x,u,v) is α_x(u,v). The pullback of α along a map f from ℝ⁴ to X sends y to α_{f(y)} composed with the manifold derivative of f at y. A form α IsSmooth if, for every open U ⊆ ℝ⁴ and every f that is smooth on U, the pullback of α along f is C^∞ on U. It IsClosed if for every such U and f, the exterior derivative of the pullback within U vanishes at every point of U. It IsNondegenerate if every tangent vector v with α_x(v,w)=0 for all w must be zero. IsSymplectic means smooth, closed and nondegenerate together. For an almost complex structure J, α Tames J if α_x(v, J_x v) > 0 for every x and every nonzero v; J IsInvariant for α if α_x(J_x u, J_x v) = α_x(u,v) for all x, u, v; and Compatible means both taming and invariance hold. Note that taming, invariance and compatibility are defined for arbitrary two-forms, without requiring α to be symplectic.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TamingCompatibility.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TamingCompatibility.lean; bytes 16..2074
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open scoped Manifold ContDiff

namespace TamingCompatibility

abbrev Space := EuclideanSpace ℝ (Fin 4)
abbrev Model := 𝓘(ℝ, Space)

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

abbrev TwoForm (X : Type*) [TopologicalSpace X] [ChartedSpace Space X] :=
  (x : X) → (TangentSpace Model x) [⋀^Fin 2]→L[ℝ] ℝ

structure AlmostComplexStructure (X : Type*) [TopologicalSpace X]
    [ChartedSpace Space X] [IsManifold Model ∞ X] where
  endomorphism : (x : X) → TangentSpace Model x →L[ℝ] TangentSpace Model x
  square : ∀ x v, endomorphism x (endomorphism x v) = -v
  smooth : ContMDiff Model.tangent Model.tangent ∞
    (fun p : TangentBundle Model X =>
      (⟨p.proj, endomorphism p.proj p.2⟩ : TangentBundle Model X))

def eval (α : TwoForm X) (x : X) (u v : TangentSpace Model x) : ℝ :=
  α x ![u, v]

noncomputable def pullback (α : TwoForm X) (f : Space → X) :
    Space → Space [⋀^Fin 2]→L[ℝ] ℝ :=
  fun y => (α (f y)).compContinuousLinearMap (mfderiv Model Model f y)

def IsSmooth (α : TwoForm X) : Prop :=
  ∀ (f : Space → X) (U : Set Space), IsOpen U →
    ContMDiffOn Model Model ∞ f U → ContDiffOn ℝ ∞ (pullback α f) U

def IsClosed (α : TwoForm X) : Prop :=
  ∀ (f : Space → X) (U : Set Space), IsOpen U →
    ContMDiffOn Model Model ∞ f U → ∀ y ∈ U,
      extDerivWithin (pullback α f) U y = 0

def IsNondegenerate (α : TwoForm X) : Prop :=
  ∀ x v, (∀ w, eval α x v w = 0) → v = 0

def IsSymplectic (α : TwoForm X) : Prop :=
  IsSmooth α ∧ IsClosed α ∧ IsNondegenerate α

def Tames (α : TwoForm X) (J : AlmostComplexStructure X) : Prop :=
  ∀ x v, v ≠ 0 → 0 < eval α x v (J.endomorphism x v)

def IsInvariant (α : TwoForm X) (J : AlmostComplexStructure X) : Prop :=
  ∀ x u v, eval α x (J.endomorphism x u) (J.endomorphism x v) = eval α x u v

def Compatible (α : TwoForm X) (J : AlmostComplexStructure X) : Prop :=
  Tames α J ∧ IsInvariant α J



end TamingCompatibility
end
end OAI


