-- Prove2me | Definitions.Def_HotSpots
-- name    : HotSpots
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:14.644143+00:00
-- url     : https://prove2.me/theorems/29375836-b93d-40ee-b15c-f04e6d8d6a18
-- statement:
--   This block sets up the framework for a hot-spots-type statement for the Neumann Laplacian on planar domains, in the namespace StrictHotSpots. Plane is two-dimensional Euclidean space. SmoothBoundary(Ω) says that every boundary point p has an open neighborhood U and a C^∞ function ρ on U with ρ(p)=0 and nonzero derivative at p, such that Ω∩U is exactly {ρ<0}∩U. AdmissibleDomain(Ω) requires Ω to be nonempty, open, bounded, simply connected and to have smooth boundary in this sense. HasH1Gradient(Ω,v,g) says that v and the vector field g are square-integrable on Ω and g is the weak gradient of v: for every smooth compactly supported test function φ whose support lies in Ω and every direction e, the integral over Ω of v times the directional derivative of φ equals minus the integral of ⟨g,e⟩φ; this encodes membership of v in H¹(Ω) without boundary conditions. rayleighValues(Ω) is the set of Rayleigh quotients ∫‖g‖²/∫v² over all such pairs with ∫v=0 and ∫v²>0, and firstPositiveNeumannValue(Ω) is its infimum, the first positive Neumann eigenvalue. InFirstNeumannEigenspace(Ω,u) says that u is C^∞ on the closure of Ω, has its gradient as weak H¹ gradient, has mean zero, and satisfies the weak Neumann eigenvalue equation: for every H¹ pair (v,g), ∫⟨∇u,g⟩ equals the first eigenvalue times ∫uv. MainConclusion(Ω,u) is the defined proposition that ∇u is nonzero at every point of Ω and that, for every x in Ω, u(x) lies strictly between the infimum and supremum of u over the boundary of Ω, so no interior critical points or extrema occur. These are definitions of predicates only, with no theorem asserted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/HotSpots.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/HotSpots.lean; bytes 16..1862
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace StrictHotSpots

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def SmoothBoundary (Ω : Set Plane) : Prop :=
  ∀ p ∈ frontier Ω, ∃ (U : Set Plane) (ρ : Plane → ℝ),
    IsOpen U ∧ p ∈ U ∧ ContDiffOn ℝ ∞ ρ U ∧
    fderiv ℝ ρ p ≠ 0 ∧ ρ p = 0 ∧
    Ω ∩ U = {x | ρ x < 0} ∩ U

def AdmissibleDomain (Ω : Set Plane) : Prop :=
  Ω.Nonempty ∧ IsOpen Ω ∧ Bornology.IsBounded Ω ∧
    IsSimplyConnected Ω ∧ SmoothBoundary Ω

def HasH1Gradient (Ω : Set Plane) (v : Plane → ℝ) (g : Plane → Plane) : Prop :=
  MemLp v 2 (volume.restrict Ω) ∧ MemLp g 2 (volume.restrict Ω) ∧
  ∀ φ : Plane → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    ∀ e : Plane,
      (∫ x in Ω, v x * (fderiv ℝ φ x) e) =
        -(∫ x in Ω, (inner ℝ (g x) e) * φ x)

def rayleighValues (Ω : Set Plane) : Set ℝ :=
  {r | ∃ (v : Plane → ℝ) (g : Plane → Plane),
    HasH1Gradient Ω v g ∧ (∫ x in Ω, v x) = 0 ∧
    0 < (∫ x in Ω, (v x) ^ 2) ∧
    r = (∫ x in Ω, ‖g x‖ ^ 2) / (∫ x in Ω, (v x) ^ 2)}

def firstPositiveNeumannValue (Ω : Set Plane) : ℝ := sInf (rayleighValues Ω)

def InFirstNeumannEigenspace (Ω : Set Plane) (u : Plane → ℝ) : Prop :=
  ContDiffOn ℝ ∞ u (closure Ω) ∧ HasH1Gradient Ω u (gradient u) ∧
    (∫ x in Ω, u x) = 0 ∧
    ∀ (v : Plane → ℝ) (g : Plane → Plane), HasH1Gradient Ω v g →
      (∫ x in Ω, inner ℝ (gradient u x) (g x)) =
        firstPositiveNeumannValue Ω * (∫ x in Ω, u x * v x)

def MainConclusion (Ω : Set Plane) (u : Plane → ℝ) : Prop :=
  (∀ x ∈ Ω, gradient u x ≠ 0) ∧
    ∀ x ∈ Ω, sInf (u '' frontier Ω) < u x ∧ u x < sSup (u '' frontier Ω)



end StrictHotSpots
end
end OAI


