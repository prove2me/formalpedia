-- Prove2me | Definitions.Def_ContinuousCircleWeight
-- name    : ContinuousCircleWeight
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:05.165742+00:00
-- url     : https://prove2.me/theorems/39884cfd-ac5b-45f2-8202-0c55cfa33282
-- statement:
--   Let X = ℝ/ℤ, identified homeomorphically with the complex unit circle, and let H = ℓ²(ℤ × ℤ; ℂ). Operators are bounded complex-linear maps on H. A continuous real function f on X is transferred to the unit circle and extended by zero elsewhere in ℂ for use in continuous functional calculus. The extended nonnegative function negativeLog(t) equals ∞ at t = 0 and max(−log t, 0) otherwise. Unitaries U and V together with e ∈ H form a tracial rotation of parameter θ if VU = exp(2πiθ)UV, the moments ⟨e, UᵐVⁿe⟩ equal 1 when m = n = 0 and 0 otherwise for all integers m,n, and the complex linear span of all UᵐVⁿe is dense in H. The rotation algebra is the double commutant of {U,V} within these operators, and the weighted rotation associated to f is T = Uf(V). MainStatement is the defined proposition that there exist an irrational θ with 0 < θ < 1, a tracial rotation (U,V,e), and continuous f : X → ℝ such that 0 ≤ f ≤ 1, f vanishes at exactly one point, and the integral of negativeLog(f) against the circle volume measure is infinite, while every orthogonal projection p in the rotation algebra satisfying (1 − p)Tp = 0 is either 0 or 1. Thus this last requirement excludes every nontrivial T-invariant closed subspace whose orthogonal projection belongs to that algebra.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ContinuousCircleWeight.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ContinuousCircleWeight.lean; bytes 16..1988
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal ComplexInnerProductSpace
namespace ContinuousCircleWeight

abbrev CircleX := AddCircle (1:ℝ)

abbrev TracialHilbert := lp (fun _ : ℤ × ℤ => ℂ) 2
abbrev Operator := TracialHilbert →L[ℂ] TracialHilbert

def circleIdentification : CircleX ≃ₜ Circle :=
  AddCircle.homeomorphCircle (by norm_num)
def circleFunction (f : C(CircleX, ℝ)) (z : ℂ) : ℂ :=
  if hz : ‖z‖ = 1 then f (circleIdentification.symm ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩) else 0

def negativeLog (t : ℝ) : ℝ≥0∞ :=
  if t = 0 then ∞ else ENNReal.ofReal (-Real.log t)

structure IsTracialRotation (θ : ℝ) (U V : unitary Operator)
    (e : TracialHilbert) : Prop where
  relation : (V : Operator) * (U : Operator) =
    Complex.exp (2 * Real.pi * θ * Complex.I) • ((U : Operator) * (V : Operator))
  moments : ∀ m n : ℤ,
    inner ℂ e (((U ^ m * V ^ n : unitary Operator) : Operator) e) =
      if m = 0 ∧ n = 0 then 1 else 0
  cyclic : (Submodule.span ℂ
    (Set.range (fun mn : ℤ × ℤ =>
      ((U ^ mn.1 * V ^ mn.2 : unitary Operator) : Operator) e))).topologicalClosure = ⊤

def rotationAlgebra (U V : unitary Operator) : Set Operator :=
  Set.centralizer (Set.centralizer ({(U : Operator), (V : Operator)} : Set Operator))

def weightedRotation (U V : unitary Operator) (f : C(CircleX, ℝ)) : Operator :=
  (U : Operator) * cfc (circleFunction f) (V : Operator)

def MainStatement : Prop :=
  ∃ (θ : ℝ) (f : C(CircleX, ℝ)) (U V : unitary Operator) (e : TracialHilbert),
    0 < θ ∧ θ < 1 ∧ Irrational θ ∧
    IsTracialRotation θ U V e ∧
    (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
    (∃ z : CircleX, ∀ x, f x = 0 ↔ x = z) ∧
    (∫⁻ x, negativeLog (f x) ∂(volume : Measure CircleX)) = ∞ ∧
    ∀ p : Operator, p ∈ rotationAlgebra U V → IsStarProjection p →
      (1 - p) * weightedRotation U V f * p = 0 → p = 0 ∨ p = 1



end ContinuousCircleWeight
end
end OAI


