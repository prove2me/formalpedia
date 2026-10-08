-- Prove2me | Definitions.Def_LipschitzHilbert
-- name    : LipschitzHilbert
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:17.405254+00:00
-- url     : https://prove2.me/theorems/d12a5bfb-320c-4629-a854-6dd713c92d91
-- statement:
--   This block sets up directional Hilbert transform operators in the Euclidean plane ℝ² and defines a proposition asserting uniform L² bounds for them. For a vector field v, sample(v,t,x) = x − t·v(x) is the point reached from x by moving distance t against v. For a complex-valued f, directionalKernel is t⁻¹ f(sample(v,t,x)); twoSidedTruncation(v,ε,a,f)(x) integrates this kernel over ε≤|t|≤a, that is over [−a,−ε] plus [ε,a], giving a hard-cutoff truncated directional Hilbert transform; shortTransform is the symmetrized version, the integral over [ε,a] of t⁻¹(f(x−t v(x)) − f(x+t v(x))). smoothPrincipalValue(v,a,f)(x) integrates over [0,a] the quotient t⁻¹ g(t), with g(t)=f(sample(v,t,x)) − f(sample(v,−t,x)), after redefining its value at t=0 as the derivative g′(0). ShortHilbertConclusion(a,C), for a real a and nonnegative constant C, is a defined proposition, not an established theorem. It says that for every 1-Lipschitz vector field v on the plane with ‖v(x)‖=1 everywhere, five things hold. First, for every 0<ε<a and every complex Schwartz function f, the L²(volume) norm of the two-sided truncation is at most C times the L² norm of f. Second, the same bound holds for smoothPrincipalValue. Third, a weak-type bound: for every level in (0,∞), the measure of {x : level < |smoothPrincipalValue(x)|} is at most level⁻² (C‖f‖₂)². Fourth, for each 0<ε<a the truncation on Schwartz functions agrees almost everywhere with a continuous ℂ-linear operator on L² of operator norm at most C. Fifth, the principal-value operator likewise extends to such a bounded operator on L² of norm at most C.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/LipschitzHilbert.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/LipschitzHilbert.lean; bytes 16..2778
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

/- Use the normed-field structure on ℂ for real scalar multiplication. -/
attribute [-instance] instCommCStarAlgebraComplex

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LipschitzHilbert

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev DirectionPlane := EuclideanSpace ℝ (Fin 2)

def sample (v : DirectionPlane → DirectionPlane) (t : ℝ) (x : DirectionPlane) :
    DirectionPlane := x - t • v x

/-- The symmetrized form of the hard-truncated directional integral. -/
def shortTransform (v : DirectionPlane → DirectionPlane) (ε a : ℝ)
    (f : DirectionPlane → ℂ) (x : DirectionPlane) : ℂ :=
  ∫ t in ε..a, t⁻¹ • (f (sample v t x) - f (sample v (-t) x))

def directionalKernel (v : DirectionPlane → DirectionPlane)
    (f : DirectionPlane → ℂ) (x : DirectionPlane) (t : ℝ) : ℂ :=
  t⁻¹ • f (sample v t x)

/-- The two hard-cutoff intervals in the directional Hilbert transform. -/
def twoSidedTruncation (v : DirectionPlane → DirectionPlane) (ε a : ℝ)
    (f : DirectionPlane → ℂ) (x : DirectionPlane) : ℂ :=
  (∫ t in -a..-ε, directionalKernel v f x t) +
    ∫ t in ε..a, directionalKernel v f x t

/-- The symmetric quotient extended continuously at zero for smooth inputs. -/
def smoothPrincipalValue (v : DirectionPlane → DirectionPlane) (a : ℝ)
    (f : DirectionPlane → ℂ) (x : DirectionPlane) : ℂ :=
  let g := fun t : ℝ => f (sample v t x)-f (sample v (-t) x)
  ∫ t in (0:ℝ)..a, Function.update (fun t => t⁻¹ • g t) 0 (deriv g 0) t

attribute [instance] instCommCStarAlgebraComplex

def ShortHilbertConclusion (a : ℝ) (C : ℝ≥0) : Prop :=
  ∀ v : Plane → Plane, LipschitzWith 1 v → (∀ x, ‖v x‖=1) →
    (∀ epsilon : ℝ, 0<epsilon → epsilon<a → ∀ f : SchwartzMap Plane ℂ,
      eLpNorm (twoSidedTruncation v epsilon a f) 2 volume≤C*eLpNorm f 2 volume) ∧
    (∀ f : SchwartzMap Plane ℂ,
      eLpNorm (smoothPrincipalValue v a f) 2 volume≤C*eLpNorm f 2 volume) ∧
    (∀ f : SchwartzMap Plane ℂ, ∀ level : ℝ≥0∞, level≠0 → level≠∞ →
      volume {x | level<‖smoothPrincipalValue v a f x‖ₑ}≤
        level⁻¹^2*((C:ℝ≥0∞)*eLpNorm f 2 volume)^2) ∧
    (∀ epsilon : ℝ, 0<epsilon → epsilon<a →
      ∃ T : Lp ℂ 2 (volume : Measure Plane) →L[ℂ] Lp ℂ 2 volume,
        ‖T‖≤C ∧ ∀ f : SchwartzMap Plane ℂ,
          (T (f.toLp 2 volume) : Plane → ℂ)=ᵐ[volume] twoSidedTruncation v epsilon a f) ∧
    (∃ T : Lp ℂ 2 (volume : Measure Plane) →L[ℂ] Lp ℂ 2 volume,
      ‖T‖≤C ∧ ∀ f : SchwartzMap Plane ℂ,
        (T (f.toLp 2 volume) : Plane → ℂ)=ᵐ[volume] smoothPrincipalValue v a f)



end LipschitzHilbert
end
end OAI


