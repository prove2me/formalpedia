-- Prove2me | Definitions.Def_BalancedBoxRouting
-- name    : BalancedBoxRouting
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:00.840364+00:00
-- url     : https://prove2.me/theorems/f3e9dfd7-67c3-43d5-8ddc-f7e9d2711bce
-- statement:
--   In three-dimensional real space, a field U(t,x) assigns a spatial vector to each real time and position. Coordinate directions comprise the time direction and the three spatial directions, and mixed derivatives are iterated Fréchet derivatives in any finite ordered list of these directions, with the empty list giving U itself. A box centered at c with coordinate radii r consists of points satisfying |xⱼ−cⱼ|≤rⱼ for every coordinate; solid boxes use rational centers and radii. For rational vectors a,b,h,k, the prescribed affine map has coordinates bⱼ+(kⱼ/hⱼ)(xⱼ−aⱼ). No positivity of these radii is required in these definitions. Rational numbers are encoded by triples of natural numbers (u,v,w), representing (u−v)/(w+1), and four such codes encode a rational space-time point. A field is Effective if there are computable rational evaluations, a computable natural-valued modulus, and computable natural bounds for every mixed derivative: for each derivative list ds, coded point q, accuracy n≥0, and coordinate j, the evaluation approximates that derivative at every point within distance 1/(modulus(ds,n)+1) of q with error at most 1/(n+1); the bound for ds bounds all its coordinates everywhere. An AdmissibleField is infinitely differentiable, compactly supported in space-time, Effective, spatially divergence-free, and zero outside times [1/4,3/4]. Spatial divergence is the sum of the three matching coordinate partial derivatives. IsGlobalFlow(U,Φ) means that Φ(0,x)=x, each trajectory is differentiable at every real time and satisfies dΦ(t,x)/dt=U(t,Φ(t,x)), and every trajectory with the same initial position satisfying this equation coincides with it for all time. For finite families a,b,h,k of rational vectors, Delivers means that around each source solid box there is an open neighborhood on which the time-one flow equals its prescribed affine map.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BalancedBoxRouting.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BalancedBoxRouting.lean; bytes 16..3188
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open scoped BigOperators ContDiff

namespace BoxTransport.Routing

abbrev Space := Fin 3 → ℝ
abbrev RationalSpace := Fin 3 → ℚ
abbrev SpaceTime := ℝ × Space
abbrev RationalSpaceTime := ℚ × RationalSpace
abbrev Field := SpaceTime → Space

abbrev Axis := Option (Fin 3)

def coordinateVector (j : Fin 3) : Space := Pi.single j 1

def coordinateDirection : Axis → SpaceTime
  | none => (1, 0)
  | some j => (0, coordinateVector j)

def realPoint (q : RationalSpace) : Space := fun j => (q j : ℝ)

def realSpaceTime (q : RationalSpaceTime) : SpaceTime := (q.1, realPoint q.2)

def realBox (c r : Space) : Set Space :=
  {x | ∀ j, |x j - c j| ≤ r j}

def solidBox (a h : RationalSpace) : Set Space :=
  realBox (realPoint a) (realPoint h)

def prescribedAffine (a b h k : RationalSpace) (x : Space) : Space :=
  fun j => (b j : ℝ) + ((k j / h j : ℚ) : ℝ) * (x j - (a j : ℝ))

noncomputable def mixedDerivative : List Axis → Field → Field
  | [], U => U
  | j :: js, U => fun p => fderiv ℝ (mixedDerivative js U) p (coordinateDirection j)

abbrev RationalCode := ℕ × ℕ × ℕ

def rationalValue (q : RationalCode) : ℚ := ((q.1 : ℚ) - q.2.1) / (q.2.2 + 1)

abbrev RationalPointCode := RationalCode × RationalCode × RationalCode × RationalCode

def codeSpaceTime (q : RationalPointCode) : SpaceTime :=
  ((rationalValue q.1 : ℝ), ![(rationalValue q.2.1 : ℝ),
    (rationalValue q.2.2.1 : ℝ), (rationalValue q.2.2.2 : ℝ)])

abbrev EvaluationRequest := List Axis × RationalPointCode × ℕ × Fin 3

def Effective (U : Field) : Prop :=
  ∃ eval : EvaluationRequest → RationalCode,
    ∃ modulus : List Axis × ℕ → ℕ,
      ∃ bound : List Axis → ℕ,
        Computable eval ∧ Computable modulus ∧ Computable bound ∧
        (∀ (ds : List Axis) (q : RationalPointCode) (n : ℕ) (p : SpaceTime),
          ‖p - codeSpaceTime q‖ ≤ ((modulus (ds, n) : ℝ) + 1)⁻¹ →
          ∀ j : Fin 3,
            |mixedDerivative ds U p j - (rationalValue (eval (ds, q, n, j)) : ℝ)| ≤
              ((n : ℝ) + 1)⁻¹) ∧
        (∀ (ds : List Axis) (p : SpaceTime) (j : Fin 3),
          |mixedDerivative ds U p j| ≤ (bound ds : ℝ))

noncomputable def spatialDivergence (U : Field) (t : ℝ) (x : Space) : ℝ :=
  ∑ j : Fin 3, (fderiv ℝ (fun y => U (t, y)) x (coordinateVector j)) j

def AdmissibleField (U : Field) : Prop :=
  ContDiff ℝ ∞ U ∧ HasCompactSupport U ∧ Effective U ∧
    (∀ t x, spatialDivergence U t x = 0) ∧
    (∀ (t : ℝ) (x : Space), t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) → U (t, x) = 0)

def IsGlobalFlow (U : Field) (Φ : ℝ → Space → Space) : Prop :=
  (∀ x, Φ 0 x = x) ∧
    (∀ t x, HasDerivAt (fun s => Φ s x) (U (t, Φ t x)) t) ∧
    (∀ (x : Space) (γ : ℝ → Space), γ 0 = x →
      (∀ t, HasDerivAt γ (U (t, γ t)) t) → ∀ t, γ t = Φ t x)

def Delivers {n : ℕ} (a b h k : Fin n → RationalSpace)
    (Φ : ℝ → Space → Space) : Prop :=
  ∀ i, ∃ O : Set Space, IsOpen O ∧ solidBox (a i) (h i) ⊆ O ∧
    ∀ x ∈ O, Φ 1 x = prescribedAffine (a i) (b i) (h i) (k i) x



end BoxTransport.Routing
end OAI


