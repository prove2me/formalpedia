-- Prove2me | Definitions.Def_DaugavetModuli
-- name    : DaugavetModuli
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:06.91645+00:00
-- url     : https://prove2.me/theorems/93ac2406-8bc7-4bfb-afe5-e00b1b5aed83
-- statement:
--   For a real normed space X, a cofinite subspace is a closed linear subspace F with finite-dimensional quotient X/F. Given a seminorm N, define A(x,t,y) = (N(x+ty)+N(x−ty))/2−1. The quantity H(N,x,t) is the supremum, over cofinite F, of the infimum of A(x,t,y) over y∈F with N(y)≥1; D(N,x,t) instead uses the infimum of N(x+ty)−1 over y∈F with N(y)=1. The averaged and one-sided moduli are respectively the infima of H(N,x,t) and D(N,x,t) over x with N(x)=1. These are real infima and suprema. EquivalentNorm means that positive constants a,b satisfy a‖x‖≤N(x)≤b‖x‖ for every x. AUC is the proposition that the one-sided modulus is positive for every t>0. The Daugavet property requires ‖I+T‖=1+‖T‖ for every operator T(x)=ℓ(x)v, where ℓ is a continuous real linear functional and v∈X. For real L¹(μ) classes f,g, measureDistance is the real infimum of all a>0 satisfying μ.real({ω: |f(ω)−g(ω)|>a})<a, where μ.real is the real-valued conversion of the measure. MeasurePrecompactBall(E) means that, for every ε>0, finitely many centers in the ambient L¹(μ) space cover the whole closed unit ball of a linear subspace E within measureDistance less than ε. UnitSliceProperty requires that, for every unit vector w, continuous linear functional ℓ, and real α for which some u with ‖u‖≤1 satisfies ℓ(u)>α, every ρ>0 admits a unit vector y with ℓ(y)>α and ‖w+y‖≥2−ρ. Finally, KWOmega is the countable product [0,1]^ℕ, equipped with the infinite product of interval volume measures. These are definitions of quantities and properties, with no assertions relating the properties.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DaugavetModuli.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DaugavetModuli.lean; bytes 16..2855
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe uX u_1

namespace ExactModuli

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Closed linear subspaces of finite codimension. -/
def Cofinite (F : Submodule ℝ X) : Prop :=
  IsClosed (F : Set X) ∧ FiniteDimensional ℝ (X ⧸ F)

/-- Averaged increment for directions of norm at least one. -/
def averagedIncrement (N : Seminorm ℝ X) (x : X) (t : ℝ) (y : X) : ℝ :=
  (N (x + t • y) + N (x - t • y)) / 2 - 1

def H (N : Seminorm ℝ X) (x : X) (t : ℝ) : ℝ :=
  sSup {r | ∃ F : Submodule ℝ X, Cofinite F ∧
    r = sInf {a | ∃ y ∈ F, 1 ≤ N y ∧ a = averagedIncrement N x t y}}

def D (N : Seminorm ℝ X) (x : X) (t : ℝ) : ℝ :=
  sSup {r | ∃ F : Submodule ℝ X, Cofinite F ∧
    r = sInf {a | ∃ y ∈ F, N y = 1 ∧ a = N (x + t • y) - 1}}

def averagedModulus (N : Seminorm ℝ X) (t : ℝ) : ℝ :=
  sInf {r | ∃ x, N x = 1 ∧ r = H N x t}

def oneSidedModulus (N : Seminorm ℝ X) (t : ℝ) : ℝ :=
  sInf {r | ∃ x, N x = 1 ∧ r = D N x t}

/-- Two-sided comparison makes this seminorm a genuine norm equivalent to the original. -/
def EquivalentNorm (N : Seminorm ℝ X) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ x, a * ‖x‖ ≤ N x ∧ N x ≤ b * ‖x‖

def AUC (N : Seminorm ℝ X) : Prop :=
  ∀ t : ℝ, 0 < t → 0 < oneSidedModulus N t

/-- Every rank-one operator has the form `ell.smulRight v`. -/
def Daugavet (X : Type uX) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ (ell : X →L[ℝ] ℝ) (v : X),
    ‖ContinuousLinearMap.id ℝ X + ell.smulRight v‖ = 1 + ‖ell.smulRight v‖

variable {Ω : Type u_1} [MeasurableSpace Ω] (μ : Measure Ω)

/-- Convergence-in-measure distance on L1 equivalence classes. -/
def measureDistance (f g : Lp ℝ 1 μ) : ℝ :=
  sInf {a : ℝ | 0 < a ∧ μ.real {ω | a < |f ω - g ω|} < a}

/-- Finite covers of the entire unit ball in convergence-in-measure distance. -/
def MeasurePrecompactBall (E : Submodule ℝ (Lp ℝ 1 μ)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ s : Finset (Lp ℝ 1 μ),
    ∀ y : E, ‖y‖ ≤ 1 → ∃ b ∈ s, measureDistance μ (y : Lp ℝ 1 μ) b < ε

/-- Every nonempty unit-ball slice contains an almost antipodal unit vector. -/
def UnitSliceProperty (X : Type uX) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ (w : X), ‖w‖ = 1 → ∀ (ell : X →L[ℝ] ℝ) (α : ℝ),
    (∃ u : X, ‖u‖ ≤ 1 ∧ α < ell u) →
    ∀ ρ : ℝ, 0 < ρ → ∃ y : X, ‖y‖ = 1 ∧ α < ell y ∧ 2 - ρ ≤ ‖w + y‖

/-- The countable product of unit intervals. -/
abbrev KWOmega := ℕ → unitInterval

def kwMeasure : Measure KWOmega := Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval))



end ExactModuli
end
end OAI


