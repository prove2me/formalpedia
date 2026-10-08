-- Prove2me | Definitions.Def_RadialTransition
-- name    : RadialTransition
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:14.256961+00:00
-- url     : https://prove2.me/theorems/da1aa29e-b3f6-46f8-b92b-ad096a3f73c2
-- statement:
--   This block sets up a framework for classical statistical mechanics of N particles in three-dimensional Euclidean space interacting through a radial pair potential φ, a real function on the nonnegative reals. The cube(L) is the set of points whose three coordinates all lie in [0,L], and configurationCube(L,N) is the set of N-tuples of points in that cube. The energy of a configuration is the sum of φ(distance) over all pairs i<j. The partition function with inverse temperature β is (1/N!) times the integral over configurationCube(L,N) of exp(-β·energy). The packingNumber(L) is the supremum of the sizes of finite sets of points in cube(L) whose distinct points are at distance at least 1 from each other, and IsPackingDensity(p) says packingNumber(L)/L^3 tends to p as L tends to infinity. Further predicates on a potential are: IsBoundedPotential, meaning |φ| is bounded by some constant M≥0; StableWith(φ,B), meaning that for every N and every configuration the energy is at least -B·N; and AlgebraicDecayWith(φ,C), meaning |φ(r)| ≤ C·r^(-3-1/32) for all r≥1. IsCanonicalFreeEnergy(φ,ρ,f) says that for every β>0 the quantity -log(partition with N=⌊ρL^3⌋ particles)/(βL^3) tends to f(β) as L tends to infinity, so f is the free energy per unit volume at density ρ. Finally, StrictTemperatureCorner(f,βc) says that f has a left derivative dLeft and a right derivative dRight at βc, with dRight<dLeft, and that f is not differentiable at βc. These are definitions only, and no theorem is asserted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/RadialTransition.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/RadialTransition.lean; bytes 16..1887
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators NNReal
open Filter MeasureTheory Set

namespace RadialTransition

abbrev Position := EuclideanSpace ℝ (Fin 3)
abbrev Potential := ℝ≥0 → ℝ

def cube (L : ℝ) : Set Position :=
  {x | ∀ k : Fin 3, 0 ≤ x k ∧ x k ≤ L}

def configurationCube (L : ℝ) (N : ℕ) : Set (Fin N → Position) :=
  {x | ∀ i : Fin N, x i ∈ cube L}

def energy (φ : Potential) {N : ℕ} (x : Fin N → Position) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N with i < j, φ (nndist (x i) (x j))

def partition (φ : Potential) (L : ℝ) (N : ℕ) (β : ℝ) : ℝ :=
  (N.factorial : ℝ)⁻¹ *
    ∫ x in configurationCube L N, Real.exp (-β * energy φ x)

def packingNumber (L : ℝ) : ℕ :=
  sSup {n : ℕ | ∃ X : Finset Position, X.card = n ∧
    (∀ x ∈ X, x ∈ cube L) ∧
    (∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1 ≤ dist x y)}

def IsPackingDensity (p : ℝ) : Prop :=
  Tendsto (fun L : ℝ => (packingNumber L : ℝ) / L ^ 3) atTop (nhds p)

def IsBoundedPotential (φ : Potential) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℝ≥0, |φ r| ≤ M

def StableWith (φ : Potential) (B : ℝ) : Prop :=
  ∀ (N : ℕ) (x : Fin N → Position), -(B * N) ≤ energy φ x

def AlgebraicDecayWith (φ : Potential) (C : ℝ) : Prop :=
  ∀ r : ℝ≥0, 1 ≤ r → |φ r| ≤ C * (r : ℝ) ^ (-(3 : ℝ) - 1 / 32)

def IsCanonicalFreeEnergy (φ : Potential) (ρ : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ β : ℝ, 0 < β →
    Tendsto (fun L : ℝ =>
      -(Real.log (partition φ L ⌊ρ * L ^ 3⌋₊ β) / (β * L ^ 3)))
      atTop (nhds (f β))

def StrictTemperatureCorner (f : ℝ → ℝ) (βc : ℝ) : Prop :=
  ∃ dLeft dRight : ℝ,
    HasDerivWithinAt f dLeft (Iic βc) βc ∧
    HasDerivWithinAt f dRight (Ici βc) βc ∧
    dRight < dLeft ∧ ¬DifferentiableAt ℝ f βc



end RadialTransition
end
end OAI


