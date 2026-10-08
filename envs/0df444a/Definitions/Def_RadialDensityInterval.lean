-- Prove2me | Definitions.Def_RadialDensityInterval
-- name    : RadialDensityInterval
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:14.019261+00:00
-- url     : https://prove2.me/theorems/d8fecf52-cde1-4aa8-8607-2c69acf26dc2
-- statement:
--   This block works in three-dimensional Euclidean space, with a potential φ being a real function of a nonnegative real distance. cube(L) is the set of points whose three coordinates all lie in [0,L], and configurationCube(L,N) is the set of N-tuples of points each in cube(L). The energy of a configuration x is the sum of φ(‖xᵢ−xⱼ‖) over all index pairs i<j. The partition function Z(φ,L,N,β) is (1/N!) times the integral over configurationCube(L,N) of exp(−β·energy(x)). packingNumber(L) is the supremum, over natural numbers n, of sizes of finite sets of n points in cube(L) with all pairwise distances at least 1, and IsPackingDensity(p) says that packingNumber(L)/L³ tends to p as L tends to infinity. IsBoundedPotential(φ) says that some M≥0 satisfies |φ(r)|≤M for every r. StableWith(φ,B) says that for every N and every configuration of N points in the space, the energy is at least −B·N. AlgebraicDecayWith(φ,C) says that |φ(r)|≤C·r^(−3−1/32) for all r≥1. IsCanonicalFreeEnergy(φ,ρ,f) says that for every β>0, with N=⌊ρL³⌋, the quantity −log Z(φ,L,N,β)/(β L³) tends to f(β) as L tends to infinity. StrictTemperatureCorner(f,βc) says there are numbers dLeft and dRight such that f has derivative dLeft at βc within (−∞,βc], derivative dRight at βc within [βc,∞), dRight<dLeft, and f is not differentiable at βc. These are definitions only; no theorem about them is stated in this block.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/RadialDensityInterval.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/RadialDensityInterval.lean; bytes 16..1904
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
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


