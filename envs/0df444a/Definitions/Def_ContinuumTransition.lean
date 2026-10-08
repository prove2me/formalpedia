-- Prove2me | Definitions.Def_ContinuumTransition
-- name    : ContinuumTransition
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:05.327411+00:00
-- url     : https://prove2.me/theorems/bf19f350-40a7-4c3a-84f2-69fbb3ed114a
-- statement:
--   In three-dimensional Euclidean space, a radial pair potential associated with φ:ℝ→ℝ has value φ(‖x‖) for x≠0 and +∞ at x=0; the energy Eφ of N particles is the sum over unordered distinct pairs. Admissibility means that this extended-real potential is measurable, φ is bounded above and below on every compact interval of positive radii, φ(r)→+∞ as r↓0, and φ≤−a on some annulus of radii 0<r₁<r₂ for some a>0. It also requires integrability of r²|φ(r)| over (R,∞) for some R>0 and stability: Eφ(x)≥−BN for some real B, every natural N, and every configuration x. The cube of side L is defined by all three coordinates lying in [−L/2,L/2]. At inverse temperature β, the Boltzmann weight is zero for infinite energy and exp(−βEφ) otherwise. The canonical partition function Zφ(β,L,N) is 1 for N=0 and otherwise 1/N! times the integral of this weight over configurations in the cube. A function f has canonical free energy when, for every β>0 and density ρ>0, L⁻³ log Zφ(β,L,⌊ρL³⌋₊) tends to −βf(β,ρ) as L→∞, where the particle count uses the nonnegative integer floor. MainStatement is the defined proposition that there exist such an admissible φ, a function f with this limit, a nonempty open interval I⊆(0,∞) of densities, and βc∈(1/2,3/2), with φ(r)=o(r⁻³) as r→∞, such that for every ρ∈I the function β↦f(β,ρ) has finite left and right derivatives at βc and its right derivative is strictly smaller than its left derivative.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ContinuumTransition.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ContinuumTransition.lean; bytes 16..2299
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set

namespace ContinuumTemperature

abbrev Space := EuclideanSpace ℝ (Fin 3)

noncomputable def radialPotential (φ : ℝ → ℝ) (x : Space) : EReal :=
  if x = 0 then ⊤ else (φ ‖x‖ : EReal)

noncomputable def energy (φ : ℝ → ℝ) {N : ℕ} (x : Fin N → Space) : EReal :=
  ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j),
    radialPotential φ (x i - x j)

def Admissible (φ : ℝ → ℝ) : Prop :=
  Measurable (radialPotential φ) ∧
  (∀ a b : ℝ, 0 < a → a ≤ b →
    BddAbove (φ '' Icc a b) ∧ BddBelow (φ '' Icc a b)) ∧
  Tendsto φ (𝓝[>] (0 : ℝ)) atTop ∧
  (∃ r₁ r₂ a : ℝ, 0 < r₁ ∧ r₁ < r₂ ∧ 0 < a ∧
    ∀ r ∈ Icc r₁ r₂, φ r ≤ -a) ∧
  (∃ R : ℝ, 0 < R ∧ IntegrableOn (fun r : ℝ => r ^ 2 * |φ r|) (Ioi R)) ∧
  (∃ B : ℝ, ∀ (N : ℕ) (x : Fin N → Space),
    ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)

def cube (L : ℝ) : Set Space :=
  {x | ∀ i, x i ∈ Icc (-L / 2) (L / 2)}

noncomputable def boltzmann (φ : ℝ → ℝ) (β : ℝ) {N : ℕ}
    (x : Fin N → Space) : ℝ :=
  if energy φ x = ⊤ then 0 else Real.exp (-β * (energy φ x).toReal)

noncomputable def partition (φ : ℝ → ℝ) (β L : ℝ) (N : ℕ) : ℝ :=
  if N = 0 then 1 else
    (1 / (N.factorial : ℝ)) *
      ∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ β x

def HasCanonicalFreeEnergy (φ : ℝ → ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ β ρ : ℝ, 0 < β → 0 < ρ →
    Tendsto (fun L : ℝ => L⁻¹ ^ 3 * Real.log (partition φ β L ⌊ρ * L ^ 3⌋₊))
      atTop (𝓝 (-β * f β ρ))

def MainStatement : Prop :=
  ∃ (φ : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (I : Set ℝ) (βc : ℝ),
    Admissible φ ∧
    Asymptotics.IsLittleO atTop φ (fun r : ℝ => r ^ (-3 : ℤ)) ∧
    HasCanonicalFreeEnergy φ f ∧
    IsOpen I ∧ OrdConnected I ∧ I.Nonempty ∧ I ⊆ Ioi 0 ∧
    βc ∈ Ioo (1 / 2 : ℝ) (3 / 2 : ℝ) ∧
    ∀ ρ ∈ I, ∃ dminus dplus : ℝ,
      HasDerivWithinAt (fun β => f β ρ) dminus (Iic βc) βc ∧
      HasDerivWithinAt (fun β => f β ρ) dplus (Ici βc) βc ∧
      dplus < dminus



end ContinuumTemperature
end OAI


