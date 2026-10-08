-- Prove2me | Definitions.Def_CoulombRadii
-- name    : CoulombRadii
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:05.837097+00:00
-- url     : https://prove2.me/theorems/c8168a64-4f28-4902-9cb7-819196e31087
-- statement:
--   For n electrons, positions lie in ℝ³, configurations are n-tuples of positions, spin assignments are n-tuples with two possible spin values, and a wavefunction ψ assigns a complex value to each spin assignment and configuration. A proposed gradient g has one complex component for each spin assignment, electron and spatial coordinate; it is a weak gradient when integration against every smooth compactly supported real test function φ satisfies ∫(∂ᵢₐφ)ψ = −∫φgᵢₐ, where the derivative varies only that electron’s indicated coordinate. Antisymmetry means that simultaneously permuting positions and spins multiplies ψ by the permutation’s sign, almost everywhere in configuration space. The form domain requires antisymmetry, this weak-gradient identity, square integrability of every wavefunction and gradient component, and integrability of |ψ|² against each nuclear factor 1/|xᵢ| and pair factor 1/|xᵢ−xⱼ| for i<j. The squared norm is the spin sum of ∫|ψ|². For nuclear charge Z, the potential is V_Z(x)=−Z∑ᵢ1/|xᵢ|+∑ᵢ<ⱼ1/|xᵢ−xⱼ|, and energy is half the summed squared-gradient integrals plus the spin sum of ∫V_Z|ψ|². A normalized ground state for a neutral atom has Z electrons, squared norm one, and a form-domain gradient making its energy minimal among all normalized form-domain competitors. For N+1 electrons, the density at x is (N+1) times the spin sum of the integral of |ψ(x,y)|² over the other N positions. Exterior mass at radius r integrates this density over |x|>r; radius(ψ,m) is the infimum of all r≥0 whose exterior mass is at most the natural number m. The constant bTF is (81π²/2)^(1/3). For any family Ψ_N of (N+1)-electron wavefunctions, upperRadius and lowerRadius are the extended-real limsup and liminf of radius(Ψ_N,m) as N tends to infinity with m<N+1; these definitions impose no ground-state condition on the family.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoulombRadii.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CoulombRadii.lean; bytes 16..3299
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ContDiff

namespace NeutralAtom

abbrev Position := EuclideanSpace ℝ (Fin 3)
abbrev Configuration (n : ℕ) := Fin n → Position
abbrev Spins (n : ℕ) := Fin n → Fin 2
abbrev Wavefunction (n : ℕ) := Spins n → Configuration n → ℂ
abbrev Gradient (n : ℕ) := Spins n → Fin n → Fin 3 → Configuration n → ℂ

def coordinateDirection {n : ℕ} (i : Fin n) (a : Fin 3) : Configuration n :=
  Pi.single i (EuclideanSpace.single a 1)

def HasWeakGradient {n : ℕ} (ψ : Wavefunction n) (g : Gradient n) : Prop :=
  ∀ σ i a (φ : Configuration n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, (fderiv ℝ φ x (coordinateDirection i a) : ℂ) * ψ σ x) =
      -(∫ x, (φ x : ℂ) * g σ i a x)

def IsAntisymmetric {n : ℕ} (ψ : Wavefunction n) : Prop :=
  ∀ (p : Equiv.Perm (Fin n)) (σ : Spins n),
    (fun x : Configuration n => ψ (σ ∘ p) (x ∘ p)) =ᵐ[volume]
      (fun x => (((Equiv.Perm.sign p : ℤ) : ℂ)) * ψ σ x)

def FormDomain {n : ℕ} (ψ : Wavefunction n) (g : Gradient n) : Prop :=
  IsAntisymmetric ψ ∧ HasWeakGradient ψ g ∧
  (∀ σ, MemLp (ψ σ) 2 volume) ∧
  (∀ σ i a, MemLp (g σ i a) 2 volume) ∧
  (∀ σ i, Integrable (fun x : Configuration n => ‖x i‖⁻¹ * ‖ψ σ x‖ ^ 2)) ∧
  (∀ σ i j, i < j →
    Integrable (fun x : Configuration n => ‖x i - x j‖⁻¹ * ‖ψ σ x‖ ^ 2))

def normSquared {n : ℕ} (ψ : Wavefunction n) : ℝ :=
  ∑ σ : Spins n, ∫ x : Configuration n, ‖ψ σ x‖ ^ 2

def coulombPotential {n : ℕ} (Z : ℕ) (x : Configuration n) : ℝ :=
  -(Z : ℝ) * (∑ i : Fin n, ‖x i‖⁻¹) +
    ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), ‖x i - x j‖⁻¹

def energy {n : ℕ} (Z : ℕ) (ψ : Wavefunction n) (g : Gradient n) : ℝ :=
  (1 / 2 : ℝ) * (∑ σ : Spins n, ∑ i : Fin n, ∑ a : Fin 3,
    ∫ x : Configuration n, ‖g σ i a x‖ ^ 2) +
  ∑ σ : Spins n, ∫ x : Configuration n, coulombPotential Z x * ‖ψ σ x‖ ^ 2

def IsNormalizedGroundState (Z : ℕ) (ψ : Wavefunction Z) : Prop :=
  ∃ g : Gradient Z, FormDomain ψ g ∧ normSquared ψ = 1 ∧
    ∀ (χ : Wavefunction Z) (h : Gradient Z),
      FormDomain χ h → normSquared χ = 1 → energy Z ψ g ≤ energy Z χ h

def density {N : ℕ} (ψ : Wavefunction (N + 1)) (x : Position) : ℝ :=
  (N + 1 : ℝ) * ∑ σ : Spins (N + 1),
    ∫ y : Configuration N, ‖ψ σ (Fin.cons x y)‖ ^ 2

def exteriorMass {N : ℕ} (ψ : Wavefunction (N + 1)) (r : ℝ) : ℝ :=
  ∫ x in {x : Position | r < ‖x‖}, density ψ x

def radius {N : ℕ} (ψ : Wavefunction (N + 1)) (m : ℕ) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ exteriorMass ψ r ≤ (m : ℝ)}

def bTF : ℝ := (81 * Real.pi ^ 2 / 2) ^ (1 / 3 : ℝ)

def largeCharge (m : ℕ) : Filter ℕ :=
  atTop ⊓ Filter.principal {N : ℕ | m < N + 1}

def upperRadius (Ψ : ∀ N : ℕ, Wavefunction (N + 1)) (m : ℕ) : EReal :=
  Filter.limsup (fun N : ℕ => (radius (Ψ N) m : EReal)) (largeCharge m)

def lowerRadius (Ψ : ∀ N : ℕ, Wavefunction (N + 1)) (m : ℕ) : EReal :=
  Filter.liminf (fun N : ℕ => (radius (Ψ N) m : EReal)) (largeCharge m)



end NeutralAtom
end
end OAI


