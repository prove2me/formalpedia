-- Prove2me | Definitions.Def_CoulombIonization
-- name    : CoulombIonization
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:05.770421+00:00
-- url     : https://prove2.me/theorems/f26dac81-42e1-4c2c-88d0-035c306998be
-- statement:
--   For N particles in ℝ³, configurations assign a position to each particle and spin configurations assign one of two spin values to each particle. A form vector consists of complex wavefunctions for every spin configuration and specified coordinate gradients. It is admissible when wavefunctions and gradients are square integrable, the gradients are weak derivatives as expressed by integration by parts against smooth compactly supported real test functions, simultaneous permutations of positions and spins multiply the wavefunction almost everywhere by the permutation sign, the total squared norm summed over spins is one, and all nuclear-attraction and pair-repulsion integrals are integrable. Its energy at nuclear charge Z is one-half the summed squared gradient norms, minus Z times the integrals of |ψ|²/|xᵢ|, plus the integrals of |ψ|²/|xᵢ−xⱼ| over pairs i<j, with all terms summed over spins. E(Z,N) is the infimum of admissible energies for N>0 and is zero for N=0. For natural m,Z, ionization is I(m,Z)=E(Z,Z−m)−E(Z,Z), using truncated natural subtraction. A Thomas–Fermi admissible density ρ is almost everywhere nonnegative and integrable, has integral M, and has integrable ρ^(5/3), ρ(x)/|x|, and ρ(x)ρ(y)/|x−y|. Its functional is c∫ρ^(5/3)−Z∫ρ(x)/|x|+(1/2)∫∫ρ(x)ρ(y)/|x−y|, where c=(3/10)(3π²)^(2/3); E_TF(Z,M) is its infimum over admissible densities, and I_TF(m,Z)=E_TF(Z,Z−m)−E_TF(Z,Z) for real m,Z. TFCharacterization(a) requires I_TF(m,Z)→a m^(7/3) as real Z→∞ for every fixed real m>0. JointLimit(a) requires I(mⱼ,Zⱼ)/mⱼ^(7/3)→a along every pair of natural sequences with 1≤mⱼ<Zⱼ, mⱼ→∞, and Zⱼ/mⱼ→∞. IteratedLimits(a) requires both the limsup and liminf of I(m,Z) as natural Z→∞, divided by m^(7/3), to tend to a as natural m→∞. MainStatement is the defined proposition that a positive real a satisfies all three limit conditions.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoulombIonization.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CoulombIonization.lean; bytes 16..3519
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

noncomputable section
namespace CoulombAtom

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Configuration (N : ℕ) := Fin N → Space
abbrev Spins (N : ℕ) := Fin N → Fin 2

structure FormVector (N : ℕ) where
  value : Spins N → Configuration N → ℂ
  gradient : Spins N → Fin N → Fin 3 → Configuration N → ℂ

def direction {N : ℕ} (i : Fin N) (a : Fin 3) : Configuration N :=
  Pi.single i (EuclideanSpace.single a 1)

def FormAdmissible {N : ℕ} (ψ : FormVector N) : Prop :=
  (∀ s, MemLp (ψ.value s) 2) ∧
  (∀ s i a, MemLp (ψ.gradient s i a) 2) ∧
  (∀ s i a (φ : Configuration N → ℝ),
    ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, ψ.value s x * Complex.ofReal (lineDeriv ℝ φ x (direction i a))) =
      -(∫ x, ψ.gradient s i a x * (φ x : ℂ))) ∧
  (∀ (π : Equiv.Perm (Fin N)) s, ∀ᵐ x,
    ψ.value (s ∘ π) (x ∘ π) =
      (((Equiv.Perm.sign π : ℤ) : ℂ) * ψ.value s x)) ∧
  (∑ s : Spins N, ∫ x, ‖ψ.value s x‖ ^ 2) = 1 ∧
  (∀ s i, Integrable (fun x => ‖ψ.value s x‖ ^ 2 / ‖x i‖)) ∧
  (∀ s i j, i ≠ j →
    Integrable (fun x => ‖ψ.value s x‖ ^ 2 / ‖x i - x j‖))

def formEnergy {N : ℕ} (Z : ℝ) (ψ : FormVector N) : ℝ :=
  (1 / 2 : ℝ) *
      (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        (∫ x, ‖ψ.gradient s i a x‖ ^ 2)) -
    Z * (∑ s : Spins N, ∑ i : Fin N,
      (∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i‖)) +
    (∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N,
      if i < j then (∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i - x j‖) else 0)

def energy (Z : ℝ) (N : ℕ) : ℝ :=
  if N = 0 then 0 else sInf {e | ∃ ψ : FormVector N,
    FormAdmissible ψ ∧ formEnergy Z ψ = e}

def ionization (m Z : ℕ) : ℝ :=
  energy Z (Z - m) - energy Z Z

def tfKinetic : ℝ := (3 / 10 : ℝ) * (3 * Real.pi ^ 2) ^ (2 / 3 : ℝ)

def directIntegrand (ρ : Space → ℝ) (p : Space × Space) : ℝ :=
  ρ p.1 * ρ p.2 / ‖p.1 - p.2‖

def TFAdmissible (M : ℝ) (ρ : Space → ℝ) : Prop :=
  (∀ᵐ x, 0 ≤ ρ x) ∧ Integrable ρ ∧ (∫ x, ρ x) = M ∧
  Integrable (fun x => ρ x ^ (5 / 3 : ℝ)) ∧
  Integrable (fun x => ρ x / ‖x‖) ∧ Integrable (directIntegrand ρ)

def tfFunctional (Z : ℝ) (ρ : Space → ℝ) : ℝ :=
  tfKinetic * (∫ x, ρ x ^ (5 / 3 : ℝ)) - Z * (∫ x, ρ x / ‖x‖) +
    (1 / 2 : ℝ) * ∫ p, directIntegrand ρ p

def tfEnergy (Z M : ℝ) : ℝ :=
  sInf {e | ∃ ρ : Space → ℝ, TFAdmissible M ρ ∧ tfFunctional Z ρ = e}

def tfIonization (m Z : ℝ) : ℝ := tfEnergy Z (Z - m) - tfEnergy Z Z

def TFCharacterization (a : ℝ) : Prop :=
  ∀ m : ℝ, 0 < m →
    Tendsto (tfIonization m) atTop (𝓝 (a * m ^ (7 / 3 : ℝ)))

def JointLimit (a : ℝ) : Prop :=
  ∀ m Z : ℕ → ℕ, (∀ j, 1 ≤ m j ∧ m j < Z j) →
    Tendsto m atTop atTop →
    Tendsto (fun j => (Z j : ℝ) / (m j : ℝ)) atTop atTop →
    Tendsto (fun j => ionization (m j) (Z j) / (m j : ℝ) ^ (7 / 3 : ℝ))
      atTop (𝓝 a)

def IteratedLimits (a : ℝ) : Prop :=
  Tendsto (fun m : ℕ => (limsup (ionization m) atTop) / (m : ℝ) ^ (7 / 3 : ℝ))
    atTop (𝓝 a) ∧
  Tendsto (fun m : ℕ => (liminf (ionization m) atTop) / (m : ℝ) ^ (7 / 3 : ℝ))
    atTop (𝓝 a)

def MainStatement : Prop :=
  ∃ a : ℝ, 0 < a ∧ TFCharacterization a ∧ JointLimit a ∧ IteratedLimits a



end CoulombAtom
end
end OAI


