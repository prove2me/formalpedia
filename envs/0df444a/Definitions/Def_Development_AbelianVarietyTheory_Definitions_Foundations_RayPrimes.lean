-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:12.700349+00:00
-- url     : https://prove2.me/theorems/e873e994-6f57-4405-b970-f7e1ba27af2d
-- title:
--   Ray Primes
-- statement:
--   Definitions and structural lemmas for Ray Primes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/RayPrimes.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GlobalTheory.Mem.An
def zerosIn {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ T ∧ DirichletCharacter.LFunction χ ρ = 0}
def zmult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ
def zsum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∑ᶠ ρ ∈ zerosIn χ t T, (zmult χ ρ : ℂ) * f ρ
def zsumR {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) (f : ℂ → ℝ) : ℝ :=
  ∑ᶠ ρ ∈ zerosIn χ t T, (zmult χ ρ : ℝ) * f ρ
def psiChi {q : ℕ} (χ : DirichletCharacter ℂ q) (u : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)
def rayI {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Subgroup.closure {I | ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔮 ∧
    (I : FractionalIdeal (𝓞 K)⁰ K) = (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)}
def rayP {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Subgroup.closure {I | ∃ a : 𝓞 K, a - 1 ∈ 𝔮 ∧
    (I : FractionalIdeal (𝓞 K)⁰ K) = ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)}
def rayNo {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) : ℕ := (rayP 𝔮).relIndex (rayI 𝔮)
def rayPrimes {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) (X : ℝ) : Set (HeightOneSpectrum (𝓞 K)) :=
  {v | ¬ v.asIdeal ∣ 𝔮 ∧ (Ideal.absNorm v.asIdeal : ℝ) ≤ X ∧
    ∃ I ∈ rayP 𝔮, (I : FractionalIdeal (𝓞 K)⁰ K) = (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)}
def NormOne (d M p : ℕ) : Prop :=
  ∃ A B : ℤ, A ^ 2 + (d : ℤ) * B ^ 2 = 4 * (p : ℤ) ∧ (M : ℤ) ∣ B ∧ (2 * (M : ℤ)) ∣ A - 2 - B
open Classical in

def normPrimes (d M : ℕ) (X Y : ℝ) : Finset ℕ :=
  (Ioc ⌊X⌋₊ ⌊Y⌋₊).filter (fun p => p.Prime ∧ NormOne d M p)
end GlobalTheory.Mem.An


