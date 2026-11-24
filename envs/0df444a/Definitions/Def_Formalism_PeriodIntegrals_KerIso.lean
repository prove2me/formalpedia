-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_KerIso
-- name    : Formalism_PeriodIntegrals_KerIso
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T21:10:23.140889+00:00
-- url     : https://prove2.me/theorems/c3c268b3-2927-48c0-beac-ad01f560728f
-- title:
--   Ker Iso
-- statement:
--   Definitions and structural lemmas for Ker Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/KerIso.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
namespace PI.KerIso
def IsIsom {K E : Type} [Field K] [Field E] [Algebra K E] (cj : E → E) {n : Type} [Fintype n]
    (g : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) : Prop :=
  ∀ x y, ∑ w, algebraMap K E (g x w) * cj (algebraMap K E (g y w))
      = algebraMap K E (∑ a, Algebra.trace K E (x a * cj (y a)))
def AtP {K E : Type} [Field K] [NumberField K] [Field E] [Algebra K E] {n : Type} [Fintype n] (M : Set E)
    (g : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) (p : ℕ) : Prop :=
  (∀ x : Fin 4 → E, (∀ a, x a ∈ M) → ∃ s : ℕ, Nat.Coprime s p ∧
    ∀ w, (s : K) * g x w ∈ (algebraMap (𝓞 K) K).range) ∧
  ∀ v : Fin 4 × n → K, (∀ w, v w ∈ (algebraMap (𝓞 K) K).range) →
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ a, (s : E) * g.symm v a ∈ M
def detRel {K E : Type} [Field K] [Field E] [Algebra K E] {n : Type} [Fintype n]
    (g g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) : K :=
  LinearMap.det ((g₀.symm.trans g : (Fin 4 × n → K) ≃ₗ[K] _) : (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K))
def ordK {K : Type} [Field K] [NumberField K] (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : K) : ℤ :=
  -WithZero.log (𝔭.valuation K x)
def IsConj (K : Type) {E : Type} [Field K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E) : Prop :=
  (∀ x, cj (cj x) = x) ∧ (∀ k : K, ∃ k' : K, cj (algebraMap K E k) = algebraMap K E k') ∧
    ∃ k : K, cj (algebraMap K E k) ≠ algebraMap K E k
def DetOrdIndep : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [Algebra K E] (n : Type) [Fintype n] (M : Set E) (p : ℕ)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (g g' g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)),
    p.Prime → ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal → AtP M g p → AtP M g' p →
      ordK 𝔭 (detRel g g₀) = ordK 𝔭 (detRel g' g₀)
def DetOrdFin : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (n : Type) [Fintype n]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), I ≠ 0 →
    ∀ (S : ℕ → Prop) (pp : ℕ → IsDedekindDomain.HeightOneSpectrum (𝓞 K))
      (gp : ℕ → ((Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K))) (g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)),
      (∀ p, p.Prime → S p → ((p : ℕ) : 𝓞 K) ∈ (pp p).asIdeal) →
      (∀ p, p.Prime → S p → AtP {x : E | x ∈ I} (gp p) p) →
        {p : ℕ | p.Prime ∧ S p ∧ ordK (pp p) (detRel (gp p) g₀) ≠ 0}.Finite
def FourSq : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E) (n : Type) [Fintype n],
    Module.finrank ℚ K = 2 → Fintype.card n = Module.finrank K E → IsConj K cj →
    (∀ x : E, x ≠ 0 → 0 < Algebra.trace ℚ E (x * cj x)) →
      ∃ g : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K), IsIsom cj g
def ExtC : Prop :=
  ∀ (K E : Type) [Field K] [Field E] [Algebra K E] [FiniteDimensional K E] (n : Type) [Fintype n] (φ : K →+* ℂ)
    (τ : n → E →+* ℂ), Function.Injective τ → (∀ i k, τ i (algebraMap K E k) = φ k) →
    Fintype.card n = Module.finrank K E → ∀ g : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K),
      ∃ gC : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ),
        ∀ x : Fin 4 → E, gC (fun w => τ w.2 (x w.1)) = fun w => φ (g x w)
def SplitsAt (K : Type) {E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E) (p : ℕ) : Prop :=
  ∃ P : Ideal (𝓞 K), P.IsPrime ∧ ((p : ℕ) : 𝓞 K) ∈ P ∧ ∃ a b : 𝓞 K,
    cj (algebraMap K E (a : K)) = algebraMap K E (b : K) ∧ a ∈ P ∧ b ∉ P
def SelfDualI (K : Type) {E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Prop :=
  ∀ y : E, y ∈ I ↔ ∀ x ∈ I, Algebra.trace K E (x * cj y) ∈ (algebraMap (𝓞 K) K).range
def LocIso : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E) (n : Type) [Fintype n]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (p : ℕ),
    Module.finrank ℚ K = 2 → IsConj K cj → p.Prime → SplitsAt K cj p → SelfDualI K cj I →
    (∃ g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K), IsIsom cj g₀) →
      ∃ g : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K), IsIsom cj g ∧ AtP {x : E | x ∈ I} g p
end PI.KerIso


