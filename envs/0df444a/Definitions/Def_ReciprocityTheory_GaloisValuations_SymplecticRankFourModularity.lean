-- Prove2me | Definitions.Def_ReciprocityTheory_GaloisValuations_SymplecticRankFourModularity
-- name    : ReciprocityTheory_GaloisValuations_SymplecticRankFourModularity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:45.271056+00:00
-- url     : https://prove2.me/theorems/7baca49b-ee03-4063-9a5c-fbd0f83cc1a1
-- title:
--   Symplectic Rank Four Modularity
-- statement:
--   Definitions and structural lemmas for Symplectic Rank Four Modularity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/SymplecticRankFourModularity.lean

import Definitions.Def_Formalism_ConjugateSelfDual_StatementRest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial Filter
namespace ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual
section basic
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n l : ℕ} [Fact l.Prime]
def IsFinitePlace (F : Type*) [Field F] [NumberField F] {Ω : Type*} [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) : Prop :=
  ∃ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v
def IsPlaceAbove (F : Type*) [Field F] [NumberField F] {Ω : Type*} [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (p : ℕ) : Prop :=
  ∃ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v ∧ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal
def CondDvd {H : Type*} [Monoid H] (χ : G F Ω →* H) (N : ℕ) : Prop :=
  ∀ σ : G F Ω, (∀ ζ : Ω, ζ ^ N = 1 → σ ζ = ζ) → χ σ = 1
def TwoPowerOrder {H : Type*} [Monoid H] (χ : G F Ω →* H) : Prop := ∃ j : ℕ, ∀ σ, χ σ ^ (2 ^ j) = 1
def tw (e : ℤ) (χ : G F Ω →* (Qbar l)ˣ) : G F Ω →* (Qbar l)ˣ := (cyc F Ω l) ^ e * χ
def CongChar (a b : G F Ω →* (Qbar l)ˣ) : Prop :=
  ∀ σ, ‖((a σ : (Qbar l)ˣ) : Qbar l) - (b σ : (Qbar l)ˣ)‖ < 1
def ResidualSS (ρ : G F Ω →* GL (Fin n) (Qbar l)) (c : Fin n → (G F Ω →* (Qbar l)ˣ)) : Prop :=
  ∀ (σ : G F Ω) (i : ℕ),
    ‖((ρ σ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly -
        ∏ j : Fin n, (X - C (((c j σ : (Qbar l)ˣ)) : Qbar l))).coeff i‖ < 1
def InertiaDiagAt (ρ : G F Ω →* GL (Fin n) (Qbar l)) (A : ValuationSubring Ω)
    (c : Fin n → (G F Ω →* (Qbar l)ˣ)) : Prop :=
  ∃ g : GL (Fin n) (Qbar l), ∀ σ ∈ Inertia (F := F) A,
    ((g⁻¹ * ρ σ * g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      Matrix.diagonal fun i => (((c i σ : (Qbar l)ˣ)) : Qbar l)
def OrdExactAt (ρ : G F Ω →* GL (Fin n) (Qbar l)) (A : ValuationSubring Ω)
    (c : Fin n → (G F Ω →* (Qbar l)ˣ)) : Prop :=
  ∃ g : GL (Fin n) (Qbar l),
    (∀ σ ∈ A.decompositionSubgroup F,
      ((g⁻¹ * ρ σ * g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).BlockTriangular id) ∧
    ∀ σ ∈ Inertia (F := F) A, ∀ i : Fin n,
      ((g⁻¹ * ρ σ * g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) i i =
        (((c i σ : (Qbar l)ˣ)) : Qbar l)
def OrdResidAt (ρ : G F Ω →* GL (Fin n) (Qbar l)) (A : ValuationSubring Ω)
    (c : Fin n → (G F Ω →* (Qbar l)ˣ)) : Prop :=
  ∃ g : GL (Fin n) (Qbar l),
    (∀ σ ∈ A.decompositionSubgroup F,
      ((g⁻¹ * ρ σ * g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).BlockTriangular id) ∧
    (∀ σ ∈ Inertia (F := F) A, ∀ i : Fin n,
      ((g⁻¹ * ρ σ * g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) i i =
        (((c i σ : (Qbar l)ˣ)) : Qbar l)) ∧
    ∀ σ ∈ A.decompositionSubgroup F, ∀ i : Fin n,
      ‖((g⁻¹ * ρ σ * g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) i i -
        (((c i σ : (Qbar l)ˣ)) : Qbar l)‖ < 1
structure HasShape (ρ : G F Ω →* GL (Fin n) (Qbar l)) (c : Fin n → (G F Ω →* (Qbar l)ˣ)) : Prop where
  cont : Continuous ρ
  irred : Irred ρ
  ord : ∀ A, IsPlaceAbove F A l → OrdExactAt ρ A c
  away : ∀ A, IsFinitePlace F A → ¬ IsPlaceAbove F A l → InertiaDiagAt ρ A c
  resid : ResidualSS ρ c
end basic
section proposals
variable {l : ℕ} [Fact l.Prime]
def ConjSelfDualOne {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] {n : ℕ} {R : Type*} [CommRing R]
    (ρ : G K Ω →* GL (Fin n) R) : Prop :=
  ∃ s : K ≃+* K, s ≠ RingEquiv.refl K ∧
    ∃ (τ : Ω ≃+* Ω) (hτ : ∀ x : K, τ (algebraMap K _ x) = algebraMap K _ (s x)),
    (∀ x, τ (τ x) = x) ∧
    ∃ J : Matrix (Fin n) (Fin n) R, IsUnit J.det ∧ J.transpose = J ∧
      ∀ σ : G K Ω, (ρ σ : Matrix (Fin n) (Fin n) R).transpose * J *
        (ρ (conjGal s τ hτ σ) : Matrix _ _ _) = J
def UnitaryRankThreeModularity (K : Type*) [Field K] [NumberField K] (Ω : Type*) [Field Ω] [Algebra K Ω]
    (S : CuspSpectrum K 3) (l : ℕ) [Fact l.Prime] (e : ℤ) (χ : G K Ω →* (Qbar l)ˣ) : Prop :=
  ∀ ρ : G K Ω →* GL (Fin 3) (Qbar l), HasShape ρ ![tw e χ, 1, (tw e χ)⁻¹] →
    (∀ A, IsPlaceAbove K A l → OrdResidAt ρ A ![tw e χ, 1, (tw e χ)⁻¹]) → ConjSelfDualOne ρ →
    ∀ ι : Qbar l →+* ℂ, ∃ π : S.Rep, (∀ τ, S.wt π τ = ![e, 0, -e]) ∧ FrobMatch ρ ι (S.hecke π)
def SymplecticWith {Ω : Type*} [Field Ω] [Algebra ℚ Ω] {n : ℕ} {R : Type*} [CommRing R]
    (r : G ℚ Ω →* GL (Fin n) R) (ν : G ℚ Ω →* Rˣ) : Prop :=
  ∃ J : Matrix (Fin n) (Fin n) R, IsUnit J.det ∧ J.transpose = -J ∧ (∀ i, J i i = 0) ∧
    ∀ σ, (r σ : Matrix (Fin n) (Fin n) R).transpose * J * (r σ : Matrix _ _ _) =
      (((ν σ : Rˣ)) : R) • J
def SymplecticRankFourModularity (Ω : Type*) [Field Ω] [Algebra ℚ Ω] (S : CuspSpectrum ℚ 4) (l : ℕ) [Fact l.Prime] (e a : ℤ)
    (χ ξ : G ℚ Ω →* (Qbar l)ˣ) : Prop :=
  ∀ r : G ℚ Ω →* GL (Fin 4) (Qbar l), HasShape r ![tw a ξ * tw e χ, tw e χ, tw a ξ, 1] →
    (∀ A, IsPlaceAbove ℚ A l → OrdResidAt r A ![tw a ξ * tw e χ, tw e χ, tw a ξ, 1]) →
    SymplecticWith r (tw a ξ * tw e χ) →
    ∀ ι : Qbar l →+* ℂ, ∃ π : S.Rep, (∀ τ, S.wt π τ = ![e + a, e, a, 0]) ∧ FrobMatch r ι (S.hecke π)
def RankTwoReducibleNonexistence (Ω : Type*) [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] (e : ℤ)
    (χ : G ℚ Ω →* (Qbar l)ˣ) : Prop :=
  ¬ ∃ s : G ℚ Ω →* GL (Fin 2) (Qbar l), HasShape s ![tw e χ, 1] ∧
    (∀ A, IsPlaceAbove ℚ A l → OrdResidAt s A ![tw e χ, 1]) ∧
    ∀ σ, (s σ : Matrix (Fin 2) (Fin 2) (Qbar l)).det = (((tw e χ σ : (Qbar l)ˣ)) : Qbar l)
def IsModularOf {Ω : Type*} [Field Ω] [Algebra ℚ Ω] (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) (k : Fin 2 → ℤ)
    (ι : Qbar l →+* ℂ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∃ χ : DirichletCharacter ℂ N,
    ∃ f : CuspForm (CongruenceSubgroup.Gamma1 N) (k 0 - k 1 + 1), IsNormEigenform f χ ∧
    ∀ᶠ v in cofinite, ∀ (A : ValuationSubring Ω) (σ : G ℚ Ω), IsPlaceOver (F := ℚ) A v →
      IsFrob A (normV v) σ →
      ι (ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)).trace =
        ((normV v : ℕ) : ℂ) ^ (k 1) * (UpperHalfPlane.qExpansion 1 f).coeff (normV v)
def RankTwoOddModularity (Ω : Type*) [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] (e : ℤ)
    (χ₁ χ₂ : G ℚ Ω →* (Qbar l)ˣ) : Prop :=
  ∀ W : G ℚ Ω →* GL (Fin 2) (Qbar l), HasShape W ![tw e χ₁, tw (-e) χ₂] → IsOdd W →
    ∀ ι : Qbar l →+* ℂ, IsModularOf W ![e, -e] ι
end proposals
end ReciprocityTheory.Gal


