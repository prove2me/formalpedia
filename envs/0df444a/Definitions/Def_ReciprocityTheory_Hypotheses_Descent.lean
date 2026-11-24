-- Prove2me | Definitions.Def_ReciprocityTheory_Hypotheses_Descent
-- name    : ReciprocityTheory_Hypotheses_Descent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:39.256423+00:00
-- url     : https://prove2.me/theorems/71ac1c4f-e6f8-4b5c-b239-ffc1134fb7bc
-- title:
--   Descent
-- statement:
--   Definitions and structural lemmas for Descent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Hypotheses/Descent.lean

import Definitions.Def_ReciprocityTheory_GaloisValuations_SymplecticRankFourModularity
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
namespace ReciprocityTheory.Hyp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
def resGal (K L Ω : Type*) [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower K L Ω] : G L Ω →* G K Ω :=
  AlgEquiv.restrictScalarsHom K
def SolubleDescent (𝒮 : SpectrumFamily) : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [Group.IsSolvable (L ≃ₐ[K] L)], IsCMField K → IsCMField L →
  ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω]
    (l : ℕ) [Fact l.Prime] (n : ℕ) (ρ : G K Ω →* GL (Fin n) (Qbar l)), Continuous ρ →
    ConjSelfDualOne ρ → Irred (ρ.comp (resGal K L Ω)) →
  ∀ (k : Fin n → ℤ) (ι : Qbar l →+* ℂ),
    (∃ π' : (𝒮 L n).Rep, (∀ τ, (𝒮 L n).wt π' τ = k) ∧
      FrobMatch (ρ.comp (resGal K L Ω)) ι ((𝒮 L n).hecke π')) →
    ∃ π : (𝒮 K n).Rep, (∀ τ, (𝒮 K n).wt π τ = k) ∧ FrobMatch ρ ι ((𝒮 K n).hecke π)
def SolubleDescentReal (𝒮 : SpectrumFamily) : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsGalois ℚ F] [Group.IsSolvable (F ≃ₐ[ℚ] F)], IsTotallyReal F →
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra F Ω] [IsScalarTower ℚ F Ω] [IsAlgClosure ℚ Ω]
    (l : ℕ) [Fact l.Prime] (n : ℕ) (ρ : G ℚ Ω →* GL (Fin n) (Qbar l)) (ν : G ℚ Ω →* (Qbar l)ˣ),
    Continuous ρ → SymplecticWith ρ ν → (∀ c, IsComplexConj c → ν c = -1) →
    Irred (ρ.comp (resGal ℚ F Ω)) →
  ∀ (k : Fin n → ℤ) (ι : Qbar l →+* ℂ), StrictAnti k →
    (∃ π' : (𝒮 F n).Rep, (∀ τ, (𝒮 F n).wt π' τ = k) ∧
      FrobMatch (ρ.comp (resGal ℚ F Ω)) ι ((𝒮 F n).hecke π')) →
    ∃ π : (𝒮 ℚ n).Rep, (∀ τ, (𝒮 ℚ n).wt π τ = k) ∧ FrobMatch ρ ι ((𝒮 ℚ n).hecke π)
def SolubleDescentCMReal (𝒮 : SpectrumFamily) : Prop :=
  ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] [IsGalois F L]
    [Group.IsSolvable (L ≃ₐ[F] L)], IsTotallyReal F → IsCMField L →
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra F Ω] [Algebra L Ω] [IsScalarTower ℚ F Ω]
    [IsScalarTower ℚ L Ω] [IsScalarTower F L Ω] [IsAlgClosure ℚ Ω]
    (l : ℕ) [Fact l.Prime] (n : ℕ) (ρ : G ℚ Ω →* GL (Fin n) (Qbar l)) (ν : G ℚ Ω →* (Qbar l)ˣ),
    Continuous ρ → SymplecticWith ρ ν → (∀ c, IsComplexConj c → ν c = -1) →
    Irred (ρ.comp (resGal ℚ L Ω)) →
  ∀ (k : Fin n → ℤ) (ι : Qbar l →+* ℂ), StrictAnti k →
    (∃ π' : (𝒮 L n).Rep, (∀ τ, (𝒮 L n).wt π' τ = k) ∧
      FrobMatch (ρ.comp (resGal ℚ L Ω)) ι ((𝒮 L n).hecke π')) →
    ∃ π : (𝒮 F n).Rep, (∀ τ, (𝒮 F n).wt π τ = k) ∧
      FrobMatch (ρ.comp (resGal ℚ F Ω)) ι ((𝒮 F n).hecke π)
end ReciprocityTheory.Hyp


