-- Prove2me | Definitions.Def_ReciprocityTheory_CommutativeAlgebra_WeakRegularity_GorIndepStatement
-- name    : ReciprocityTheory_CommutativeAlgebra_WeakRegularity_GorIndepStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:16.98292+00:00
-- url     : https://prove2.me/theorems/a42c41c3-d9f7-4620-b688-ab068e85cf8b
-- title:
--   Gor Indep Statement
-- statement:
--   Definitions and structural lemmas for Gor Indep Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/WeakRegularity/GorIndepStatement.lean

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.CA.Link
open IsLocalRing
universe u
def IsGorZero (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  IsArtinianRing A ∧
    ∃ s : A, s ≠ 0 ∧ (⊥ : Ideal A).colon (maximalIdeal A : Set A) = Ideal.span {s}
def IsGor (R : Type*) [CommRing R] [IsLocalRing R] : Prop :=
  IsNoetherianRing R ∧ ∃ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) ∧
    RingTheory.Sequence.IsRegular R rs ∧
    ∃ _ : IsLocalRing (R ⧸ Ideal.ofList rs), IsGorZero (R ⧸ Ideal.ofList rs)
def FullCM {R : Type*} [CommRing R] (I : Ideal R) : Prop :=
  ∃ _ : IsLocalRing (R ⧸ I), IsCM (R ⧸ I) ∧ ringKrullDim (R ⧸ I) = ringKrullDim R
def ann {R : Type*} [CommRing R] (I : Ideal R) : Ideal R := (⊥ : Ideal R).colon (I : Set R)
def LinkageStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R], IsGor R → ∀ I : Ideal R, I ≠ ⊥ → FullCM I →
    FullCM (ann I) ∧ ann (ann I) = I ∧
    (∀ φ : I →ₗ[R] R, ∃ b : R, ∀ i : I, φ i = b * i) ∧
    ∀ p : Ideal R, p ∈ (ann I).minimalPrimes ↔
      p ∈ minimalPrimes R ∧
        ∃ _ : p.IsPrime, I.map (algebraMap R (Localization.AtPrime p)) ≠ ⊥
def GorIndepStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R], IsGor R → ∀ rs : List R,
    (∀ r ∈ rs, r ∈ maximalIdeal R) → RingTheory.Sequence.IsRegular R rs →
    IsArtinianRing (R ⧸ Ideal.ofList rs) →
    ∃ _ : IsLocalRing (R ⧸ Ideal.ofList rs), IsGorZero (R ⧸ Ideal.ofList rs)
def CIGorStatement : Prop :=
  ∀ (P : Type u) [CommRing P] [IsRegularLocalRing P], ∀ fs : List P,
    (∀ f ∈ fs, f ∈ maximalIdeal P) → RingTheory.Sequence.IsRegular P fs →
    ∃ _ : IsLocalRing (P ⧸ Ideal.ofList fs), IsGor (P ⧸ Ideal.ofList fs)
def GorCMStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R], IsGor R → IsCM R
end ReciprocityTheory.CA.Link


