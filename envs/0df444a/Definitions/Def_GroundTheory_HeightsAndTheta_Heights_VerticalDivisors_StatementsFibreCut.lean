-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFibreCut
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFibreCut
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:26.892805+00:00
-- url     : https://prove2.me/theorems/339822d9-57a8-41ad-960a-981fad5cee1f
-- title:
--   Statements Fibre Cut
-- statement:
--   Definitions and structural lemmas for Statements Fibre Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/StatementsFibreCut.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial IsDedekindDomain
def FibreClosedComponent.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDedekindDomain O] (F : Type) [Field F] [Algebra O F]
    [IsFractionRing O F] (n : ℕ) (P W : Ideal (MvPolynomial (Fin n) O)) (v : HeightOneSpectrum O),
    P.IsPrime → P.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ →
      W ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes →
        W.IsMaximal →
          ringKrullDim (MvPolynomial (Fin n) F ⧸ P.map (MvPolynomial.map (algebraMap O F))) = 0
def FibreCut.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDedekindDomain O] (n : ℕ) (P W : Ideal (MvPolynomial (Fin n) O))
    (v : HeightOneSpectrum O),
    P.IsPrime → P.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ →
      W ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes →
        ¬ W.IsMaximal →
          ∃ (P' W' : Ideal (MvPolynomial (Fin n) O)) (f : MvPolynomial (Fin n) O),
            f ∉ P ∧ P' ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧
            P'.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ ∧
            W' ∈ (P' ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes ∧
            ringKrullDim (MvPolynomial (Fin n) O ⧸ W') + 1 = ringKrullDim (MvPolynomial (Fin n) O ⧸ W)
def GenericFibreDrop.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (F : Type) [Field F] [Algebra O F]
    [IsFractionRing O F] (n : ℕ) (P P' : Ideal (MvPolynomial (Fin n) O))
    (f : MvPolynomial (Fin n) O),
    P.IsPrime → P'.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ → f ∉ P →
      P' ∈ (P ⊔ Ideal.span {f}).minimalPrimes →
        ringKrullDim (MvPolynomial (Fin n) F ⧸ P.map (MvPolynomial.map (algebraMap O F))) =
          ringKrullDim (MvPolynomial (Fin n) F ⧸ P'.map (MvPolynomial.map (algebraMap O F))) + 1
def CodimOnePrimeAvoid.Statement : Prop :=
  ∀ (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] (h : B),
    h ≠ 0 → 1 ≤ ringKrullDim B →
      ∃ N : Ideal B, N.IsPrime ∧ h ∉ N ∧ ringKrullDim (B ⧸ N) + 1 = ringKrullDim B
def two : HeightOneSpectrum ℤ :=
  ⟨Ideal.span {2}, (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two, by simp⟩
end GroundTheory.Heights₂.Heights.Vertical


