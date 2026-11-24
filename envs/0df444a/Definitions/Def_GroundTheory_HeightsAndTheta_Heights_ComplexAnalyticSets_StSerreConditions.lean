-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreConditions
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreConditions
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:06.147186+00:00
-- url     : https://prove2.me/theorems/044cbd1f-f354-4cfe-bc68-8ea6212f7441
-- title:
--   St Serre Conditions
-- statement:
--   Definitions and structural lemmas for St Serre Conditions, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSerreConditions.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatNormalFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing RingTheory.Sequence
def SerreRAt (B : Type*) [CommRing B] (k : ℕ) : Prop :=
  ringKrullDim B ≤ (k : WithBot ℕ∞) → IsRegularLocalRing B
def SerreSAt (B : Type*) [CommRing B] [IsLocalRing B] (k : ℕ) : Prop :=
  ∃ rs : List B, (∀ r ∈ rs, r ∈ maximalIdeal B) ∧ IsWeaklyRegular B rs ∧
    min (k : WithBot ℕ∞) (ringKrullDim B) ≤ (rs.length : WithBot ℕ∞)
def SerreR (A : Type*) [CommRing A] (k : ℕ) : Prop :=
  ∀ (P : Ideal A) [P.IsPrime], SerreRAt (Localization.AtPrime P) k
def SerreS (A : Type*) [CommRing A] (k : ℕ) : Prop :=
  ∀ (P : Ideal A) [P.IsPrime], SerreSAt (Localization.AtPrime P) k
def NormalRing (A : Type*) [CommRing A] : Prop :=
  ∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P)
theorem primeFibreLocalRing_ideal_ne_top (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Ideal S) [P.IsPrime] :
    Ideal.map (algebraMap S (Localization.AtPrime P))
      (Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) P)) ≠ ⊤ := by
  intro h
  have hle : Ideal.map (algebraMap S (Localization.AtPrime P))
      (Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) P)) ≤ maximalIdeal (Localization.AtPrime P) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono Ideal.map_comap_le
  exact (maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (h ▸ hle))
instance primeFibreLocalRing.isLocalRing (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Ideal S) [P.IsPrime] : IsLocalRing (primeFibreLocalRing R P) := by
  have : Nontrivial (primeFibreLocalRing R P) :=
    Ideal.Quotient.nontrivial_iff.mpr (primeFibreLocalRing_ideal_ne_top R P)
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
noncomputable def localizationAtPrimeComplexEquiv (P : Ideal ℂ) [P.IsPrime] :
    Localization.AtPrime P ≃+* ℂ := by
  have hP : P = ⊥ := (Ideal.eq_bot_or_top P).resolve_right (Ideal.IsPrime.ne_top ‹_›)
  exact (IsLocalization.atUnits ℂ P.primeCompl (fun x hx => by
    subst hP
    exact isUnit_iff_ne_zero.2 (by simpa using hx))).toRingEquiv.symm
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


