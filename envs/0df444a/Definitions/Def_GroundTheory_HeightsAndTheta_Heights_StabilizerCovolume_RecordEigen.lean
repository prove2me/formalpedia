-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigen
-- name    : GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:40.430278+00:00
-- url     : https://prove2.me/theorems/323c5e69-6d1f-4d0e-b9b7-1c4d1e23408f
-- title:
--   Record Eigen
-- statement:
--   Definitions and structural lemmas for Record Eigen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/RecordEigen.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_primeFrac_ne_zero_6c9de5626853

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
structure SmallBlockLattices (L : Type) [Field L] [NumberField L] (Ψ : Type) where

  eig : Ψ → FractionalIdeal (𝓞 L)⁰ L

  record : Ψ → FractionalIdeal (𝓞 L)⁰ L

  ht : Ψ → FractionalIdeal (𝓞 L)⁰ L
  eig_ne : ∀ τ, eig τ ≠ 0
  record_ne : ∀ τ, record τ ≠ 0
  ht_ne : ∀ τ, ht τ ≠ 0

  arch : Ψ → (L →+* ℂ) → ℝ
  arch_pos : ∀ τ σ, 0 < arch τ σ
def lineDeg {L : Type} [Field L] [NumberField L] (𝔞 : FractionalIdeal (𝓞 L)⁰ L) (nrm : (L →+* ℂ) → ℝ) : ℝ :=
  (-Real.log (FractionalIdeal.absNorm 𝔞 : ℝ) - ∑ σ : L →+* ℂ, Real.log (nrm σ)) / Module.finrank ℚ L
def SmallBlockLattices.degree {L : Type} [Field L] [NumberField L] {Ψ : Type} [Fintype Ψ]
    (P : SmallBlockLattices L Ψ) (lat : Ψ → FractionalIdeal (𝓞 L)⁰ L) : ℝ :=
  ∑ τ, lineDeg (lat τ) (P.arch τ)
def primesB (B : ℕ) (bad : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 B).filter Nat.Prime ∪ bad
def OrderBoundAtPrime {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] {Ψ : Type}
    (ι : Ψ → E →+* L) (j' : ℕ) (S : Finset ℕ) (P : SmallBlockLattices L Ψ) : Prop :=
  ∀ τ, LocalCountBound (P.ht τ * (P.record τ)⁻¹) (extDifferent (ι τ)) S j' j'
def EigenRecordAt {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] {Ψ : Type}
    (ι : Ψ → E →+* L) (j' : ℕ) (P : SmallBlockLattices L Ψ) : Prop :=
  ∀ τ, ∀ 𝔓 : HeightOneSpectrum (𝓞 L),
    |(FractionalIdeal.count L 𝔓 (P.record τ * (P.eig τ)⁻¹) : ℝ)| ≤
      j' * (FractionalIdeal.count L 𝔓 (extDifferent (ι τ) : FractionalIdeal (𝓞 L)⁰ L) : ℝ)
def RecordEigen.Statement : Prop :=
  ∃ C : ℝ, ∀ (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L] (Ψ : Type) [Fintype Ψ]
    (ι : Ψ → E →+* L) (j' B : ℕ) (bad : Finset ℕ) (P : SmallBlockLattices L Ψ),
    2 ≤ B → (∀ p ∈ bad, p.Prime) → bad.card ≤ B → EigenRecordAt ι j' P → OrderBoundAtPrime ι j' (primesB B bad) P →
      |P.degree P.record - P.degree P.eig| ≤ Fintype.card Ψ * j' * logRd E ∧
        |P.degree P.ht - P.degree P.record| ≤ C * (Fintype.card Ψ * j') * (Real.log B + logRd E)
theorem extDifferent_ne_bot {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] (ι : E →+* L) :
    extDifferent ι ≠ ⊥ := by
  rw [extDifferent, Ne, Ideal.map_eq_bot_iff_of_injective]
  · exact differentIdeal_ne_bot
  · intro x y h
    have h' := congrArg (fun z : 𝓞 L => (z : L)) h
    simp only [RingOfIntegers.mapRingHom_apply] at h'
    exact RingOfIntegers.ext (ι.injective h')
def smallBlockTwo {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] (ι : E →+* L) :
    SmallBlockLattices L Unit where
  eig _ := ((extDifferent ι : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L)
  record _ := 1
  ht _ := (primeFrac L 2)⁻¹
  eig_ne _ := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact extDifferent_ne_bot ι
  record_ne _ := one_ne_zero
  ht_ne _ := inv_ne_zero (primeFrac_ne_zero L Nat.prime_two)
  arch _ _ := 2
  arch_pos _ _ := two_pos
end GroundTheory.Heights₂.Heights.NineStatements


