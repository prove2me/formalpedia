-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
-- name    : GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:12.84457+00:00
-- url     : https://prove2.me/theorems/780d7d1c-94f0-405f-bd77-7fd14a84510c
-- title:
--   Record Eigen Inputs
-- statement:
--   Definitions and structural lemmas for Record Eigen Inputs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/RecordEigenInputs.lean

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
noncomputable section
namespace GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
def logRd (E : Type) [Field E] [NumberField E] : ℝ :=
  Real.log |(NumberField.discr E : ℝ)| / Module.finrank ℚ E
def extDifferent {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] (ι : E →+* L) :
    Ideal (𝓞 L) :=
  Ideal.map (RingOfIntegers.mapRingHom ι) (differentIdeal ℤ (𝓞 E))
def primeFrac (L : Type) [Field L] [NumberField L] (p : ℕ) : FractionalIdeal (𝓞 L)⁰ L :=
  ((Ideal.span {(p : 𝓞 L)} : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L)
def PrimeLogSum.Statement : Prop :=
  ∃ C : ℝ, ∀ B : ℕ, 2 ≤ B → ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ B →
    ∑ p ∈ P, Real.log p / ((p : ℝ) - 1) ≤ C * Real.log B
def LocalCountBound {L : Type} [Field L] [NumberField L] (𝔠 : FractionalIdeal (𝓞 L)⁰ L) (𝔇 : Ideal (𝓞 L))
    (S : Finset ℕ) (a b : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ 𝔓 : HeightOneSpectrum (𝓞 L), (p : 𝓞 L) ∈ 𝔓.asIdeal →
    |(FractionalIdeal.count L 𝔓 𝔠 : ℝ)| ≤
      (if p ∈ S then a * (FractionalIdeal.count L 𝔓 (primeFrac L p) : ℝ) / ((p : ℝ) - 1) else 0) +
        b * (FractionalIdeal.count L 𝔓 (𝔇 : FractionalIdeal (𝓞 L)⁰ L) : ℝ)
def NormCountBound.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (𝔠 : FractionalIdeal (𝓞 L)⁰ L) (𝔇 : Ideal (𝓞 L)) (S : Finset ℕ)
    (a b : ℝ), 𝔠 ≠ 0 → 𝔇 ≠ ⊥ → 0 ≤ a → 0 ≤ b → LocalCountBound 𝔠 𝔇 S a b →
    |Real.log (FractionalIdeal.absNorm 𝔠 : ℝ)| ≤
      Module.finrank ℚ L * (a * ∑ p ∈ S, Real.log p / ((p : ℝ) - 1)) + b * Real.log (Ideal.absNorm 𝔇 : ℝ)
def DifferentExtNorm.Statement : Prop :=
  ∀ (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L] (ι : E →+* L),
    extDifferent ι ≠ ⊥ ∧
      Real.log (Ideal.absNorm (extDifferent ι) : ℝ) = Module.finrank ℚ L * logRd E
end GroundTheory.Heights₂.Heights.NineStatements


