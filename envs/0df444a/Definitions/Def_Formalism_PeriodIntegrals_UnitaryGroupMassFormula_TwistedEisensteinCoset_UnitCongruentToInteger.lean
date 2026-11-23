-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:35.980411+00:00
-- url     : https://prove2.me/theorems/5d6a0303-cd97-403f-a370-646fb3982865
-- title:
--   Unit Congruent To Integer
-- statement:
--   Definitions and structural lemmas for Unit Congruent To Integer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/UnitCongruentToInteger.lean

import Definitions.Def_Formalism_PeriodIntegrals_TwistedEisensteinNonvanishing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace PI.TwistedEisensteinNonvanishing.W
def IntegerIntegralIffDvd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ i e : ℕ, IntAt P ((i : E) / (qOf P : E) ^ e) ↔ qOf P ^ e ∣ i
def IntegralApproximationByInteger : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ (x : E) (N : ℕ), IntAt P x → ∃ i : ℕ, i < qOf P ^ N ∧ IntAt P ((x - i) / (qOf P : E) ^ N)
def ElementEqPrimePowerMulUnit : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ a : E, a ≠ 0 → ∃ (e : ℤ) (w : E), a = (qOf P : E) ^ e * w ∧ w ≠ 0 ∧ IntAt P w ∧ IntAt P w⁻¹
def ValuationExponentUnique : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ (e e' : ℤ) (w w' : E), w ≠ 0 → IntAt P w → IntAt P w⁻¹ → IntAt P w' → IntAt P w'⁻¹ →
      (qOf P : E) ^ e * w = (qOf P : E) ^ e' * w' → e = e'
def UnitCongruentToInteger : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ (w : E) (N : ℕ), w ≠ 0 → IntAt P w → IntAt P w⁻¹ →
      ∃ w0 : ℕ, Nat.Coprime w0 (qOf P) ∧ IntAt P ((w - w0) / (qOf P : E) ^ N)
end PI.TwistedEisensteinNonvanishing.W


