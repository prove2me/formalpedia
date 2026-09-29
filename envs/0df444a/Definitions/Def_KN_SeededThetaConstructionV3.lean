-- Prove2me | Definitions.Def_KN_SeededThetaConstructionV3
-- name    : KN_SeededThetaConstructionV3
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-09-25T11:15:24.4888+00:00
-- url     : https://prove2.me/theorems/c4f09582-0876-457b-b2a2-a898afb02558
-- title:
--   Normalized seeded theta data over the rebased realization
-- statement:
--   Finite seeded theta systems, norm relations, unit Euler factors, normalized theta measures, and interpolation, rebuilt over the rebased horizontal-character realization.
-- source:
--   Kriz–Nordentoft, Horizontal p-adic L-functions, arXiv:2310.20678v3, Sections 4–5.

import Definitions.Def_KN_SeededHorizontalCharacterRealizationV2B

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- Finite-level theta data using the faithful horizontal-character
realization. -/
structure SeededFiniteThetaDataV2
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV2 p ιp f η B) where
  coefficientRing : Subring ℂ_[p]
  coefficientRing_eq : coefficientRing = (𝓞_ℂ_[p]).toSubring
  coefficient_integral : ∀ x : coefficientRing, (x : ℂ_[p]) ∈ 𝓞_ℂ_[p]
  characters : SeededHorizontalCharacterRealizationV2 L
  theta : ∀ A : Finset ℕ, HorizontalGroupAlgebra coefficientRing p L.exponent A
  eulerFactor : ∀ (A : Finset ℕ) (n : ℕ),
    HorizontalGroupAlgebra coefficientRing p L.exponent A
  eulerFactor_augmentation_norm : ∀ (A : Finset ℕ) (n : ℕ),
    ‖((horizontalAugmentation (eulerFactor A n) : coefficientRing) : ℂ_[p])‖ =
      ‖ιp (η.2 (L.primeAt n) * f.coeff (L.primeAt n) - 1 -
        (η.2 (L.primeAt n)) ^ 2 * f.epsilon (L.primeAt n))‖

def SeededFiniteThetaDataV2.SatisfiesNormRelations
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV2 p ιp f η B}
    (Θ : SeededFiniteThetaDataV2 L) : Prop :=
  ∀ (A : Finset ℕ) (n : ℕ) (hn : n ∉ A),
    horizontalGroupAlgebraProjection Θ.coefficientRing (Finset.subset_insert n A)
      (Θ.theta (insert n A)) = Θ.eulerFactor A n * Θ.theta A

def SeededFiniteThetaDataV2.HasUnitEulerFactors
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV2 p ιp f η B}
    (Θ : SeededFiniteThetaDataV2 L) : Prop :=
  ∀ (A : Finset ℕ) (n : ℕ), IsUnit (Θ.eulerFactor A n)

/-- The compatible normalized theta measure, retaining the faithful quotient
maps and character realization used in its construction. -/
structure SeededNormalizedThetaMeasureV2
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV2 p ιp f η B) where
  coefficientRing : Subring ℂ_[p]
  coefficientRing_eq : coefficientRing = (𝓞_ℂ_[p]).toSubring
  coefficient_integral : ∀ x : coefficientRing, (x : ℂ_[p]) ∈ 𝓞_ℂ_[p]
  characters : SeededHorizontalCharacterRealizationV2 L
  measure : HorizontalMeasure coefficientRing p L.exponent

def SeededNormalizedThetaMeasureV2.InterpolatesSeededCriticalValues
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV2 p ιp f η B}
    (μ : SeededNormalizedThetaMeasureV2 L) : Prop :=
  ∀ χ, μ.measure.eval χ ≠ 0 ↔
    let θ := primitiveProductV2 η (μ.characters.realized χ)
    @MTT.criticalLValue ι f.form θ.1.1 ⟨Nat.ne_of_gt θ.1.2⟩ θ.2
      (k / 2 - 1) ≠ 0

end HorizontalPadicL


