-- Prove2me | Definitions.Def_KN_SeededInverseThetaSystemV2
-- name    : KN_SeededInverseThetaSystemV2
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-09-25T11:22:09.633093+00:00
-- url     : https://prove2.me/theorems/e4f71972-fcf6-4164-8322-83bb72f00ffb
-- title:
--   Inverse-seed theta systems over rebased data
-- statement:
--   Horizontal prime elements, inverse-seed Euler factors, and the inverse-seed theta-system predicate, rebuilt over the rebased full-support modular-symbol zero-set definitions.
-- source:
--   Kriz–Nordentoft, Horizontal p-adic L-functions, arXiv:2310.20678v3, Sections 4–5.

import Definitions.Def_KN_SeededThetaFullSupportModularSymbolZeroSetV2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

theorem SeededHorizontalPrimeDataV3.primeAt_coprime_supportModulus
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV3 p ιp f η B)
    (A : Finset ℕ) (n : ℕ) (hn : n ∉ A) :
    Nat.Coprime (L.primeAt n) (L.supportModulus A) := by
  rw [SeededHorizontalPrimeDataV3.supportModulus]
  apply Nat.Coprime.prod_right
  intro i hi
  apply (L.primeAt_prime n).coprime_iff_not_dvd.mpr
  intro hd
  have hprimes : L.primeAt i = L.primeAt n :=
    ((L.primeAt_prime i).dvd_iff_eq (L.primeAt_prime n).ne_one).mp hd
  have hin : i = n := L.primeAt_injective hprimes
  exact hn (hin ▸ hi)

/-- The image in the horizontal quotient at support `A` of a newly adjoined
auxiliary prime. -/
def SeededHorizontalCharacterRealizationV3.horizontalPrimeElement
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (R : SeededHorizontalCharacterRealizationV3 L)
    (A : Finset ℕ) (n : ℕ) (hn : n ∉ A) :
    HorizontalFiniteGroup p L.exponent A :=
  R.projections.supportProjection A
    (ZMod.unitOfCoprime (L.primeAt n)
      (L.primeAt_coprime_supportModulus A n hn))

/-- The three-term horizontal Euler factor over `ℂ_p` attached to adjoining
the auxiliary prime indexed by `n` to the support `A`. -/
def inverseSeedEulerFactorCp
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (R : SeededHorizontalCharacterRealizationV3 L)
    (A : Finset ℕ) (n : ℕ) (hn : n ∉ A) :
    HorizontalGroupAlgebra ℂ_[p] p L.exponent A :=
  let ℓ := L.primeAt n
  let g := R.horizontalPrimeElement A n hn
  MonoidAlgebra.single 1
      (ιp (f.coeff ℓ) / (ℓ : ℂ_[p]) ^ (k / 2 - 1)) -
    MonoidAlgebra.single g (ιp (η.2 ℓ)) -
    MonoidAlgebra.single g⁻¹ (ιp (f.epsilon ℓ * (η.2 ℓ)⁻¹))

/-- The exact inverse-seed modular-symbol formula for a finite theta system.
The first equation gives every theta coefficient after embedding into `ℂ_p`;
the second records the three-term Euler factor supplied by deleting the unique
nonunit lift in the horizontal distribution relation. -/
def SeededFiniteThetaDataV3.IsInverseSeedThetaSystem
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L) (P : MTT.Periods k ι f.form)
    (scale : IntegralPeriodScale f ιp P) : Prop :=
  letI : NeZero η.1.1 := ⟨Nat.ne_of_gt η.1.2⟩
  ∃ s : Bool, (MTT.sign s : ℤ) = (-1 : ℤ) ^ (k / 2 - 1) ∧
    (∀ (A : Finset ℕ) (g : HorizontalFiniteGroup p L.exponent A),
      let M := L.supportModulus A
      let q := η.2.conductor * M
      letI : NeZero q := ⟨mul_ne_zero η.2.conductor_ne_zero
        (Nat.ne_of_gt (L.supportModulus_pos A))⟩
      (((Θ.theta A).coeff g : Θ.coefficientRing) : ℂ_[p]) =
        ∑ u : (ZMod q)ˣ,
          if Θ.characters.projections.supportProjection A
              (ZMod.unitsMap (Nat.dvd_mul_left M η.2.conductor) u) = g then
            ιp (scale.scale * η.2 u.val.val *
              MTT.algebraicSymbol P s (k / 2 - 1) u.val.val q /
                (M : MTT.Qbar) ^ (k / 2 - 1))
          else 0) ∧
    ∀ (A : Finset ℕ) (n : ℕ) (hn : n ∉ A),
      MonoidAlgebra.mapRingHom
          (HorizontalFiniteGroup p L.exponent A) Θ.coefficientRing.subtype
          (Θ.eulerFactor A n) =
        inverseSeedEulerFactorCp Θ.characters A n hn

end HorizontalPadicL


