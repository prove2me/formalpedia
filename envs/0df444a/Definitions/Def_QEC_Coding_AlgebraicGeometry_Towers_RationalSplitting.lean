-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalSplitting
-- name    : QEC_Coding_AlgebraicGeometry_Towers_RationalSplitting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:58:46.84579+00:00
-- url     : https://prove2.me/theorems/317e0182-7200-435a-826a-0bd38d2ed0ea
-- title:
--   Rational Splitting
-- statement:
--   Definitions and structural lemmas for Rational Splitting, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalSplitting.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplittingIdeals
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_split_inertiaDegIn_eq_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_splitIntegralAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
noncomputable def splitUpperHeightOne
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier) :
    IsDedekindDomain.HeightOneSpectrum (SplitIntegralClosure Q P x hx) := by
  let R := (splitUpperPrime Q P x hx c).1
  letI : R.IsPrime := inferInstance
  letI : R.LiesOver (IsLocalRing.maximalIdeal Q.place.valuationRing) :=
    inferInstance
  letI : IsDiscreteValuationRing Q.place.valuationRing :=
    Q.place.valuationRing_isDiscreteValuationRing
  exact
    { asIdeal := R
      isPrime := inferInstance
      ne_bot := Ideal.ne_bot_of_liesOver_of_ne_bot
        (IsDiscreteValuationRing.not_a_field Q.place.valuationRing) R }
@[simp]
theorem splitUpperHeightOne_asIdeal
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier) :
    (splitUpperHeightOne Q P x hx c).asIdeal =
      (splitUpperPrime Q P x hx c).1 :=
  rfl
noncomputable def splitAbovePlace
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier) :
    GlobalPlace F256 (StepField P x hx) where
  valuation := (splitUpperHeightOne Q P x hx c).valuation
    (StepField P x hx)
  normalized := (splitUpperHeightOne Q P x hx c).valuation_surjective
    (StepField P x hx)
theorem splitUpperPrime_inertiaDeg_eq_one
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (c : LinearMap.ker f256ArtinSchreier) :
    (IsLocalRing.maximalIdeal Q.place.valuationRing).inertiaDeg'
        (splitUpperPrime Q P x hx c).1 = 1 := by
  let O := Q.place.valuationRing
  let S := SplitIntegralClosure Q P x hx
  let L := StepField P x hx
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let R : Ideal S := (splitUpperPrime Q P x hx c).1
  let G := L ≃ₐ[K] L
  letI : IsDiscreteValuationRing O :=
    Q.place.valuationRing_isDiscreteValuationRing
  letI : MulSemiringAction G S :=
    IsIntegralClosure.MulSemiringAction O K L S
  letI : IsGaloisGroup G O S :=
    IsGaloisGroup.of_isFractionRing G O S K L
  letI : R.IsPrime := inferInstance
  letI : R.LiesOver m := inferInstance
  calc
    m.inertiaDeg' R = m.inertiaDegIn S := by
      letI : m.IsMaximal := by dsimp [m]; infer_instance
      letI : R.IsMaximal := by dsimp [R]; infer_instance
      rw [Ideal.inertiaDeg'_eq_inertiaDeg]
      exact (Ideal.inertiaDegIn_eq_inertiaDeg m R G).symm
    _ = 1 := split_inertiaDegIn_eq_one Q P x hx hregular
noncomputable def splitUpperQuotientConstantsEquiv
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (c : LinearMap.ker f256ArtinSchreier) :
    F256 ≃+*
      (SplitIntegralClosure Q P x hx ⧸
        (splitUpperPrime Q P x hx c).1) := by
  let O := Q.place.valuationRing
  let S := SplitIntegralClosure Q P x hx
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let R : Ideal S := (splitUpperPrime Q P x hx c).1
  letI : m.IsMaximal := by
    dsimp [m]
    infer_instance
  letI : R.IsMaximal := by
    dsimp [R]
    infer_instance
  letI : R.LiesOver m := inferInstance
  letI : Field (O ⧸ m) := Ideal.Quotient.field m
  letI : Field (S ⧸ R) := Ideal.Quotient.field R
  letI : Algebra (O ⧸ m) (S ⧸ R) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.over_def R m).le
  have hfinrank : Module.finrank (O ⧸ m) (S ⧸ R) = 1 := by
    rw [← Ideal.inertiaDeg_algebraMap]
    exact splitUpperPrime_inertiaDeg_eq_one Q P x hx hregular c
  let e : (O ⧸ m) ≃+* (S ⧸ R) :=
    RingEquiv.ofBijective (algebraMap (O ⧸ m) (S ⧸ R))
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfinrank)
  exact Q.constantsEquiv.trans e
noncomputable def splitUpperQuotientResidueEquiv
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier) :
    (SplitIntegralClosure Q P x hx ⧸
        (splitUpperPrime Q P x hx c).1) ≃+*
      GlobalPlace.residueField (splitAbovePlace Q P x hx c) := by
  let S := SplitIntegralClosure Q P x hx
  let L := StepField P x hx
  let H := splitUpperHeightOne Q P x hx c
  letI : H.asIdeal.IsMaximal := inferInstance
  let e₁ : (S ⧸ H.asIdeal) ≃+*
      IsLocalRing.ResidueField (H.valuationSubringAtPrime L) :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal H.asIdeal
      (H.valuationSubringAtPrime L)
  let e₂ : H.valuationSubringAtPrime L ≃+*
      (H.valuation L).valuationSubring := by
    rw [H.valuationSubringAtPrime_eq_valuationSubring]
  exact e₁.trans (IsLocalRing.ResidueField.mapEquiv e₂)
noncomputable def splitUpperAbstractResidueEquiv
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (c : LinearMap.ker f256ArtinSchreier) :
    F256 ≃+* GlobalPlace.residueField (splitAbovePlace Q P x hx c) :=
  (splitUpperQuotientConstantsEquiv Q P x hx hregular c).trans
    (splitUpperQuotientResidueEquiv Q P x hx c)
theorem splitUpperConstantsToResidue_bijective
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (c : LinearMap.ker f256ArtinSchreier) :
    Function.Bijective
      (GlobalPlace.constantsToResidue (splitAbovePlace Q P x hx c)) := by
  let e := splitUpperAbstractResidueEquiv Q P x hx hregular c
  letI : Finite (GlobalPlace.residueField (splitAbovePlace Q P x hx c)) :=
    Finite.of_equiv F256 e.toEquiv
  apply (Nat.bijective_iff_injective_and_card _).2
  refine ⟨(GlobalPlace.constantsToResidue
    (splitAbovePlace Q P x hx c)).injective, ?_⟩
  exact Nat.card_congr e.toEquiv
noncomputable def splitUpperConstantsEquiv
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (c : LinearMap.ker f256ArtinSchreier) :
    F256 ≃+* GlobalPlace.residueField (splitAbovePlace Q P x hx c) :=
  RingEquiv.ofBijective
    (GlobalPlace.constantsToResidue (splitAbovePlace Q P x hx c))
    (splitUpperConstantsToResidue_bijective Q P x hx hregular c)
noncomputable def splitUpperRationalPlace
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (c : LinearMap.ker f256ArtinSchreier) :
    RationalPlace F256 (StepField P x hx) where
  place := splitAbovePlace Q P x hx c
  constantsEquiv := splitUpperConstantsEquiv Q P x hx hregular c
  constantsEquiv_apply _ := rfl
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


