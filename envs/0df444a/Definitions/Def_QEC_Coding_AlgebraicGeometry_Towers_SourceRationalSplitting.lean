-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRationalSplitting
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceRationalSplitting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:32:11.117004+00:00
-- url     : https://prove2.me/theorems/c48d02d2-701e-4dd5-97f7-14f3540a9933
-- title:
--   Source Rational Splitting
-- statement:
--   Definitions and structural lemmas for Source Rational Splitting, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceRationalSplitting.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplittingIdeals
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceSplitIntegralCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplit_inertiaDegIn_eq_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepResidualPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceSplitIntegralCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepResidualPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
noncomputable def sourceSplitUpperHeightOne
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier) :
    IsDedekindDomain.HeightOneSpectrum (SourceSplitIntegralClosure Q P x hx) := by
  let R := (sourceSplitUpperPrime Q P x hx c).1
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
theorem sourceSplitUpperHeightOne_asIdeal
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier) :
    (sourceSplitUpperHeightOne Q P x hx c).asIdeal =
      (sourceSplitUpperPrime Q P x hx c).1 :=
  rfl
noncomputable def sourceSplitAbovePlace
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier) :
    GlobalPlace F256 (SourceStepField P x hx) where
  valuation := (sourceSplitUpperHeightOne Q P x hx c).valuation
    (SourceStepField P x hx)
  normalized := (sourceSplitUpperHeightOne Q P x hx c).valuation_surjective
    (SourceStepField P x hx)
theorem sourceSplitUpperPrime_inertiaDeg_eq_one
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    (IsLocalRing.maximalIdeal Q.place.valuationRing).inertiaDeg'
        (sourceSplitUpperPrime Q P x hx c).1 = 1 := by
  let O := Q.place.valuationRing
  let S := SourceSplitIntegralClosure Q P x hx
  let L := SourceStepField P x hx
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let R : Ideal S := (sourceSplitUpperPrime Q P x hx c).1
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
    _ = 1 := sourceSplit_inertiaDegIn_eq_one
      Q P x hx hregular hsplit
noncomputable def sourceSplitUpperQuotientConstantsEquiv
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    F256 ≃+*
      (SourceSplitIntegralClosure Q P x hx ⧸
        (sourceSplitUpperPrime Q P x hx c).1) := by
  let O := Q.place.valuationRing
  let S := SourceSplitIntegralClosure Q P x hx
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let R : Ideal S := (sourceSplitUpperPrime Q P x hx c).1
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
    exact sourceSplitUpperPrime_inertiaDeg_eq_one
      Q P x hx hregular hsplit c
  let e : (O ⧸ m) ≃+* (S ⧸ R) :=
    RingEquiv.ofBijective (algebraMap (O ⧸ m) (S ⧸ R))
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfinrank)
  exact Q.constantsEquiv.trans e
noncomputable def sourceSplitUpperQuotientResidueEquiv
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier) :
    (SourceSplitIntegralClosure Q P x hx ⧸
        (sourceSplitUpperPrime Q P x hx c).1) ≃+*
      GlobalPlace.residueField (sourceSplitAbovePlace Q P x hx c) := by
  let S := SourceSplitIntegralClosure Q P x hx
  let L := SourceStepField P x hx
  let H := sourceSplitUpperHeightOne Q P x hx c
  letI : H.asIdeal.IsMaximal := inferInstance
  let e₁ : (S ⧸ H.asIdeal) ≃+*
      IsLocalRing.ResidueField (H.valuationSubringAtPrime L) :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal H.asIdeal
      (H.valuationSubringAtPrime L)
  let e₂ : H.valuationSubringAtPrime L ≃+*
      (H.valuation L).valuationSubring := by
    rw [H.valuationSubringAtPrime_eq_valuationSubring]
  exact e₁.trans (IsLocalRing.ResidueField.mapEquiv e₂)
noncomputable def sourceSplitUpperAbstractResidueEquiv
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    F256 ≃+* GlobalPlace.residueField (sourceSplitAbovePlace Q P x hx c) :=
  (sourceSplitUpperQuotientConstantsEquiv
      Q P x hx hregular hsplit c).trans
    (sourceSplitUpperQuotientResidueEquiv Q P x hx c)
theorem sourceSplitUpperConstantsToResidue_bijective
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    Function.Bijective
      (GlobalPlace.constantsToResidue (sourceSplitAbovePlace Q P x hx c)) := by
  let e := sourceSplitUpperAbstractResidueEquiv
    Q P x hx hregular hsplit c
  letI : Finite (GlobalPlace.residueField
      (sourceSplitAbovePlace Q P x hx c)) :=
    Finite.of_equiv F256 e.toEquiv
  apply (Nat.bijective_iff_injective_and_card _).2
  refine ⟨(GlobalPlace.constantsToResidue
    (sourceSplitAbovePlace Q P x hx c)).injective, ?_⟩
  exact Nat.card_congr e.toEquiv
noncomputable def sourceSplitUpperConstantsEquiv
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    F256 ≃+* GlobalPlace.residueField (sourceSplitAbovePlace Q P x hx c) :=
  RingEquiv.ofBijective
    (GlobalPlace.constantsToResidue (sourceSplitAbovePlace Q P x hx c))
    (sourceSplitUpperConstantsToResidue_bijective
      Q P x hx hregular hsplit c)
noncomputable def sourceSplitUpperRationalPlace
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    RationalPlace F256 (SourceStepField P x hx) where
  place := sourceSplitAbovePlace Q P x hx c
  constantsEquiv := sourceSplitUpperConstantsEquiv
    Q P x hx hregular hsplit c
  constantsEquiv_apply _ := rfl
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


