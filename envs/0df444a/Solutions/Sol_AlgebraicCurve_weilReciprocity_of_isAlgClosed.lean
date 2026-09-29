-- Prove2me | solution 1 for AlgebraicCurve.weilReciprocity_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/36bcd802-991d-5f27-888b-59f98e8e5cf9

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_Mathlib_FieldTheory_RatFuncImperfectionDegree
import Theorems.Thm_AlgebraicCurve_weilReciprocity
import Theorems.Thm_AlgebraicCurve_weilReciprocity_algebraMap_of_isSeparable
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_weilReciprocity
import Theorems.Thm_AlgebraicCurve_FunctionField_finite_of_ratFuncAlgHom
import Theorems.Thm_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_Algebra_IsSeparable_of_finrank_fieldRange_frobenius_eq
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Divisor_evalFun_add
import Theorems.Thm_AlgebraicCurve_Divisor_evalFun_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_weilReciprocity_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul"
p2m_attr_erase "simp" "ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

open AlgebraicCurve

namespace WRpAux

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem finsupp_prod_zpow_const {c : K} (hc : c ≠ 0) (D : Divisor K F) :
    (D.prod fun _ n => c ^ n) = c ^ (D.sum fun _ n => n) := by
  classical
  unfold Finsupp.prod Finsupp.sum
  induction D.support using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, zpow_add₀ hc, ih]

theorem degree_eq_sum_of_rational (D : Divisor K F)
    (hrat : ∀ v ∈ D.support, Place.IsRational v) :
    Divisor.degree D = D.sum fun _ n => n := by
  unfold Divisor.degree
  rw [Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun v hv => ?_
  rw [AddMonoidHom.mulRight_apply, (AlgebraicCurve.Place.isRational_iff_deg_eq_one v).1 (hrat v hv),
    Nat.cast_one, mul_one]

theorem evalFun_nsmul (f : F) (D : Divisor K F) (hD : ∀ v ∈ D.support, Place.evalAt v f ≠ 0) (n : ℕ) :
    Divisor.evalFun f (n • D) = Divisor.evalFun f D ^ n := by
  induction n with
  | zero => rw [zero_smul, Divisor.evalFun_zero, pow_zero]
  | succ n ih =>
    rw [add_smul, one_smul, pow_succ, ← ih]
    refine AlgebraicCurve.Divisor.evalFun_add f (fun v hv => hD v (Finsupp.support_smul hv)) hD

theorem evalFun_pow (g : F) (D : Divisor K F) (hrat : ∀ v ∈ D.support, Place.IsRational v)
    (hg : ∀ v ∈ D.support, g ∈ v.toValuationSubring) (n : ℕ) :
    Divisor.evalFun (g ^ n) D = Divisor.evalFun g D ^ n := by
  classical
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, Divisor.evalFun_def]
    exact Finset.prod_eq_one fun v _ => by rw [Place.evalAt_one, one_zpow]
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih]
    exact AlgebraicCurve.Divisor.evalFun_mul hrat (fun v hv => pow_mem (hg v hv) n) hg

theorem ratFuncAlgHom_fieldRange_eq_adjoin (φ : RatFunc K →ₐ[K] F) :
    φ.fieldRange = IntermediateField.adjoin K ({φ RatFunc.X} : Set F) := by
  have key : ∀ p : Polynomial K,
      φ (algebraMap (Polynomial K) (RatFunc K) p) = Polynomial.aeval (φ RatFunc.X) p := by
    intro p
    have h2 : φ.comp (IsScalarTower.toAlgHom K (Polynomial K) (RatFunc K))
        = Polynomial.aeval (φ RatFunc.X) := by
      apply Polynomial.algHom_ext
      simp [RatFunc.algebraMap_X]
    exact DFunLike.congr_fun h2 p
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    apply RatFunc.induction_on z
    intro p q hq
    show φ (algebraMap (Polynomial K) (RatFunc K) p
        / algebraMap (Polynomial K) (RatFunc K) q)
      ∈ IntermediateField.adjoin K ({φ RatFunc.X} : Set F)
    rw [map_div₀, key, key]
    have hmem : ∀ r : Polynomial K,
        Polynomial.aeval (φ RatFunc.X) r
          ∈ IntermediateField.adjoin K ({φ RatFunc.X} : Set F) := by
      intro r
      exact IntermediateField.algebra_adjoin_le_adjoin K _
        (Polynomial.aeval_mem_adjoin_singleton K _)
    exact div_mem (hmem p) (hmem q)
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact ⟨RatFunc.X, rfl⟩

end WRpAux

open WRpAux

theorem solution (K F : Type*) [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F] [HasPrincipalDivisors K F] : WeilReciprocity K F := by
  classical

  obtain ⟨p, hpK⟩ := CharP.exists K
  by_cases hp0 : p = 0
  · subst hp0
    haveI : CharZero K := CharP.charP_to_charZero K
    exact AlgebraicCurve.weilReciprocity K F
  haveI hpfact : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero K p).resolve_right hp0⟩
  haveI : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  haveI : CharP (RatFunc K) p := charP_of_injective_algebraMap (algebraMap K (RatFunc K)).injective p
  haveI : PerfectField K := IsAlgClosed.perfectField K

  have hdeg : Module.finrank (frobenius F p).fieldRange F = p := by
    rw [finrank_fieldRange_frobenius_eq_of_finiteDimensional (RatFunc K) F p,
      RatFunc.finrank_fieldRange_frobenius K p]

  have hratAll : ∀ w : Place K F, w.IsRational := fun w =>
    AlgebraicCurve.Place.isRational_of_isAlgClosed w
  have hratP1 : ∀ v : Place K (RatFunc K), v.IsRational := fun v =>
    (AlgebraicCurve.Place.isRational_iff_deg_eq_one v).2
      (AlgebraicCurve.RationalFunctionField.deg_eq_one_of_isAlgClosed K v)

  have hconstCase : ∀ (f : F) (c : K) (Df Dg : Divisor K F), f ≠ 0 → algebraMap K F c ≠ 0 →
      (∀ v : Place K F, Df v = v.ord f) → (∀ v : Place K F, Dg v = v.ord (algebraMap K F c)) →
      (∀ v ∈ Df.support, Place.IsRational v) →
      Divisor.evalFun f Dg = Divisor.evalFun (algebraMap K F c) Df := by
    intro f c Df Dg hf hg hDf hDg hratf
    have hc : c ≠ 0 := fun h => hg (by rw [h, map_zero])
    have hDg0 : Dg = 0 := by
      ext v
      rw [hDg v, AlgebraicCurve.Place.ord_algebraMap, Finsupp.coe_zero, Pi.zero_apply]
    obtain ⟨D', hD', hdeg'⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) f hf
    have hDfD' : Df = D' := by
      ext v; rw [hDf v, hD' v]
    have hsum : (Df.sum fun _ n => n) = 0 := by
      rw [← degree_eq_sum_of_rational Df hratf, hDfD', hdeg']
    rw [hDg0, Divisor.evalFun_zero, Divisor.evalFun_def]
    rw [show (∏ v ∈ Df.support, Place.evalAt v (algebraMap K F c) ^ Df v)
        = Df.prod fun _ n => c ^ n from
      Finset.prod_congr rfl fun v _ => by rw [AlgebraicCurve.Place.evalAt_algebraMap]]
    rw [finsupp_prod_zpow_const hc, hsum, zpow_zero]

  have hsepCase : ∀ (f g : F) (Df Dg : Divisor K F), f ≠ 0 → g ≠ 0 →
      (∀ v : Place K F, Df v = v.ord f) → (∀ v : Place K F, Dg v = v.ord g) → (∀ v : Place K F, v.ord f = 0 ∨ v.ord g = 0) →
      g ∉ Set.range (algebraMap K F) → g ∉ (frobenius F p).fieldRange →
      Divisor.evalFun f Dg = Divisor.evalFun g Df := by
    intro f g Df Dg hf hg hDf hDg hdisj hconst hfrob
    obtain ⟨φ, hφ⟩ := AlgebraicCurve.FunctionField.exists_ratFuncAlgHom_apply_X_eq hconst
    have finφ : @Module.Finite (RatFunc K) F _ _ (φ.toRingHom.toAlgebra).toModule :=
      AlgebraicCurve.FunctionField.finite_of_ratFuncAlgHom φ
    let algφ : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
    have stφ : @IsScalarTower K (RatFunc K) F _ algφ.toSMul _ :=
      @IsScalarTower.of_algebraMap_eq K (RatFunc K) F _ _ _ _ algφ _ fun x => (φ.commutes x).symm
    have hXg : @algebraMap (RatFunc K) F _ _ algφ RatFunc.X = g := hφ
    have sepφ : @Algebra.IsSeparable (RatFunc K) F _ _ algφ :=
      @Algebra.IsSeparable.of_finrank_fieldRange_frobenius_eq (RatFunc K) F _ _ algφ finφ p _ _ hdeg
        RatFunc.X (by rw [hXg]; exact hfrob)
    haveI : HasPrincipalDivisors K (RatFunc K) :=
      AlgebraicCurve.RationalFunctionField.hasPrincipalDivisors K
    have key := @AlgebraicCurve.weilReciprocity_algebraMap_of_isSeparable K (RatFunc K) F _ _ _ _ _ algφ stφ finφ sepφ
      _ _ (AlgebraicCurve.RationalFunctionField.weilReciprocity K) f RatFunc.X hf RatFunc.X_ne_zero
      Df Dg hDf (fun w => by rw [hDg w, ← hXg]) (fun w => by rw [← hXg] at hdisj; exact hdisj w)
      (fun w _ => hratAll w) hratP1 (fun v _ w _ => hratAll w)
    rw [hXg] at key
    exact key

  have main : ∀ (m : ℕ) (f g : F) (Df Dg : Divisor K F), f ≠ 0 → g ≠ 0 →
      (∀ v : Place K F, Df v = v.ord f) → (∀ v : Place K F, Dg v = v.ord g) → (∀ v : Place K F, v.ord f = 0 ∨ v.ord g = 0) →
      (∃ v, Dg v ≠ 0 ∧ (Dg v).natAbs ≤ m) →
      Divisor.evalFun f Dg = Divisor.evalFun g Df := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m IH =>
      intro f g Df Dg hf hg hDf hDg hdisj hm
      obtain ⟨v₀, hv₀, hv₀m⟩ := hm

      have hconst : g ∉ Set.range (algebraMap K F) := by
        rintro ⟨c, rfl⟩
        exact hv₀ (by rw [hDg v₀, AlgebraicCurve.Place.ord_algebraMap])
      by_cases hfrob : g ∈ (frobenius F p).fieldRange
      ·
        obtain ⟨g₁, hg₁g⟩ := RingHom.mem_fieldRange.1 hfrob
        rw [frobenius_def] at hg₁g
        subst hg₁g
        have hg₁ : g₁ ≠ 0 := by rintro rfl; exact hg (by rw [zero_pow hpfact.out.ne_zero])
        have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hpfact.out.ne_zero
        have hordp : ∀ v : Place K F, v.ord (g₁ ^ p) = (p : ℤ) * v.ord g₁ := by
          intro v; rw [← zpow_natCast, Place.ord_zpow]

        let Dg₁ : Divisor K F := Finsupp.mapRange (fun n => n / (p : ℤ)) (by simp) Dg
        have hDg₁ : ∀ v, Dg₁ v = v.ord g₁ := by
          intro v
          show Dg v / (p : ℤ) = v.ord g₁
          rw [hDg v, hordp v, Int.mul_ediv_cancel_left _ hpz]
        have hDgp : Dg = p • Dg₁ := by
          ext v
          rw [Finsupp.smul_apply, hDg v, hordp v, ← hDg₁ v, nsmul_eq_mul]
        have hdisj₁ : ∀ v : Place K F, v.ord f = 0 ∨ v.ord g₁ = 0 := by
          intro v
          rcases hdisj v with h | h
          · exact Or.inl h
          · right; rw [hordp v] at h; exact (mul_eq_zero.1 h).resolve_left hpz

        have hv₀' : Dg₁ v₀ ≠ 0 := by
          intro h; apply hv₀; rw [hDgp, Finsupp.smul_apply, h, smul_zero]
        have hlt : (Dg₁ v₀).natAbs < m := by
          have h1 : (Dg v₀).natAbs = p * (Dg₁ v₀).natAbs := by
            rw [hDgp, Finsupp.smul_apply, nsmul_eq_mul, Int.natAbs_mul, Int.natAbs_natCast]
          have h2 : (Dg₁ v₀).natAbs < p * (Dg₁ v₀).natAbs :=
            lt_mul_left (Int.natAbs_pos.2 hv₀') hpfact.out.one_lt
          omega
        have IH' := IH _ hlt f g₁ Df Dg₁ hf hg₁ hDf hDg₁ hdisj₁ ⟨v₀, hv₀', le_rfl⟩

        have hfD : ∀ v ∈ Dg₁.support, Place.evalAt v f ≠ 0 := by
          intro v hv
          have hvg : v.ord g₁ ≠ 0 := by rw [← hDg₁ v]; exact Finsupp.mem_support_iff.1 hv
          exact AlgebraicCurve.Place.evalAt_ne_zero v (hratAll v) hf ((hdisj₁ v).resolve_right hvg)
        have hgD : ∀ v ∈ Df.support, g₁ ∈ v.toValuationSubring := by
          intro v hv
          have hvf : v.ord f ≠ 0 := by rw [← hDf v]; exact Finsupp.mem_support_iff.1 hv
          exact AlgebraicCurve.Place.mem_of_ord_nonneg v hg₁ (le_of_eq ((hdisj₁ v).resolve_left hvf).symm)
        rw [hDgp, evalFun_nsmul f Dg₁ hfD p, evalFun_pow g₁ Df (fun v _ => hratAll v) hgD p, IH']
      · exact hsepCase f g Df Dg hf hg hDf hDg hdisj hconst hfrob

  intro f g Df Dg hf hg hDf hDg hdisj hratf hratg
  by_cases hDg0 : ∀ v, Dg v = 0
  ·
    have hord : ∀ v : Place K F, v.ord g = 0 := fun v => by rw [← hDg v]; exact hDg0 v

    let φ₀ : RatFunc K →ₐ[K] F := IsScalarTower.toAlgHom K (RatFunc K) F
    have hj : Transcendental K (φ₀ RatFunc.X) := by
      show Transcendental K (algebraMap (RatFunc K) F RatFunc.X)
      exact (transcendental_algebraMap_iff (algebraMap (RatFunc K) F).injective).2 RatFunc.transcendental_X
    haveI : FiniteDimensional (IntermediateField.adjoin K ({φ₀ RatFunc.X} : Set F)) F := by
      rw [← ratFuncAlgHom_fieldRange_eq_adjoin φ₀]
      let ε : RatFunc K ≃ₐ[K] φ₀.fieldRange := AlgEquiv.ofInjectiveField φ₀
      letI : Algebra (RatFunc K) φ₀.fieldRange := ε.toAlgHom.toRingHom.toAlgebra
      haveI : IsScalarTower (RatFunc K) φ₀.fieldRange F :=
        IsScalarTower.of_algebraMap_eq fun z => rfl
      exact Module.Finite.of_restrictScalars_finite (RatFunc K) φ₀.fieldRange F
    obtain ⟨c, hc⟩ := RingHom.mem_range.mp
      (AlgebraicCurve.Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed (φ₀ RatFunc.X) hj hord)
    subst hc
    exact hconstCase f c Df Dg hf hg hDf hDg hratf
  · push_neg at hDg0
    obtain ⟨v₀, hv₀⟩ := hDg0
    exact main _ f g Df Dg hf hg hDf hDg hdisj ⟨v₀, hv₀, le_rfl⟩

end S_AlgebraicCurve_weilReciprocity_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicCurve_weilReciprocity_of_isAlgClosed (solution)
