-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationStalkDifferentialComparison
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalNormalizationStalkDifferentialComparison
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:53:04.642199+00:00
-- url     : https://prove2.me/theorems/2a4a1364-b05b-42e4-b659-96209ae84398
-- title:
--   LPSOriginal Normalization Stalk Differential Comparison
-- statement:
--   Definitions and structural lemmas for LPSOriginal Normalization Stalk Differential Comparison, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationStalkDifferentialComparison.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_StalkScalars
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_KaehlerMapImage
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeLocalDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalRegularDifferentialComparison
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_scalarRingEquiv_transport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeStalkScalar_chart
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalGluedChartMap_openImmersion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityStalkMeromorphicValuationRingEquiv_algebraMap
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv_tmulValue
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv_tmulValue
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizationChart_order_cover
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizationCurveSpecPoint_infinity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizationCurveSpecPoint_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroStalkMeromorphicValuationRingEquiv_algebraMap
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped TensorProduct
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance _p2m_local_instance_777eb8c026_29 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "IC0" => lpsOriginalComplexNormalZeroChart N hpos
local notation "ICI" => lpsOriginalComplexNormalInfinityChart N hpos
local instance _p2m_local_instance_777eb8c026_36 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance _p2m_local_instance_777eb8c026_37 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance _p2m_local_instance_777eb8c026_38 : IsScalarTower ℂ J K := .of_algebraMap_eq' rfl
local instance _p2m_local_instance_777eb8c026_39 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
lemma lpsOriginalZeroConstant_value (c : ℂ) :
    (lpsOriginalComplexZeroConstantRingHom N hpos c).val = algebraMap ℂ K c := by
  rw [lpsOriginalComplexZeroConstantChartRingHom_apply]
  change (lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv N hpos (c ⊗ₜ[ℤ] 1)).val = _
  simpa only [OneMemClass.coe_one,map_one,mul_one] using
    lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv_tmulValue N hpos c 1
lemma lpsOriginalInfinityConstant_value (c : ℂ) :
    (lpsOriginalComplexInfinityConstantRingHom N hpos c).val = algebraMap ℂ K c := by
  rw [lpsOriginalComplexInfinityConstantChartRingHom_apply]
  change (lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv N hpos (c ⊗ₜ[ℤ] 1)).val = _
  simpa only [OneMemClass.coe_one,map_one,mul_one] using
    lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv_tmulValue N hpos c 1
lemma lpsOriginalZeroPointStalk_constant (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) (c : ℂ) :
    ((lpsOriginalZeroNormalizationPointLocalRingEquiv N hpos hN x hj)
      (StructureSheaf.toStalk IC0
        ((lpsOriginalZeroNormalizationSpecPoint N hpos hN x hj).base
          (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ))
        (lpsOriginalComplexZeroConstantRingHom N hpos c))).val = algebraMap ℂ K c := by
  change ((lpsOriginalZeroStalkMeromorphicValuationRingEquiv N hpos hN x hj)
    (algebraMap IC0 _ (lpsOriginalComplexZeroConstantRingHom N hpos c))).val = _
  rw [lpsOriginalZeroStalkMeromorphicValuationRingEquiv_algebraMap]
  exact lpsOriginalZeroConstant_value N hpos c
lemma lpsOriginalInfinityPointStalk_constant (x : LPSOriginalFilledCurve N)
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x
      (((algebraMap J K).comp lpsOriginalCanonicalComplexPolynomialFractionMap) Polynomial.X)⁻¹)
    (c : ℂ) :
    ((lpsOriginalInfinityNormalizationPointLocalRingEquiv N hpos hN x hi)
      (StructureSheaf.toStalk ICI
        ((lpsOriginalInfinityNormalizationSpecPoint N hpos hN x hi).base
          (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ))
        (lpsOriginalComplexInfinityConstantRingHom N hpos c))).val = algebraMap ℂ K c := by
  change ((lpsOriginalInfinityStalkMeromorphicValuationRingEquiv N hpos hN x hi)
    (algebraMap ICI _ (lpsOriginalComplexInfinityConstantRingHom N hpos c))).val = _
  rw [lpsOriginalInfinityStalkMeromorphicValuationRingEquiv_algebraMap]
  exact lpsOriginalInfinityConstant_value N hpos c
def lpsOriginalNormalizationStalkStructuralScalar (x : LPSOriginalFilledCurve N) :
    ℂ →+* (lpsOriginalComplexNormalGluedScheme N hpos).presheaf.stalk
      ((lpsOriginalNormalizationCurveSpecPoint N hpos hN x).base
        (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ)) :=
  schemeStalkScalar (.of ℂ) (lpsOriginalComplexNormalGluedScheme N hpos)
    (lpsOriginalComplexNormalGluedToSpecC N hpos)
    ((lpsOriginalNormalizationCurveSpecPoint N hpos hN x).base
      (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ))
lemma lpsOriginalNormalizationStalkStructuralScalar_zero (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) (c : ℂ) :
    ((lpsOriginalNormalizationCurveLocalRingEquiv_zero N hpos hN x hj)
      (lpsOriginalNormalizationStalkStructuralScalar N hpos hN x c)).val = algebraMap ℂ K c := by
  let y := (lpsOriginalZeroNormalizationSpecPoint N hpos hN x hj).base
    (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ)
  let : IsOpenImmersion (lpsOriginalComplexNormalGluedChartMap N hpos false) :=
    lpsOriginalComplexNormalGluedChartMap_openImmersion N hpos false
  let e := (CategoryTheory.asIso
    ((lpsOriginalComplexNormalGluedChartMap N hpos false).stalkMap y)).commRingCatIsoToRingEquiv.trans
    (lpsOriginalZeroNormalizationPointLocalRingEquiv N hpos hN x hj)
  have ht := scalarRingEquiv_transport (.of ℂ)
    (.of ((AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x)).valuationSubring))
    (Spec (.of ℂ) ⟶ lpsOriginalComplexNormalGluedScheme N hpos)
    (fun q => (lpsOriginalComplexNormalGluedScheme N hpos).presheaf.stalk
      (q.base (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ)))
    (fun q => schemeStalkScalar (.of ℂ) (lpsOriginalComplexNormalGluedScheme N hpos)
      (lpsOriginalComplexNormalGluedToSpecC N hpos)
      (q.base (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ)))
    (lpsOriginalNormalizationCurveSpecPoint_zero N hpos hN x hj) e c
  refine (congrArg (fun v => v.val) ht).trans ?_
  change ((lpsOriginalZeroNormalizationPointLocalRingEquiv N hpos hN x hj)
    ((lpsOriginalComplexNormalGluedChartMap N hpos false).stalkMap y
      (schemeStalkScalar (.of ℂ) (lpsOriginalComplexNormalGluedScheme N hpos)
        (lpsOriginalComplexNormalGluedToSpecC N hpos)
        ((lpsOriginalComplexNormalGluedChartMap N hpos false) y) c))).val = _
  have hc := schemeStalkScalar_chart (.of ℂ) (.of IC0)
    (lpsOriginalComplexNormalGluedScheme N hpos)
    (lpsOriginalComplexNormalGluedChartMap N hpos false)
    (lpsOriginalComplexNormalGluedToSpecC N hpos)
    (CommRingCat.ofHom (lpsOriginalComplexZeroConstantRingHom N hpos))
    (lpsOriginalComplexNormalGluedToSpecC_chart N hpos false) y c
  exact (congrArg (fun z => ((lpsOriginalZeroNormalizationPointLocalRingEquiv
    N hpos hN x hj) z).val) hc).trans
      (lpsOriginalZeroPointStalk_constant N hpos hN x hj c)
lemma lpsOriginalNormalizationStalkStructuralScalar_infinity (x : LPSOriginalFilledCurve N)
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x
      (((algebraMap J K).comp lpsOriginalCanonicalComplexPolynomialFractionMap) Polynomial.X)⁻¹)
    (c : ℂ) :
    ((lpsOriginalNormalizationCurveLocalRingEquiv_infinity N hpos hN x hi)
      (lpsOriginalNormalizationStalkStructuralScalar N hpos hN x c)).val = algebraMap ℂ K c := by
  let y := (lpsOriginalInfinityNormalizationSpecPoint N hpos hN x hi).base
    (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ)
  let : IsOpenImmersion (lpsOriginalComplexNormalGluedChartMap N hpos true) :=
    lpsOriginalComplexNormalGluedChartMap_openImmersion N hpos true
  let e := (CategoryTheory.asIso
    ((lpsOriginalComplexNormalGluedChartMap N hpos true).stalkMap y)).commRingCatIsoToRingEquiv.trans
    (lpsOriginalInfinityNormalizationPointLocalRingEquiv N hpos hN x hi)
  have ht := scalarRingEquiv_transport (.of ℂ)
    (.of ((AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x)).valuationSubring))
    (Spec (.of ℂ) ⟶ lpsOriginalComplexNormalGluedScheme N hpos)
    (fun q => (lpsOriginalComplexNormalGluedScheme N hpos).presheaf.stalk
      (q.base (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ)))
    (fun q => schemeStalkScalar (.of ℂ) (lpsOriginalComplexNormalGluedScheme N hpos)
      (lpsOriginalComplexNormalGluedToSpecC N hpos)
      (q.base (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ)))
    (lpsOriginalNormalizationCurveSpecPoint_infinity N hpos hN x hi) e c
  refine (congrArg (fun v => v.val) ht).trans ?_
  change ((lpsOriginalInfinityNormalizationPointLocalRingEquiv N hpos hN x hi)
    ((lpsOriginalComplexNormalGluedChartMap N hpos true).stalkMap y
      (schemeStalkScalar (.of ℂ) (lpsOriginalComplexNormalGluedScheme N hpos)
        (lpsOriginalComplexNormalGluedToSpecC N hpos)
        ((lpsOriginalComplexNormalGluedChartMap N hpos true) y) c))).val = _
  have hc := schemeStalkScalar_chart (.of ℂ) (.of ICI)
    (lpsOriginalComplexNormalGluedScheme N hpos)
    (lpsOriginalComplexNormalGluedChartMap N hpos true)
    (lpsOriginalComplexNormalGluedToSpecC N hpos)
    (CommRingCat.ofHom (lpsOriginalComplexInfinityConstantRingHom N hpos))
    (lpsOriginalComplexNormalGluedToSpecC_chart N hpos true) y c
  exact (congrArg (fun z => ((lpsOriginalInfinityNormalizationPointLocalRingEquiv
    N hpos hN x hi) z).val) hc).trans
      (lpsOriginalInfinityPointStalk_constant N hpos hN x hi c)
lemma lpsOriginalNormalizationStalkStructuralScalar_value (x : LPSOriginalFilledCurve N) (c : ℂ) :
    ((lpsOriginalNormalizationCurveLocalRingEquiv N hpos hN x)
      (lpsOriginalNormalizationStalkStructuralScalar N hpos hN x c)).val = algebraMap ℂ K c := by
  by_cases hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)
  · simp only [lpsOriginalNormalizationCurveLocalRingEquiv,dif_pos hj]
    exact lpsOriginalNormalizationStalkStructuralScalar_zero N hpos hN x hj c
  · simp only [lpsOriginalNormalizationCurveLocalRingEquiv,dif_neg hj]
    exact lpsOriginalNormalizationStalkStructuralScalar_infinity N hpos hN x
      ((lpsOriginalNormalizationChart_order_cover N hpos hN x).resolve_left hj) c
abbrev lpsOriginalNormalizationPointStalk (x : LPSOriginalFilledCurve N) : CommRingCat :=
  (lpsOriginalComplexNormalGluedScheme N hpos).presheaf.stalk
    ((lpsOriginalNormalizationCurveSpecPoint N hpos hN x).base
      (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ))
variable (x : LPSOriginalFilledCurve N)
local notation "St" => lpsOriginalNormalizationPointStalk N hpos hN x
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
local instance _p2m_local_instance_777eb8c026_192 : Algebra ℂ St := (lpsOriginalNormalizationStalkStructuralScalar N hpos hN x).toAlgebra
local instance _p2m_local_instance_777eb8c026_193 : Algebra ℂ V :=
  (lpsOriginalComplexConstantsToMeromorphicValuationRing N hpos hN x).toAlgebra
def lpsOriginalNormalizationStalkValuationComplexAlgEquiv : St ≃ₐ[ℂ] V where
  toRingEquiv := lpsOriginalNormalizationCurveLocalRingEquiv N hpos hN x
  commutes' c := by
    apply Subtype.ext
    change ((lpsOriginalNormalizationCurveLocalRingEquiv N hpos hN x)
      (lpsOriginalNormalizationStalkStructuralScalar N hpos hN x c)).val = algebraMap ℂ K c
    exact lpsOriginalNormalizationStalkStructuralScalar_value N hpos hN x c
def lpsOriginalNormalizationStalkToFieldComplexAlgHom : St →ₐ[ℂ] K where
  toRingHom := (ValuationSubring.subtype V).comp
    (lpsOriginalNormalizationStalkValuationComplexAlgEquiv N hpos hN x).toRingHom
  commutes' c := by
    exact congrArg (fun v : V => v.val)
      ((lpsOriginalNormalizationStalkValuationComplexAlgEquiv N hpos hN x).commutes c)
local instance _p2m_local_instance_777eb8c026_214 : Algebra V K := (ValuationSubring.subtype V).toAlgebra
local instance _p2m_local_instance_777eb8c026_215 : Algebra St V :=
  (lpsOriginalNormalizationStalkValuationComplexAlgEquiv N hpos hN x).toRingHom.toAlgebra
local instance _p2m_local_instance_777eb8c026_217 : Algebra St K := (lpsOriginalNormalizationStalkToFieldComplexAlgHom N hpos hN x).toAlgebra
local instance _p2m_local_instance_777eb8c026_218 : IsScalarTower ℂ St V := .of_algebraMap_eq fun c =>
  ((lpsOriginalNormalizationStalkValuationComplexAlgEquiv N hpos hN x).commutes c).symm
local instance _p2m_local_instance_777eb8c026_220 : IsScalarTower ℂ V K := .of_algebraMap_eq fun c => by rfl
local instance _p2m_local_instance_777eb8c026_221 : IsScalarTower ℂ St K := .of_algebraMap_eq fun c =>
  ((lpsOriginalNormalizationStalkToFieldComplexAlgHom N hpos hN x).commutes c).symm
local instance _p2m_local_instance_777eb8c026_223 : IsScalarTower St V K := .of_algebraMap_eq fun v => by rfl
local instance _p2m_local_instance_777eb8c026_225 : SMulCommClass ℂ V K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (f.val * g) = f.val * (algebraMap ℂ K c * g)
    ring
local instance _p2m_local_instance_777eb8c026_229 : SMulCommClass ℂ St K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (algebraMap St K f * g) =
      algebraMap St K f * (algebraMap ℂ K c * g)
    ring
local instance _p2m_local_instance_777eb8c026_234 : SMulCommClass ℂ St V where
  smul_comm c f g := by
    change algebraMap ℂ V c * (algebraMap St V f * g) =
      algebraMap St V f * (algebraMap ℂ V c * g)
    ring
local instance _p2m_local_instance_777eb8c026_239 : SMulCommClass ℂ K K where
  smul_comm c f g := by
    change algebraMap ℂ K c * (f * g) = f * (algebraMap ℂ K c * g)
    ring
local instance _p2m_local_instance_777eb8c026_243 : SMul K (KaehlerDifferential ℂ K) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance _p2m_local_instance_777eb8c026_245 : Module K (KaehlerDifferential ℂ K) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance _p2m_local_instance_777eb8c026_247 : SMul V (KaehlerDifferential ℂ K) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance _p2m_local_instance_777eb8c026_249 : Module V (KaehlerDifferential ℂ K) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance _p2m_local_instance_777eb8c026_251 : SMul St (KaehlerDifferential ℂ K) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance _p2m_local_instance_777eb8c026_253 : Module St (KaehlerDifferential ℂ K) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance _p2m_local_instance_777eb8c026_255 : SMul St (KaehlerDifferential ℂ V) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ V
local instance _p2m_local_instance_777eb8c026_257 : Module St (KaehlerDifferential ℂ V) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ V
end
end QEC.Coding.TannerLiftedProduct


