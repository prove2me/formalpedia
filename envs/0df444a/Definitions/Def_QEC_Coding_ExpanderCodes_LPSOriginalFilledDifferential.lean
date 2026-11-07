-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledDifferential
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalFilledDifferential
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T02:05:23.702856+00:00
-- url     : https://prove2.me/theorems/6a940655-038b-403b-bfe6-96c865826a4a
-- title:
--   LPSOriginal Filled Differential
-- statement:
--   Definitions and structural lemmas for LPSOriginal Filled Differential, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledDifferential.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialGluing
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspQCoefficient_zero_add
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspQCoefficient_zero_smul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCoordinateCoefficient_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCoordinateCoefficient_cocycle
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspChart_cusp
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold
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
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section
def lpsOriginalFilledDifferential (N : ℕ) [NeZero N] (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    ∀x : LPSOriginalFilledCurve N, TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  exact fun x => ContinuousLinearMap.mul ℂ ℂ
    (lpsOriginalFilledCoordinateCoefficient N f x (chartAt ℂ x x))
lemma lpsOriginalFilledDifferential_inCoordinates (N : ℕ) [NeZero N]
    (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (x y : LPSOriginalFilledCurve N)
    (hy : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      y∈(chartAt ℂ x).source) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ)) ℂ
      (Bundle.Trivial (LPSOriginalFilledCurve N) ℂ) x y x y
      (lpsOriginalFilledDifferential N hN f y)=
        ContinuousLinearMap.mul ℂ ℂ
          (lpsOriginalFilledCoordinateCoefficient N f x (chartAt ℂ x y)) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  have hz : chartAt ℂ x y∈((chartAt ℂ x).symm.trans (chartAt ℂ y)).source := by
    change chartAt ℂ x y∈(chartAt ℂ x).target ∧
      (chartAt ℂ x).symm (chartAt ℂ x y)∈(chartAt ℂ y).source
    exact ⟨(chartAt ℂ x).map_source hy,by rw [(chartAt ℂ x).left_inv hy];exact mem_chart_source ℂ y⟩
  have hk := lpsOriginalFilledCoordinateCoefficient_cocycle N hN f x y
    (chartAt ℂ x y) hz
  have he : ((chartAt ℂ x).symm.trans (chartAt ℂ y)) (chartAt ℂ x y)=chartAt ℂ y y := by
    rw [OpenPartialHomeomorph.trans_apply,(chartAt ℂ x).left_inv hy]
  dsimp only at hk
  rw [he] at hk
  have ht : (trivializationAt ℂ (Bundle.Trivial (LPSOriginalFilledCurve N) ℂ) x).continuousLinearMapAt ℂ y=
      ContinuousLinearMap.id ℂ ℂ := Bundle.Trivial.continuousLinearMapAt_trivialization ℂ _ ℂ y
  rw [ContinuousLinearMap.inCoordinates,ht,ContinuousLinearMap.id_comp,
    TangentBundle.symmL_trivializationAt_eq_core hy,tangentBundleCore_coordChange_achart]
  have heq : extChartAt 𝓘(ℂ) y ∘ (extChartAt 𝓘(ℂ) x).symm=
      (((chartAt ℂ x).symm.trans (chartAt ℂ y)) : ℂ→ℂ) := rfl
  rw [heq]
  simp only [modelWithCornersSelf_coe,Set.range_id,fderivWithin_univ]
  change (ContinuousLinearMap.mul ℂ ℂ
    (lpsOriginalFilledCoordinateCoefficient N f y (chartAt ℂ y y))).comp
      (fderiv ℂ (((chartAt ℂ x).symm.trans (chartAt ℂ y)) : ℂ→ℂ) (chartAt ℂ x y))=
      ContinuousLinearMap.mul ℂ ℂ (lpsOriginalFilledCoordinateCoefficient N f x (chartAt ℂ x y))
  apply ContinuousLinearMap.ext
  intro v
  change lpsOriginalFilledCoordinateCoefficient N f y (chartAt ℂ y y) *
    (fderiv ℂ (((chartAt ℂ x).symm.trans (chartAt ℂ y)) : ℂ→ℂ) (chartAt ℂ x y)) v=
      lpsOriginalFilledCoordinateCoefficient N f x (chartAt ℂ x y) * v
  rw [fderiv_eq_deriv_mul]
  rw [←mul_assoc,hk]
lemma lpsOriginalFilledDifferential_contMDiff (N : ℕ) [NeZero N]
    (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ,ℂ→L[ℂ]ℂ)) ω
      (fun x : LPSOriginalFilledCurve N => Bundle.TotalSpace.mk' (ℂ→L[ℂ]ℂ)
        (E:=fun y : LPSOriginalFilledCurve N =>
          TangentSpace 𝓘(ℂ) y →L[ℂ] Bundle.Trivial (LPSOriginalFilledCurve N) ℂ y)
        x (lpsOriginalFilledDifferential N hN f x)) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  intro x
  apply (contMDiffAt_hom_bundle _).mpr
  refine ⟨contMDiffAt_id,?_⟩
  have ha := lpsOriginalFilledCoordinateCoefficient_analytic N hN f x
    (chartAt ℂ x x) ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
  have hc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x) x :=
    contMDiffAt_extChartAt (I:=𝓘(ℂ))
  have hK : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (fun y => lpsOriginalFilledCoordinateCoefficient N f x (chartAt ℂ x y)) x :=
    ha.contDiffAt.contMDiffAt.comp x hc
  have hm := (ContinuousLinearMap.mul ℂ ℂ).contMDiffAt (n:=ω) |>.comp x hK
  apply hm.congr_of_eventuallyEq
  have hn : ∀ᶠ y in 𝓝 x, y∈(chartAt ℂ x).source :=
    (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
  filter_upwards [hn] with y hy
  exact lpsOriginalFilledDifferential_inCoordinates N hN f x y hy
def lpsOriginalFilledHolomorphicDifferential (N : ℕ) [NeZero N] (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    ContMDiffSection 𝓘(ℂ) (ℂ→L[ℂ]ℂ) ω
      (fun x : LPSOriginalFilledCurve N =>
        TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial (LPSOriginalFilledCurve N) ℂ x) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact ⟨lpsOriginalFilledDifferential N hN f,
    lpsOriginalFilledDifferential_contMDiff N hN f⟩
lemma lpsOriginalFilledDifferential_add (N : ℕ) [NeZero N] (hN : 4∣N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsOriginalFilledDifferential N hN (f+g)=
      lpsOriginalFilledDifferential N hN f+lpsOriginalFilledDifferential N hN g := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  funext x
  cases x with
  | inl y =>
    change ContinuousLinearMap.mul ℂ ℂ ((f+g) (UpperHalfPlane.ofComplex
      (lpsOriginalFilledInteriorChart N hN y (Sum.inl y))))=_
    simp only [FunLike.coe_add,Pi.add_apply]
    exact map_add (ContinuousLinearMap.mul ℂ ℂ) _ _
  | inr c =>
    change ContinuousLinearMap.mul ℂ ℂ (lpsOriginalCuspQCoefficient N (f+g)
      (lpsOriginalCuspRepresentative N c) (lpsOriginalFilledCuspChart N c (Sum.inr c)))=_
    rw [lpsOriginalFilledCuspChart_cusp,lpsOriginalCuspQCoefficient_zero_add]
    rw [map_add]
    change ContinuousLinearMap.mul ℂ ℂ (lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N c) 0)+
      ContinuousLinearMap.mul ℂ ℂ (lpsOriginalCuspQCoefficient N g (lpsOriginalCuspRepresentative N c) 0)=
      ContinuousLinearMap.mul ℂ ℂ (lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N c)
        (lpsOriginalFilledCuspChart N c (Sum.inr c)))+
      ContinuousLinearMap.mul ℂ ℂ (lpsOriginalCuspQCoefficient N g (lpsOriginalCuspRepresentative N c)
        (lpsOriginalFilledCuspChart N c (Sum.inr c)))
    rw [lpsOriginalFilledCuspChart_cusp]
lemma lpsOriginalFilledDifferential_smul (N : ℕ) [NeZero N] (hN : 4∣N)
    (c : ℂ) (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsOriginalFilledDifferential N hN (c • f)=
      c • lpsOriginalFilledDifferential N hN f := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  funext x
  cases x with
  | inl y =>
    change ContinuousLinearMap.mul ℂ ℂ ((c • f) (UpperHalfPlane.ofComplex
      (lpsOriginalFilledInteriorChart N hN y (Sum.inl y))))=_
    simp only [FunLike.coe_smul,Pi.smul_apply]
    exact map_smul (ContinuousLinearMap.mul ℂ ℂ) c _
  | inr d =>
    change ContinuousLinearMap.mul ℂ ℂ (lpsOriginalCuspQCoefficient N (c • f)
      (lpsOriginalCuspRepresentative N d) (lpsOriginalFilledCuspChart N d (Sum.inr d)))=_
    rw [lpsOriginalFilledCuspChart_cusp,lpsOriginalCuspQCoefficient_zero_smul]
    change ContinuousLinearMap.mul ℂ ℂ (c • lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N d) 0)=_
    rw [map_smul]
    change c • ContinuousLinearMap.mul ℂ ℂ (lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N d) 0)=
      c • ContinuousLinearMap.mul ℂ ℂ (lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N d)
        (lpsOriginalFilledCuspChart N d (Sum.inr d)))
    rw [lpsOriginalFilledCuspChart_cusp]
def lpsOriginalFilledDifferentialLinearMap (N : ℕ) [NeZero N] (hN : 4∣N) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2 →ₗ[ℂ]
      ContMDiffSection 𝓘(ℂ) (ℂ→L[ℂ]ℂ) ω
        (fun x : LPSOriginalFilledCurve N =>
          TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial (LPSOriginalFilledCurve N) ℂ x) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  refine { toFun:=lpsOriginalFilledHolomorphicDifferential N hN
           map_add':=?_
           map_smul':=?_ }
  · intro f g
    apply ContMDiffSection.ext
    intro x
    exact congrFun (lpsOriginalFilledDifferential_add N hN f g) x
  · intro c f
    apply ContMDiffSection.ext
    intro x
    exact congrFun (lpsOriginalFilledDifferential_smul N hN c f) x
end
end QEC.Coding.TannerLiftedProduct


