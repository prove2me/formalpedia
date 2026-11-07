-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
-- name    : QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T03:02:48.752083+00:00
-- url     : https://prove2.me/theorems/633aee9d-f77c-4493-aa0f-a90cd6c70c01
-- title:
--   LPSTheta Eisenstein Correction
-- statement:
--   Definitions and structural lemmas for LPSTheta Eisenstein Correction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCorrection.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
noncomputable def lpsThetaEisensteinTwoWeight (a : Fin 5) : ℂ :=
  ![1,-(3/2),5/2,0,-2] a
noncomputable def lpsThetaEisensteinPrimeWeight (q : ℕ) (b : Fin 3) : ℂ :=
  ![1,-((q:ℂ)+1)/(q:ℂ),(q:ℂ)] b
noncomputable def lpsThetaEisensteinChi4Weight (q : ℕ) (b : Fin 3) : ℂ :=
  ![-1,(q:ℂ)+1,-(q:ℂ)^3] b
noncomputable def lpsThetaEisensteinQuadraticWeight (q : ℕ) [Fact q.Prime] (a : Fin 5) : ℂ :=
  ![-1,3*lpsQuadraticE2Character q (2:ZMod q),-10,0,32] a
noncomputable def lpsThetaEisensteinNormalization (q : ℕ) : ℂ :=
  (24*(q:ℂ)*((q:ℂ)^2-1))⁻¹
noncomputable def lpsThetaEisensteinCorrection (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    ModularForm (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) 2 :=
  lpsThetaEisensteinNormalization q •
    ((∑ a : Fin 5,∑ b : Fin 3,
      (lpsThetaEisensteinTwoWeight a*lpsThetaEisensteinPrimeWeight q b) •
        lpsE2DifferenceThetaBasis q a b) +
      (∑ b : Fin 3,lpsThetaEisensteinChi4Weight q b • lpsChi4E2ThetaBasis q b) +
      (∑ a : Fin 5,lpsThetaEisensteinQuadraticWeight q a • lpsQuadraticE2ThetaBasis q hq2 a) -
      lpsChi4PrimeE2TwistModularForm q hq2)
noncomputable def lpsModularForm_coefficientLinearMap (N n : ℕ) :
    ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2 →ₗ[ℂ] ℂ where
  toFun f := PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)
  map_add' f g := by
    have hp : (1:ℝ)∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
    have h := congrArg (PowerSeries.coeff n)
      (ModularForm.qExpansion_add (by norm_num : (0:ℝ)<1) hp f g)
    simpa only [FunLike.coe_add,map_add] using h
  map_smul' a f := by
    have hp : (1:ℝ)∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
    have h := congrArg (PowerSeries.coeff n)
      (ModularForm.qExpansion_smul (by norm_num : (0:ℝ)<1) hp a f)
    simpa only [FunLike.coe_smul,PowerSeries.coeff_smul,smul_eq_mul,RingHom.id_apply] using h
noncomputable def lpsThetaEisensteinCorrectionCoefficient (q : ℕ) [Fact q.Prime] (n : ℕ) : ℂ :=
  lpsThetaEisensteinNormalization q *
    ((∑ a : Fin 5,∑ b : Fin 3,
      (lpsThetaEisensteinTwoWeight a*lpsThetaEisensteinPrimeWeight q b) *
        lpsE2DifferenceCoefficient (2^a.val*q^b.val) n) +
      (∑ b : Fin 3,lpsThetaEisensteinChi4Weight q b *
        (if q^b.val∣n then -24*(ArithmeticFunction.sigma 1 (n/q^b.val):ℂ)*
          lpsChi4E2Character ((n/q^b.val:ℕ):ZMod 4) else 0)) +
      (∑ a : Fin 5,lpsThetaEisensteinQuadraticWeight q a *
        (if 2^a.val∣n then -24*(ArithmeticFunction.sigma 1 (n/2^a.val):ℂ)*
          lpsQuadraticE2Character q ((n/2^a.val:ℕ):ZMod q) else 0)) -
      (-24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsQuadraticE2Character q (n:ZMod q)*lpsChi4E2Character (n:ZMod 4)))
end QEC.Coding.TannerLiftedProduct


