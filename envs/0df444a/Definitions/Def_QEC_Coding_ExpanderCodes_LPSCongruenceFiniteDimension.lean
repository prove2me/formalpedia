-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
-- name    : QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:48:47.532229+00:00
-- url     : https://prove2.me/theorems/e23746b4-999a-45d9-8839-28cb84f88a04
-- title:
--   LPSCongruence Finite Dimension
-- statement:
--   Definitions and structural lemmas for LPSCongruence Finite Dimension, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceFiniteDimension.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.LinearAlgebra.Matrix.ToLin
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0_sturm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
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
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise
noncomputable def lpsGamma0CoefficientCount (N : ℕ) (k : ℤ) : ℕ :=
  (k * Nat.card (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)).toNat / 12 + 1
noncomputable def lpsGamma0FiniteCoefficients (N : ℕ) (k : ℤ) :
    ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ]
      (Fin (lpsGamma0CoefficientCount N k) → ℂ) where
  toFun f j := PowerSeries.coeff j.val (UpperHalfPlane.qExpansion 1 f)
  map_add' f g := by
    ext j
    simp only [FunLike.coe_add, ModularForm.qExpansion_add (by norm_num : (0:ℝ)<1)
      (by simp) f g, map_add, Pi.add_apply]
  map_smul' a f := by
    ext j
    simp only [FunLike.coe_smul, ModularForm.qExpansion_smul (by norm_num : (0:ℝ)<1)
      (by simp) a f, PowerSeries.coeff_smul, Pi.smul_apply, RingHom.id_apply]
lemma lpsGamma0FiniteCoefficients_eq_zero (N : ℕ) [NeZero N] (k : ℤ)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (h : lpsGamma0FiniteCoefficients N k f = 0) : f=0 := by
  have ho := PowerSeries.nat_le_order (UpperHalfPlane.qExpansion 1 f)
    (lpsGamma0CoefficientCount N k) (fun i hi => congrFun h ⟨i,hi⟩)
  apply lpsGamma0_sturm N k f
  apply lt_of_lt_of_le _ ho
  change ((_ : ℕ) : ℕ∞) < ((lpsGamma0CoefficientCount N k : ℕ) : ℕ∞)
  exact_mod_cast Nat.lt_succ_self _
lemma lpsGamma0FiniteCoefficients_injective (N : ℕ) [NeZero N] (k : ℤ) :
    Function.Injective (lpsGamma0FiniteCoefficients N k) := by
  apply LinearMap.ker_eq_bot.mp
  exact LinearMap.ker_eq_bot'.mpr (lpsGamma0FiniteCoefficients_eq_zero N k)
lemma lpsGamma0FiniteDimensional (N : ℕ) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ (ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :=
  FiniteDimensional.of_injective (lpsGamma0FiniteCoefficients N k)
    (lpsGamma0FiniteCoefficients_injective N k)
lemma lpsGamma0CuspFiniteDimensional (N : ℕ) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) := by
  let := lpsGamma0FiniteDimensional N k
  exact FiniteDimensional.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective
noncomputable def lpsGamma0CuspBasis (N : ℕ) [NeZero N] (k : ℤ) :
    Module.Basis (Fin (Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N :
      Subgroup (GL (Fin 2) ℝ)) k))) ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) := by
  letI := lpsGamma0CuspFiniteDimensional N k
  exact Module.finBasis ℂ _
noncomputable def lpsGamma0HeckeMatrix (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) : Matrix
      (Fin (Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)))
      (Fin (Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2))) ℂ :=
  LinearMap.toMatrix (lpsGamma0CuspBasis N 2) (lpsGamma0CuspBasis N 2)
    (lpsCuspHeckeLinearMap N p hNp)
noncomputable def lpsGamma0HeckePrimePowerMatrix (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) (r : ℕ) : Matrix
      (Fin (Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)))
      (Fin (Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2))) ℂ :=
  LinearMap.toMatrix (lpsGamma0CuspBasis N 2) (lpsGamma0CuspBasis N 2)
    (lpsHeckePrimePowerLinearMap N p hNp r)
end QEC.Coding.TannerLiftedProduct


