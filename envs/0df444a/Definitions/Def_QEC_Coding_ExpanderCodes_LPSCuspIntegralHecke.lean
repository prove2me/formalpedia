-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspIntegralHecke
-- name    : QEC_Coding_ExpanderCodes_LPSCuspIntegralHecke
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T03:06:52.59059+00:00
-- url     : https://prove2.me/theorems/814bd17d-52b3-4571-b290-aa1708e49102
-- title:
--   LPSCusp Integral Hecke
-- statement:
--   Definitions and structural lemmas for LPSCusp Integral Hecke, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspIntegralHecke.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsCuspHecke
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
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
def lpsCuspCoefficient (N n : ℕ) :
    CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2 →ₗ[ℤ] ℂ :=
  ((lpsModularForm_coefficientLinearMap N n).comp CuspForm.toModularFormₗ).restrictScalars ℤ
def lpsIntegralCuspLattice (N : ℕ) :
    Submodule ℤ (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) where
  carrier f := ∀ n, ∃ z : ℤ, lpsCuspCoefficient N n f = (z : ℂ)
  zero_mem' := by intro n; exact ⟨0, by simp⟩
  add_mem' hf hg := by
    intro n
    obtain ⟨a, ha⟩ := hf n
    obtain ⟨b, hb⟩ := hg n
    exact ⟨a+b, by rw [map_add, ha, hb, Int.cast_add]⟩
  smul_mem' z f hf := by
    intro n
    obtain ⟨a, ha⟩ := hf n
    refine ⟨z*a, ?_⟩
    rw [map_smul, ha, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul, Int.cast_mul]
def lpsIntegralCuspCoordinates (N : ℕ) :
    lpsIntegralCuspLattice N →ₗ[ℤ] (Fin (lpsGamma0CoefficientCount N 2) → ℤ) where
  toFun f i := (f.property i.val).choose
  map_add' f g := by
    funext i
    apply Int.cast_injective (α := ℂ)
    simp only [Pi.add_apply]
    rw [Int.cast_add, ← (f.property i.val).choose_spec, ← (g.property i.val).choose_spec,
      ← ((f+g).property i.val).choose_spec]
    exact map_add (lpsCuspCoefficient N i.val) f.val g.val
  map_smul' z f := by
    funext i
    apply Int.cast_injective (α := ℂ)
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul]
    rw [← (f.property i.val).choose_spec, ← ((z • f).property i.val).choose_spec]
    change lpsCuspCoefficient N i.val (z • f.val) =
      ((RingHom.id ℤ) z : ℂ) * lpsCuspCoefficient N i.val f.val
    simpa only [← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul, RingHom.id_apply] using
      map_smul (lpsCuspCoefficient N i.val) z f.val
lemma lpsCuspHecke_preservesIntegralLattice (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : f ∈ lpsIntegralCuspLattice N) :
    lpsCuspHeckeLinearMap N p hNp f ∈ lpsIntegralCuspLattice N := by
  intro n
  obtain ⟨x, hx⟩ := hf (p*n)
  change PowerSeries.coeff (p*n) (UpperHalfPlane.qExpansion 1 f) = (x : ℂ) at hx
  change ∃ z : ℤ, PowerSeries.coeff n
    (UpperHalfPlane.qExpansion 1 (lpsCuspHecke N p hNp f)) = (z : ℂ)
  rw [coeff_qExpansion_lpsCuspHecke, lpsModularDilationCoefficient]
  by_cases hd : p ∣ n
  · obtain ⟨y, hy⟩ := hf (n/p)
    change PowerSeries.coeff (n/p) (UpperHalfPlane.qExpansion 1 f) = (y : ℂ) at hy
    refine ⟨x+(p : ℤ)*y, ?_⟩
    simp only [if_pos hd, hx, hy, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  · exact ⟨x, by simp [hd, hx]⟩
def lpsIntegralCuspHecke (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N) :
    Module.End ℤ (lpsIntegralCuspLattice N) where
  toFun f := ⟨lpsCuspHeckeLinearMap N p hNp f,
    lpsCuspHecke_preservesIntegralLattice N p hNp f f.property⟩
  map_add' f g := by apply Subtype.ext; exact map_add _ _ _
  map_smul' z f := by
    apply Subtype.ext
    exact map_smul ((lpsCuspHeckeLinearMap N p hNp).restrictScalars ℤ) z f.val
end
end QEC.Coding.TannerLiftedProduct


