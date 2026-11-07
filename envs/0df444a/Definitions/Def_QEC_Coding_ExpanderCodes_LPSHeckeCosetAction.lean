-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetAction
-- name    : QEC_Coding_ExpanderCodes_LPSHeckeCosetAction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:12:59.578732+00:00
-- url     : https://prove2.me/theorems/81b6ecf4-4fb5-46c4-a007-1289c6afc747
-- title:
--   LPSHecke Coset Action
-- statement:
--   Definitions and structural lemmas for LPSHecke Coset Action, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCosetAction.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
import Mathlib.GroupTheory.GroupAction.Basic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRightIndex_spec
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeUpperMatrix_index_unique
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
lemma lpsHeckeRightIndex_of_factor (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (γ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (i j : Option (Fin p)) (δ : SL(2,ℤ))
    (he : lpsHeckeUpperMatrix p i*(γ:Matrix (Fin 2) (Fin 2) ℤ)=
      (δ:Matrix (Fin 2) (Fin 2) ℤ)*lpsHeckeUpperMatrix p j) :
    lpsHeckeRightIndex N p hNp γ hγ i=j := by
  obtain ⟨ε,_hε,hε⟩ := lpsHeckeRightIndex_spec N p hNp γ hγ i
  apply lpsHeckeUpperMatrix_index_unique p _ j ((ε⁻¹*δ:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ)
  calc
    lpsHeckeUpperMatrix p (lpsHeckeRightIndex N p hNp γ hγ i)=
        ((ε⁻¹:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ)*
          ((ε:Matrix (Fin 2) (Fin 2) ℤ)*lpsHeckeUpperMatrix p (lpsHeckeRightIndex N p hNp γ hγ i)) := by
      rw [←Matrix.mul_assoc,←Matrix.SpecialLinearGroup.coe_mul,inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one,Matrix.one_mul]
    _ = _ := by
      rw [←hε,he,←Matrix.mul_assoc,←Matrix.SpecialLinearGroup.coe_mul]
lemma lpsHeckeRightIndex_one (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (i : Option (Fin p)) :
    lpsHeckeRightIndex N p hNp 1 (CongruenceSubgroup.Gamma0 N).one_mem i=i := by
  apply lpsHeckeRightIndex_of_factor N p hNp 1 (CongruenceSubgroup.Gamma0 N).one_mem i i 1
  simp
lemma lpsHeckeRightIndex_mul (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (γ δ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (hδ : δ ∈ CongruenceSubgroup.Gamma0 N) (i : Option (Fin p)) :
    lpsHeckeRightIndex N p hNp (γ*δ) ((CongruenceSubgroup.Gamma0 N).mul_mem hγ hδ) i =
      lpsHeckeRightIndex N p hNp δ hδ (lpsHeckeRightIndex N p hNp γ hγ i) := by
  obtain ⟨a,_ha,hea⟩ := lpsHeckeRightIndex_spec N p hNp γ hγ i
  obtain ⟨b,_hb,heb⟩ := lpsHeckeRightIndex_spec N p hNp δ hδ
    (lpsHeckeRightIndex N p hNp γ hγ i)
  apply lpsHeckeRightIndex_of_factor N p hNp (γ*δ)
    ((CongruenceSubgroup.Gamma0 N).mul_mem hγ hδ) i _ (a*b)
  rw [Matrix.SpecialLinearGroup.coe_mul,←Matrix.mul_assoc,hea,Matrix.mul_assoc,heb,
    ←Matrix.mul_assoc,←Matrix.SpecialLinearGroup.coe_mul]
@[instance_reducible]
noncomputable def lpsHeckeIndexAction (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N) :
    MulAction (CongruenceSubgroup.Gamma0 N) (Option (Fin p)) where
  smul γ i := lpsHeckeRightIndex N p hNp (γ:SL(2,ℤ))⁻¹
    ((CongruenceSubgroup.Gamma0 N).inv_mem γ.property) i
  one_smul i := by
    change lpsHeckeRightIndex N p hNp (1:SL(2,ℤ))⁻¹ _ i=i
    simpa only [inv_one] using lpsHeckeRightIndex_one N p hNp i
  mul_smul γ δ i := by
    change lpsHeckeRightIndex N p hNp ((γ:SL(2,ℤ))*(δ:SL(2,ℤ)))⁻¹ _ i =
      lpsHeckeRightIndex N p hNp (γ:SL(2,ℤ))⁻¹ _
        (lpsHeckeRightIndex N p hNp (δ:SL(2,ℤ))⁻¹ _ i)
    simpa only [mul_inv_rev] using lpsHeckeRightIndex_mul N p hNp
      (δ:SL(2,ℤ))⁻¹ (γ:SL(2,ℤ))⁻¹
      ((CongruenceSubgroup.Gamma0 N).inv_mem δ.property)
      ((CongruenceSubgroup.Gamma0 N).inv_mem γ.property) i
end
end QEC.Coding.TannerLiftedProduct


