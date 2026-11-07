-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
-- name    : QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:19:41.582589+00:00
-- url     : https://prove2.me/theorems/023d91a3-cce7-4b11-aa60-1ee7f99d82ad
-- title:
--   LPSCusp Petersson Trace
-- statement:
--   Definitions and structural lemmas for LPSCusp Petersson Trace, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
lemma lpsCuspPetersson_smul (N : ℕ)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (j : SL(2,ℤ)) (hj : j∈CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    petersson 2 f g (j • τ)=petersson 2 f g τ := by
  have hj' : Matrix.SpecialLinearGroup.mapGL ℝ j ∈
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) hj
  have hcast : Matrix.SpecialLinearGroup.mapGL ℝ j=(j:GL (Fin 2) ℝ) := by
    ext i k
    rfl
  rw [hcast] at hj'
  simpa only [ModularGroup.sl_moeb] using
    (SlashInvariantFormClass.petersson_smul (f:=f) (f':=g) (τ:=τ) hj')
def lpsCuspCosetPetersson (N : ℕ)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℂ :=
  Quotient.lift (fun h : SL(2,ℤ) => petersson 2 f g (h⁻¹ • τ)) fun h j hhj => by
    obtain ⟨l,hl,hl'⟩ : ∃l∈CongruenceSubgroup.Gamma0 N, j=h*l := by
      rw [← Quotient.eq_iff_equiv,Quotient.eq,QuotientGroup.leftRel_apply] at hhj
      exact ⟨h⁻¹*j,hhj,(mul_inv_cancel_left h j).symm⟩
    simp [-ModularGroup.sl_moeb,hl',mul_smul,lpsCuspPetersson_smul N f g l⁻¹ (inv_mem hl)]
def lpsCuspPeterssonTrace (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) : ℂ :=
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  ∑ γ, lpsCuspCosetPetersson N f g τ γ
def lpsCuspPeterssonDensity (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) : ℝ := (lpsCuspPeterssonTrace N f f τ).re
def lpsCuspPeterssonPairing (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) : ℂ :=
  ∫τ in ModularGroup.fd, lpsCuspPeterssonTrace N f g τ
lemma lpsWeightTwoCusp_slash_gamma0 (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : SL(2,ℤ)) (hh : h∈CongruenceSubgroup.Gamma0 N) :
    (f:ℍ→ℂ) ∣[(2:ℤ)] h=f := by
  change (f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ h=f
  exact SlashInvariantFormClass.slash_action_eq f _
    (Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) hh)
def lpsCuspCosetComponent (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N → (ℍ→ℂ) :=
  Quotient.lift (fun h : SL(2,ℤ) => (f:ℍ→ℂ) ∣[(2:ℤ)] h⁻¹) fun h j hhj => by
    obtain ⟨l,hl,hl'⟩ : ∃l∈CongruenceSubgroup.Gamma0 N, j=h*l := by
      rw [← Quotient.eq_iff_equiv,Quotient.eq,QuotientGroup.leftRel_apply] at hhj
      exact ⟨h⁻¹*j,hhj,(mul_inv_cancel_left h j).symm⟩
    rw [hl',mul_inv_rev,SlashAction.slash_mul,lpsWeightTwoCusp_slash_gamma0 N f l⁻¹ (inv_mem hl)]
def lpsCuspComponentSquareSum (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) : ℝ :=
  let : Fintype (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  ∑γ,‖lpsCuspCosetComponent N f γ τ‖^2
end
end QEC.Coding.TannerLiftedProduct


