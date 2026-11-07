-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHecke
-- name    : QEC_Coding_ExpanderCodes_LPSCuspHecke
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:14:33.374752+00:00
-- url     : https://prove2.me/theorems/64010728-1eab-4fe2-aa25-11936ea5010b
-- title:
--   LPSCusp Hecke
-- statement:
--   Definitions and structural lemmas for LPSCusp Hecke, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHecke.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRightFactorGL
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRightIndex_bijective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRightIndex_spec
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeUpperGL_rat_real
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
noncomputable def lpsHeckeSlashSum (p : ℕ) [Fact p.Prime] (f : ℍ→ℂ) : ℍ→ℂ :=
  ∑ i : Option (Fin p),f ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i
lemma lpsHeckeSlashSum_invariant (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 N) :
    (lpsHeckeSlashSum p f ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ γ)=
      lpsHeckeSlashSum p f := by
  classical
  have he (i : Option (Fin p)) :
      (((f:ℍ→ℂ) ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ γ)=
        (f:ℍ→ℂ) ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p (lpsHeckeRightIndex N p hNp γ hγ i) := by
    obtain ⟨δ,hδ,h⟩ := lpsHeckeRightIndex_spec N p hNp γ hγ i
    rw [←SlashAction.slash_mul,lpsHeckeRightFactorGL ℝ p _ _ γ δ h,SlashAction.slash_mul]
    have hf := f.slash_action_eq' (Matrix.SpecialLinearGroup.mapGL ℝ δ) ⟨δ,hδ,rfl⟩
    change ((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ δ)=(f:ℍ→ℂ) at hf
    rw [hf]
  unfold lpsHeckeSlashSum
  rw [SlashAction.sum_slash]
  simp_rw [he]
  apply Fintype.sum_bijective (lpsHeckeRightIndex N p hNp γ hγ)
    (lpsHeckeRightIndex_bijective N p hNp γ hγ)
  intro i
  rfl
lemma lpsHeckeSlashSum_zero_at_cusps (N p : ℕ) [NeZero N] [Fact p.Prime]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (c : OnePoint ℝ) (hc : IsCusp c (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    OnePoint.IsZeroAt c (lpsHeckeSlashSum p f) 2 := by
  classical
  have hz (i : Option (Fin p)) : OnePoint.IsZeroAt c
      ((f:ℍ→ℂ) ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i) 2 := by
    have hs := lpsRationalGL_smul_cusp (lpsHeckeUpperGL ℚ p i) c
      (hc.mono (Subgroup.map_le_range (Matrix.SpecialLinearGroup.mapGL ℝ) _))
    rw [lpsHeckeUpperGL_rat_real] at hs
    have hsg : IsCusp (lpsHeckeUpperGL ℝ p i • c)
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) :=
      (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr hs
    exact OnePoint.IsZeroAt.smul_iff.mp (f.zero_at_cusps' hsg)
  intro g hg
  unfold lpsHeckeSlashSum
  rw [SlashAction.sum_slash,UpperHalfPlane.IsZeroAtImInfty,Filter.ZeroAtFilter]
  have ht := tendsto_finsetSum Finset.univ
    (fun (i : Option (Fin p)) _ => hz i g hg)
  simpa only [Finset.sum_fn,Finset.sum_const_zero] using ht
noncomputable def lpsCuspHecke (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2 where
  toFun := lpsHeckeSlashSum p f
  slash_action_eq' := by
    intro g hg
    obtain ⟨γ,hγ,rfl⟩ := hg
    exact lpsHeckeSlashSum_invariant N p hNp f γ hγ
  holo' := by
    change MDiff (lpsHeckeSlashSum p (f:ℍ→ℂ))
    unfold lpsHeckeSlashSum
    apply MDifferentiable.sum
    intro i _
    have hf : MDiff (f:ℍ→ℂ) := f.holo'
    exact hf.slash 2 (lpsHeckeUpperGL ℝ p i)
  zero_at_cusps' := lpsHeckeSlashSum_zero_at_cusps N p f _
end QEC.Coding.TannerLiftedProduct


