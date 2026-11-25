-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PRadicalTorusModulusDet
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PRadicalTorusModulusDet
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T09:06:30.237445+00:00
-- url     : https://prove2.me/theorems/0171764e-dc15-4ad4-a14c-760a5c527531
-- title:
--   PRadical Torus Modulus Det
-- statement:
--   Definitions and structural lemmas for PRadical Torus Modulus Det, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PRadicalTorusModulusDet.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PRadicalTorusModulusCoords
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_add_right_73a7d76a7d0e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_conj_a26db4eadf30
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_smul_right_b5b6ef42f985
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_heisY_421c3d3a6138
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}
def heisPairMap (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) (w : InfinitePlace E) :
    (ι → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
  Matrix.mulVecLin (Matrix.of ![star (vecAt v x₀ w) ᵥ* gramAt h v w,
    star (vecAt v w₀ w) ᵥ* gramAt h v w])
omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] [DecidableEq ι] in
theorem heisPairMap_apply (w : InfinitePlace E) (z : ι → ℂ) :
    heisPairMap h v x₀ w₀ w z =
      ![hForm (gramAt h v w) (vecAt v x₀ w) z, hForm (gramAt h v w) (vecAt v w₀ w) z] := by
  funext i
  fin_cases i <;> simp [heisPairMap, hForm, Matrix.mulVec, dotProduct_mulVec]
def heisYAt (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) (w : InfinitePlace E) :
    Submodule ℂ (ι → ℂ) :=
  LinearMap.ker (heisPairMap h v x₀ w₀ w)
omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] [DecidableEq ι] in
theorem mem_heisYAt {w : InfinitePlace E} {z : ι → ℂ} :
    z ∈ heisYAt h v x₀ w₀ w ↔ hForm (gramAt h v w) (vecAt v x₀ w) z = 0 ∧
      hForm (gramAt h v w) (vecAt v w₀ w) z = 0 := by
  rw [heisYAt, LinearMap.mem_ker, heisPairMap_apply]
  constructor
  · intro hz
    exact ⟨by simpa using congrFun hz 0, by simpa using congrFun hz 1⟩
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i <;> simp [h0, h1]
theorem finrank_heisYAt (hp : IsHyperbolicPair h x₀ w₀) (w : InfinitePlace E) :
    finrank ℂ (heisYAt h v x₀ w₀ w) + 2 = Fintype.card ι := by
  obtain ⟨hH, -, ha, hb, hab⟩ := hyperbolic_at_place h v hp w
  have hba : hForm (gramAt h v w) (vecAt v w₀ w) (vecAt v x₀ w) = 1 := by
    rw [← hForm_conj hH, hab, map_one]
  have hs : Function.Surjective (heisPairMap h v x₀ w₀ w) := fun u =>
    ⟨u 0 • vecAt v w₀ w + u 1 • vecAt v x₀ w, by
      rw [heisPairMap_apply]
      funext i
      fin_cases i <;> simp [hForm_add_right, hForm_smul_right, ha, hb, hab, hba]⟩
  have e := LinearMap.finrank_range_add_finrank_ker (heisPairMap h v x₀ w₀ w)
  rw [LinearMap.range_eq_top.2 hs, finrank_top, Module.finrank_fin_fun,
    Module.finrank_fintype_fun_eq_card] at e
  rw [heisYAt]
  omega
def heisYEquiv (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) :
    heisY h v x₀ w₀ ≃ₗ[ℝ] ((w : InfinitePlace E) → heisYAt h v x₀ w₀ w) where
  toFun y w := ⟨(y : InfinitePlace E → ι → ℂ) w, mem_heisYAt.2 (y.2 w)⟩
  invFun z := ⟨fun w => (z w : ι → ℂ), mem_heisY.2 fun w => mem_heisYAt.1 (z w).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def heisYAtEquiv (hp : IsHyperbolicPair h x₀ w₀) (w : InfinitePlace E) :
    heisYAt h v x₀ w₀ w ≃ₗ[ℂ] (Fin (Fintype.card ι - 2) → ℂ) :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_fin_fun]
    have := finrank_heisYAt (v := v) hp w
    omega)
def placeScale (r : InfinitePlace E → ℝ) : (InfinitePlace E → ℝ) →ₗ[ℝ] (InfinitePlace E → ℝ) :=
  LinearMap.pi fun w => (r w • LinearMap.id).comp (LinearMap.proj w)
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


