-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Examples
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Examples
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:43:11.534071+00:00
-- url     : https://prove2.me/theorems/9dd1cbf8-d4cd-42f3-8faa-9df7e8d64994
-- title:
--   Examples
-- statement:
--   Definitions and structural lemmas for Examples, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Objects
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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_archUnitary_0eab686fdef0
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
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
section General
variable {F E W : Type*} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [AddCommGroup W] [Module E W]
end General
abbrev Eg : Type := CyclotomicField 4 ℚ
instance : IsCyclotomicExtension {4} ℚ Eg := CyclotomicField.isCyclotomicExtension 4 ℚ
theorem finrank_Eg : finrank ℚ Eg = 2 := by
  rw [IsCyclotomicExtension.finrank (n := 4) Eg
    (Polynomial.cyclotomic.irreducible_rat (n := 4) (by norm_num))]
  decide
instance : Algebra.IsQuadraticExtension ℚ Eg := { finrank_eq_two' := finrank_Eg }
instance : IsTotallyComplex Eg := IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) Eg (by norm_num)
theorem card_infinitePlace : Fintype.card (InfinitePlace Eg) = 1 := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank Eg
  rw [IsTotallyComplex.nrRealPlaces_eq_zero, finrank_Eg] at h1
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero]
  omega
instance : Subsingleton (InfinitePlace Eg) :=
  Fintype.card_le_one_iff_subsingleton.mp card_infinitePlace.le
def signs : Fin 2 → ℚˣ := ![1, -1]
def hG : HermitianForm ℚ Eg (Fin 2 → Eg) := diagForm signs
def vG : Basis (Fin 2) Eg (Fin 2 → Eg) := Pi.basisFun Eg (Fin 2)
theorem hG_apply (x y : Fin 2 → Eg) : hG.toSesq x y = conj ℚ Eg (x 0) * y 0 - conj ℚ Eg (x 1) * y 1 := by
  simp only [hG, diagForm, signs, LinearMap.mk₂'ₛₗ_apply, Fin.sum_univ_two]
  simp
  ring
theorem gram_hG : gram hG.toSesq vG = Matrix.diagonal ![1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Automorphic.gram_apply, vG, Pi.basisFun_apply] <;> rw [hG_apply] <;> simp
theorem gramAt_hG (w : InfinitePlace Eg) : gramAt hG vG w = Matrix.diagonal ![1, -1] := by
  rw [gramAt, gram_hG]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
def MG : Majorant hG vG where
  P _ := 1
  posDef _ := Matrix.PosDef.one
  siegel w := by
    rw [gramAt_hG, Matrix.one_mul, Matrix.mul_one]
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
def LaG : AddSubgroup (Fin 2 → Eg) :=
  (AddMonoidHom.compLeft (algebraMap (𝓞 Eg) Eg).toAddMonoidHom (Fin 2)).range
def v0 : Fin 2 → Eg := fun _ => 1
def lG : Submodule Eg (Fin 2 → Eg) := Submodule.span Eg {v0}
def muG : Measure (archUnitary hG vG) := Measure.haar
instance : muG.IsHaarMeasure := by
  unfold muG
  infer_instance
def Bm : Matrix (Fin 2) (Fin 2) ℂ := !![5 / 4, 3 / 4; 3 / 4, 5 / 4]
theorem det_Bm : Bm.det = 1 := by
  simp [Bm, Matrix.det_fin_two]
  norm_num
def gBu : GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero Bm (by rw [det_Bm]; norm_num)
def gB : archUnitary hG vG :=
  ⟨fun _ => gBu, mem_archUnitary.2 fun w => by
    rw [gramAt_hG]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gBu, Bm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, map_ofNat] <;> norm_num⟩
def e0 : Fin 2 → Eg := Pi.single 0 1
def VVG : Set (Fin 2 → Eg) := {y | ∃ γ ∈ latticeStab hG LaG, γ • v0 = y}
end
end GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane


