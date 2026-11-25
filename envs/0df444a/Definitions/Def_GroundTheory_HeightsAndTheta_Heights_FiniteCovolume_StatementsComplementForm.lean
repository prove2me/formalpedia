-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsComplementForm
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsComplementForm
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T02:37:40.293802+00:00
-- url     : https://prove2.me/theorems/0ce36962-7dfa-497c-aa31-ac850a07f117
-- title:
--   Statements Complement Form
-- statement:
--   Definitions and structural lemmas for Statements Complement Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsComplementForm.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans
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
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
section Complement
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
def IsHyperbolicPair (h : HermitianForm F E W) (v w : W) : Prop :=
  h.toSesq v v = 0 ∧ h.toSesq w w = 0 ∧ h.toSesq v w = 1
def hypComplement (h : HermitianForm F E W) (v w : W) : Submodule E W :=
  LinearMap.ker (h.toSesq v) ⊓ LinearMap.ker (h.toSesq w)
theorem mem_hypComplement {h : HermitianForm F E W} {v w x : W} :
    x ∈ hypComplement h v w ↔ h.toSesq v x = 0 ∧ h.toSesq w x = 0 := by
  simp [hypComplement]
def ComplementForm.Statement (h : HermitianForm F E W) : Prop :=
  ∀ v w : W, IsHyperbolicPair h v w →
    ∃ h' : HermitianForm F E (hypComplement h v w), ∀ x y, h'.toSesq x y = h.toSesq x y
end Complement
namespace GaussianPlane
def w0G : Fin 2 → Eg := ![1 / 2, -1 / 2]
theorem conj_two_G : conj ℚ Eg (2 : Eg) = 2 := map_ofNat _ 2
theorem eq_zero_of_mem_hypComplementG {x : Fin 2 → Eg} (hx : x ∈ hypComplement hG v0 w0G) :
    x = 0 := by
  rw [mem_hypComplement, hG_apply, hG_apply] at hx
  obtain ⟨h1, h2⟩ := hx
  simp [v0, w0G, conj_two_G] at h1 h2
  have e0 : x 0 = 0 := by linear_combination h2 + (1 / 2 : Eg) * h1
  have e1 : x 1 = 0 := by linear_combination h2 - (1 / 2 : Eg) * h1
  funext i
  fin_cases i
  · exact e0
  · exact e1
instance : Subsingleton (hypComplement hG v0 w0G) :=
  ⟨fun a b => Subtype.ext ((eq_zero_of_mem_hypComplementG a.2).trans
    (eq_zero_of_mem_hypComplementG b.2).symm)⟩
def complementFormG : HermitianForm ℚ Eg (hypComplement hG v0 w0G) where
  toSesq := 0
  isSymm := ⟨fun x y => by
    change conjHom ℚ Eg (0 : Eg) = (0 : Eg)
    exact map_zero _⟩
  nonsingular := by
    refine ⟨fun a b _ => Subsingleton.elim a b, fun φ => ⟨0, ?_⟩⟩
    ext x
    rw [Subsingleton.elim x 0]
    simp
end GaussianPlane
section Inhabitants
open GaussianPlane
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


