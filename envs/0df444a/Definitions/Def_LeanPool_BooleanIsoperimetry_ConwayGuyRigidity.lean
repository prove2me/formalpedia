-- Prove2me | Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyRigidity
-- name    : LeanPool_BooleanIsoperimetry_ConwayGuyRigidity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:32:38.904805+00:00
-- url     : https://prove2.me/theorems/a60335a7-0eb1-437f-8716-a694b06a4372
-- title:
--   Conway Guy Rigidity
-- statement:
--   Definitions and structural lemmas for Conway Guy Rigidity, from Alexey Milovanov; Egor Lyfar; LeanPool contributors's pinned Boolean Isoperimetry and Conway--Guy Coherent Gaps development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyRigidity.lean

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyHeight
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_conwayGuy_block_identity
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_principal_coordinateSum
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_principal_corrections_decomposition
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_principal_dot
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_principal_entry
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_basis
attribute [local simp] BooleanIsoperimetry.CoherentGap.realDot_basis


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BooleanIsoperimetry.CoherentGap
def ConwayGuyBlockIdentity (offset : ℕ) : Prop :=
  conwayGuyHeight (offset + 2) -
      ∑ index : Fin (guide (offset + 2)),
        conwayGuyHeight (offset + 2 - index.val - 1) +
    ∑ index : Fin (guide (offset + 2) - 1),
      conwayGuyHeight (triangular index.val) = 1
noncomputable def conwayGuyBaseCertificate :
    Certificate (conwayGuyArithmetic.tower.weights 1) (basis 0) :=
  Certificate.singleton (by
    refine ⟨?_, ?_, ?_⟩
    · intro coordinate
      right
      right
      have hcoordinate : coordinate = 0 := Fin.eq_zero coordinate
      subst coordinate
      simp [basis]
    · rw [dot_basis]
      simp [ConwayGuyArithmetic.tower, ConwayGuyArithmetic.weights,
        conwayGuyArithmetic]
    · right
      right
      exact coordinateSum_basis 0)
lemma principal_valid (hblock : ∀ offset, ConwayGuyBlockIdentity offset)
    (offset : ℕ) :
    IsLiftableUnit (conwayGuyArithmetic.tower.weights (offset + 2))
      (principal offset) := by
  refine ⟨principal_entry offset, ?_, ?_⟩
  · exact principal_dot offset (hblock offset)
  · right
    right
    exact principal_coordinateSum offset
noncomputable def conwayGuyFirstCoordinateRecurrence
    (hblock : ∀ offset, ConwayGuyBlockIdentity offset) :
    FirstCoordinateRecurrence conwayGuyArithmetic.tower where
  base := conwayGuyBaseCertificate
  principal := principal
  principal_valid := principal_valid hblock
  corrections := corrections
  decomposition := principal_corrections_decomposition
lemma conwayGuyBlockIdentity_all (offset : ℕ) :
    ConwayGuyBlockIdentity offset := by
  exact conwayGuy_block_identity (offset + 2) (by omega)
noncomputable def conwayGuyRecurrence :
    FirstCoordinateRecurrence conwayGuyArithmetic.tower :=
  conwayGuyFirstCoordinateRecurrence conwayGuyBlockIdentity_all
end BooleanIsoperimetry.CoherentGap


