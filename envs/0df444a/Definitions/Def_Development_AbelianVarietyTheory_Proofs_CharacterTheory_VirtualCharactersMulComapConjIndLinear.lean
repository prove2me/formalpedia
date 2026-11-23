-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinear
-- name    : Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinear
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:51.737888+00:00
-- url     : https://prove2.me/theorems/fbec465e-8fde-48dc-8a2c-a98e85001216
-- title:
--   Virtual Characters Mul Comap Conj Ind Linear
-- statement:
--   Definitions and structural lemmas for Virtual Characters Mul Comap Conj Ind Linear, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/VirtualCharactersMulComapConjIndLinear.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldInducedClassFunction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.BI
open Polynomial in
theorem _root_.GlobalTheory.BI.subgroupFunctionExtendByZero_add {G : Type} [Group G] (H : Subgroup G) (a b : H → ℂ)
    (g : G) :
    _root_.GlobalTheory.BI.ext0 H (a + b) g =
      _root_.GlobalTheory.BI.ext0 H a g + _root_.GlobalTheory.BI.ext0 H b g := by
  unfold _root_.GlobalTheory.BI.ext0
  split_ifs <;> simp
noncomputable def indAddHomComplex {G : Type} [Group G] [Finite G] (H : Subgroup G) : (H → ℂ) →+ (G → ℂ) :=
  AddMonoidHom.mk' (ind H) (fun a b => by
    funext g
    haveI := Fintype.ofFinite G
    simp only [ind, Pi.add_apply, subgroupFunctionExtendByZero_add, finsum_eq_sum_of_fintype, Finset.sum_add_distrib, mul_add])
end GlobalTheory.BI


