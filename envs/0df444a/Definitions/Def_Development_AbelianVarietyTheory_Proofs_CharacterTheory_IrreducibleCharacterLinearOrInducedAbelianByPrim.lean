-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleCharacterLinearOrInducedAbelianByPrim
-- name    : Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleCharacterLinearOrInducedAbelianByPrim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:04:08.738924+00:00
-- url     : https://prove2.me/theorems/b90b411a-4779-442e-90e5-695c74abf545
-- title:
--   Irreducible Character Linear Or Induced Abelian By Prim
-- statement:
--   Definitions and structural lemmas for Irreducible Character Linear Or Induced Abelian By Prim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IrreducibleCharacterLinearOrInducedAbelianByPrim.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CommuteImageAbelianByPrimePowerOfNormalCentralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsCharacterEigenvectorOfCommutingRepresentatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharacterEqInducedOfImprimitivitySystemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleIdempotentEqOneAndCharacterEqWeightAlStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsWeightIdempotentStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
namespace GlobalTheory.BI
def weightStabiliser {L G : Type} [Field L] [Group G] (B : Subgroup G) (hB : B.Normal)
    (lam : B →* Lˣ) : Subgroup G where
  carrier := {g | ∀ b b' : B, (b' : G) = g⁻¹ * b * g → lam b' = lam b}
  one_mem' := by
    intro b b' h
    have : b' = b := Subtype.ext (by simpa using h)
    rw [this]
  mul_mem' := by
    intro g h hg hh b b' e
    have hc : g⁻¹ * (b : G) * g ∈ B := by
      simpa using hB.conj_mem b b.2 g⁻¹
    have h1 := hg b ⟨_, hc⟩ rfl
    have h2 := hh ⟨_, hc⟩ b' (by rw [e]; simp [mul_assoc])
    rw [h2, h1]
  inv_mem' := by
    intro g hg b b' e
    exact (hg b' b (by rw [e]; simp [mul_assoc])).symm
end GlobalTheory.BI


