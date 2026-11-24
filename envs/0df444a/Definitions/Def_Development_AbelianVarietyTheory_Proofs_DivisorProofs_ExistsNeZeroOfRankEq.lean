-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroOfRankEq
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroOfRankEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:57.248794+00:00
-- url     : https://prove2.me/theorems/7a2f8f3c-619c-4b53-8548-abd1a91c4272
-- title:
--   Exists Ne Zero Of Rank Eq
-- statement:
--   Definitions and structural lemmas for Exists Ne Zero Of Rank Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroOfRankEq.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.SemisimpleCount
variable {Rg : Type} [Ring Rg] [Algebra ℂ Rg]
def killed (I : Set Rg) (M : Type) [AddCommGroup M] [Module ℂ M] [Module Rg M]
    [IsScalarTower ℂ Rg M] : Submodule ℂ M where
  carrier := {m | ∀ x ∈ I, x • m = 0}
  add_mem' := fun ha hb x hx => by rw [smul_add, ha x hx, hb x hx, add_zero]
  zero_mem' := fun x _ => smul_zero x
  smul_mem' := fun c m hm x hx => by rw [smul_comm, hm x hx, smul_zero]
section
variable (I : Set Rg) {M N : Type} [AddCommGroup M] [Module ℂ M] [Module Rg M]
    [IsScalarTower ℂ Rg M] [AddCommGroup N] [Module ℂ N] [Module Rg N] [IsScalarTower ℂ Rg N]
variable {S : Type} [AddCommGroup S] [Module Rg S]
end
end GlobalTheory.SemisimpleCount


