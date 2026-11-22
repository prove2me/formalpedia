-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_Theorem3
-- name    : LeanPool_ZhangYeungInequality_Theorem3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:52:37.400661+00:00
-- url     : https://prove2.me/theorems/c843d5f4-cd79-4112-a700-ddf955611e41
-- title:
--   Theorem3
-- statement:
--   Definitions and structural lemmas for Theorem3, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem3.lean

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_Delta
public import Definitions.Def_LeanPool_ZhangYeungInequality_CopyLemma
public import Definitions.Def_LeanPool_ZhangYeungInequality_Prelude
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped ZhangYeungPFR
universe u
section Helpers
variable {Ω : Type*} [MeasurableSpace Ω]
end Helpers
section MainTheorems
variable {Ω : Type*} [MeasurableSpace Ω]
  {S₁ S₂ S₃ S₄ : Type u}
  [MeasurableSpace S₁] [MeasurableSpace S₂]
  [MeasurableSpace S₃] [MeasurableSpace S₄]
  [Finite S₁] [Finite S₂] [Finite S₃] [Finite S₄]
  [MeasurableSingletonClass S₁] [MeasurableSingletonClass S₂]
  [MeasurableSingletonClass S₃] [MeasurableSingletonClass S₄]
end MainTheorems
end ZhangYeung


