-- Prove2me | Definitions.Def_LeanPool_ZhangYeungInequality_Theorem5
-- name    : LeanPool_ZhangYeungInequality_Theorem5
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:52:48.517722+00:00
-- url     : https://prove2.me/theorems/1725cd57-5487-4d37-a1e3-9cb25801cb98
-- title:
--   Theorem5
-- statement:
--   Definitions and structural lemmas for Theorem5, from Christopher Boone; LeanPool contributors's pinned The Zhang-Yeung non-Shannon information inequality development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/Theorem5.lean

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
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
  {n : ℕ}
  {S_U S_Z : Type u} {S : Fin n → Type u}
  [MeasurableSpace S_U] [MeasurableSpace S_Z]
  [∀ i, MeasurableSpace (S i)]
  [Finite S_U] [Finite S_Z] [∀ i, Finite (S i)]
  [MeasurableSingletonClass S_U] [MeasurableSingletonClass S_Z]
  [∀ i, MeasurableSingletonClass (S i)]
end MainTheorems
end ZhangYeung


