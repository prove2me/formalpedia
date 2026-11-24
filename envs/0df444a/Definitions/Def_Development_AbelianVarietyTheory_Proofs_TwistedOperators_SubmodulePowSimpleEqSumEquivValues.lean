-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubmodulePowSimpleEqSumEquivValues
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubmodulePowSimpleEqSumEquivValues
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:14.902886+00:00
-- url     : https://prove2.me/theorems/f5cf5556-37ad-4ce7-acf3-cf0b2d141220
-- title:
--   Submodule Pow Simple Eq Sum Equiv Values
-- statement:
--   Definitions and structural lemmas for Submodule Pow Simple Eq Sum Equiv Values, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SubmodulePowSimpleEqSumEquivValues.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule
namespace GlobalTheory.SubmodulePowSimple
variable {P : Type} [AddCommGroup P] [Module ℂ P] {ι : Type}
def equivValues (a : ι → Module.End ℂ P) (m : ℕ) (N : Submodule ℂ (Fin m → P)) :
    Set (Fin m → P) :=
  {v | ∃ S : P →ₗ[ℂ] (Fin m → P), (∀ i p, S (a i p) = fun j => a i (S p j)) ∧
    (∀ p, S p ∈ N) ∧ ∃ q, v = S q}
def snocZero (m : ℕ) : (Fin m → P) →ₗ[ℂ] (Fin (m+1) → P) where
  toFun z := Fin.snoc (α := fun _ => P) z 0
  map_add' x y := by
    funext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  map_smul' c x := by
    funext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
end GlobalTheory.SubmodulePowSimple
namespace GlobalTheory
end GlobalTheory


