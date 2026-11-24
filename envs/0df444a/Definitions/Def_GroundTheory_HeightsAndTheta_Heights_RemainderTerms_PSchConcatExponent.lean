-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchConcatExponent
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchConcatExponent
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T18:27:04.271456+00:00
-- url     : https://prove2.me/theorems/7a7ebe01-ec4a-4de2-ac90-f96a737c3f35
-- title:
--   PSch Concat Exponent
-- statement:
--   Definitions and structural lemmas for PSch Concat Exponent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchConcatExponent.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.RestTerms
noncomputable section
def SchConcatExponent.rotateFun (r a : ℕ) (p : Fin (r + a)) : Fin (r + a) :=
  if h : (p : ℕ) < a then ⟨r + p, by omega⟩ else ⟨p - a, by have := p.isLt; omega⟩
def SchConcatExponent.rotateInv (r a : ℕ) (q : Fin (r + a)) : Fin (r + a) :=
  if h : (q : ℕ) < r then ⟨q + a, by omega⟩ else ⟨q - r, by have := q.isLt; omega⟩
theorem SchConcatExponent.rotateFun_val (r a : ℕ) (p : Fin (r + a)) :
    (SchConcatExponent.rotateFun r a p : ℕ) = if (p : ℕ) < a then r + p else p - a := by
  unfold SchConcatExponent.rotateFun; split <;> rfl
theorem SchConcatExponent.rotateInv_val (r a : ℕ) (q : Fin (r + a)) :
    (SchConcatExponent.rotateInv r a q : ℕ) = if (q : ℕ) < r then q + a else q - r := by
  unfold SchConcatExponent.rotateInv; split <;> rfl
def SchConcatExponent.rotate (r a : ℕ) : Equiv.Perm (Fin (r + a)) where
  toFun := SchConcatExponent.rotateFun r a
  invFun := SchConcatExponent.rotateInv r a
  left_inv p := by
    have hp := p.isLt
    apply Fin.ext
    rw [SchConcatExponent.rotateInv_val, SchConcatExponent.rotateFun_val]
    split_ifs <;> omega
  right_inv q := by
    have hq := q.isLt
    apply Fin.ext
    rw [SchConcatExponent.rotateFun_val, SchConcatExponent.rotateInv_val]
    split_ifs <;> omega
end
end GroundTheory.Heights₂.Heights.RestTerms


