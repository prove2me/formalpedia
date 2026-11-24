-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitarySatakeCoeffAdjacentSwapOfLeviReduction
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitarySatakeCoeffAdjacentSwapOfLeviReduction
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T16:09:50.923698+00:00
-- url     : https://prove2.me/theorems/740399dc-64c0-4c92-9747-9ab0ad7b1f4e
-- title:
--   Unitary Satake Coeff Adjacent Swap Of Levi Reduction
-- statement:
--   Definitions and structural lemmas for Unitary Satake Coeff Adjacent Swap Of Levi Reduction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitarySatakeCoeffAdjacentSwapOfLeviReduction.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG GlobalTheory.SatakeWeyl
namespace GlobalTheory.SatakeWeyl.Swap
def ex (n m : ℕ) (a : Fin m → ℤ) (i : Fin n) : ℤ :=
  if h : i.val < m then a ⟨i.val, h⟩
  else if h' : n - m ≤ i.val ∧ n - 1 - i.val < m then -(a ⟨n - 1 - i.val, h'.2⟩) else 0
def emb (n i : ℕ) (h : 2 * i + 4 ≤ n) : Fin 4 → Fin n :=
  ![⟨i, by omega⟩, ⟨i + 1, by omega⟩, ⟨n - 2 - i, by omega⟩, ⟨n - 1 - i, by omega⟩]
def blk (n i : ℕ) (a : Fin n) : ℕ :=
  if a.val = i + 1 then i else if a.val = n - 1 - i then n - 2 - i else a.val
end GlobalTheory.SatakeWeyl.Swap
end


