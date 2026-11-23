-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNinePowMulInvSqSucc
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNinePowMulInvSqSucc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:40.695797+00:00
-- url     : https://prove2.me/theorems/04056e47-9cb5-446f-8782-e972cf076185
-- title:
--   Summable Nine Pow Mul Inv Sq Succ
-- statement:
--   Definitions and structural lemmas for Summable Nine Pow Mul Inv Sq Succ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNinePowMulInvSqSucc.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
namespace GlobalTheory
namespace LLeft
noncomputable def diffPow : ℕ → ℂ → ℝ → ℂ
  | 0, s, x => (x : ℂ) ^ (-s)
  | k + 1, s, x => diffPow k s x - diffPow k s (x + 1)
end LLeft
end GlobalTheory


