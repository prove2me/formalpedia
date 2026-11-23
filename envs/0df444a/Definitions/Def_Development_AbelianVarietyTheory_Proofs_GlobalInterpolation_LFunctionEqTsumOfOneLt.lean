-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionEqTsumOfOneLt
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionEqTsumOfOneLt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:40.760134+00:00
-- url     : https://prove2.me/theorems/4a2f2925-525d-409e-ac6f-449d387b0cbd
-- title:
--   LFunction Eq Tsum Of One Lt
-- statement:
--   Definitions and structural lemmas for LFunction Eq Tsum Of One Lt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionEqTsumOfOneLt.lean

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
namespace GlobalTheory.DirichletTail
open Filter Topology
noncomputable def term {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) (s : ℂ) : ℂ :=
  (∑ k ∈ Finset.range (n + 1), χ ((k + 1 : ℕ) : ZMod q)) *
    (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 1 + 1 : ℕ) : ℂ) ^ (-s))
end GlobalTheory.DirichletTail


