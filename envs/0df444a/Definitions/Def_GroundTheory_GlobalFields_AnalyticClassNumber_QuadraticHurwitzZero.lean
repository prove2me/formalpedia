-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_AnalyticClassNumber_QuadraticHurwitzZero
-- name    : GroundTheory_GlobalFields_AnalyticClassNumber_QuadraticHurwitzZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:38.822515+00:00
-- url     : https://prove2.me/theorems/f61f1201-9afd-4d0a-ade4-ef00d51973e1
-- title:
--   Quadratic Hurwitz Zero
-- statement:
--   Definitions and structural lemmas for Quadratic Hurwitz Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/AnalyticClassNumber/QuadraticHurwitzZero.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open Complex HurwitzZeta Filter Topology Set
namespace GroundTheory.Global.Quadratic
def hurwitzCombTerm (x : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  (((n : ℝ) + x : ℝ) : ℂ) ^ (-s) + ((1 - 2 * x : ℝ) : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) +
    ((2 * x - 2 : ℝ) : ℂ) * (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (-s)
def hurwitzComb (x : ℝ) (s : ℂ) : ℂ :=
  hurwitzZeta x s + ((1 - 2 * x : ℝ) : ℂ) * hurwitzZeta (1 : ℝ) s +
    ((2 * x - 2 : ℝ) : ℂ) * hurwitzZeta (1 / 2 : ℝ) s
end Quadratic
end GroundTheory.Global


