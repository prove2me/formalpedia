-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
-- name    : ReciprocityTheory_SemistableReduction_SJCoreA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:56.075799+00:00
-- url     : https://prove2.me/theorems/eebee344-e511-4167-9941-c05e1acded9b
-- title:
--   SJCore A
-- statement:
--   Definitions and structural lemmas for SJCore A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Set Real Filter Topology
def radJ (k : ℕ) : ℝ := ∫ r in Ioi (0 : ℝ), r ^ k * exp (-r ^ 2)
def radK (k : ℕ) : ℝ := ∫ r in Ioi (0 : ℝ), r ^ k * log r * exp (-r ^ 2)
end ReciprocityTheory.MultiplicativeHeights


