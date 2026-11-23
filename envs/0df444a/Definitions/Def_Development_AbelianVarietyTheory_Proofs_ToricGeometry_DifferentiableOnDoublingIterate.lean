-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnDoublingIterate
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnDoublingIterate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:06.162639+00:00
-- url     : https://prove2.me/theorems/ee7d60ba-221a-406f-8685-4a1e75c103bf
-- title:
--   Differentiable On Doubling Iterate
-- statement:
--   Definitions and structural lemmas for Differentiable On Doubling Iterate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/DifferentiableOnDoublingIterate.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
namespace GlobalTheory
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
noncomputable def doublingIterate (h : E → ℂ) : ℕ → E → ℂ
  | 0 => fun z => h ((2 : ℂ)⁻¹ • z)
  | n + 1 => fun z =>
      3 * doublingIterate h n ((2 : ℂ)⁻¹ • z) + doublingIterate h n (-((2 : ℂ)⁻¹ • z))
end
end GlobalTheory


