-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:20.343803+00:00
-- url     : https://prove2.me/theorems/de700ee9-47db-4dc1-b910-63b3a282c27a
-- title:
--   Summable And Abs Tsum Sub Integral Le
-- statement:
--   Definitions and structural lemmas for Summable And Abs Tsum Sub Integral Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/SummableAndAbsTsumSubIntegralLe.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open scoped Real
namespace GlobalTheory.KroneckerLimit
noncomputable def betaConst (s : ℝ) : ℝ := √π * Real.Gamma (s - 1 / 2) / Real.Gamma s
end GlobalTheory.KroneckerLimit


