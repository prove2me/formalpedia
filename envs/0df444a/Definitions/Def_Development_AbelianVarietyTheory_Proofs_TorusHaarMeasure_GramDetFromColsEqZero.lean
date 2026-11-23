-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetFromColsEqZero
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetFromColsEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:50.968546+00:00
-- url     : https://prove2.me/theorems/e5f831ec-7b24-48bb-847e-24390ce39a2c
-- title:
--   Gram Det From Cols Eq Zero
-- statement:
--   Definitions and structural lemmas for Gram Det From Cols Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/GramDetFromColsEqZero.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
namespace GlobalTheory
namespace GramSubmodular
variable {m α β γ : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
end GramSubmodular
end GlobalTheory


