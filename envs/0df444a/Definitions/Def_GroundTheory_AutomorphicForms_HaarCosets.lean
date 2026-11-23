-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HaarCosets
-- name    : GroundTheory_AutomorphicForms_HaarCosets
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:29.883889+00:00
-- url     : https://prove2.me/theorems/9f9369b6-2842-4389-bfa4-2522f68f889f
-- title:
--   Haar Cosets
-- statement:
--   Definitions and structural lemmas for Haar Cosets, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HaarCosets.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
open Set Filter Topology MeasureTheory
open scoped Pointwise ENNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
section Integral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [IsFiniteMeasureOnCompacts μ]
end Integral
end GroundTheory.Automorphic


