-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_AnalyticHypoSeries
-- name    : GroundTheory_AutomorphicForms_PartialDifferential_AnalyticHypoSeries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:58.626882+00:00
-- url     : https://prove2.me/theorems/1ecbc63c-bc1f-412b-9fa1-451c5b7a551d
-- title:
--   Analytic Hypo Series
-- statement:
--   Definitions and structural lemmas for Analytic Hypo Series, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/AnalyticHypoSeries.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic.Sobolev
open scoped ContDiff NNReal ENNReal Topology
open Set Filter
noncomputable section
section Converse
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
end Converse
section Forward
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]
end Forward
end
end GroundTheory.Automorphic.Sobolev


