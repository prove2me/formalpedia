-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEntireMellinSmoothedDirichletSum
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEntireMellinSmoothedDirichletSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:24.996449+00:00
-- url     : https://prove2.me/theorems/779adf1d-73ff-4be3-813e-6b048acbac6f
-- title:
--   Exists Entire Mellin Smoothed Dirichlet Sum
-- statement:
--   Definitions and structural lemmas for Exists Entire Mellin Smoothed Dirichlet Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsEntireMellinSmoothedDirichletSum.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open Set Filter Asymptotics Topology
namespace GlobalTheory.SmoothedSumMellin
end GlobalTheory.SmoothedSumMellin


