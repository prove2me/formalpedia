-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelThreeSeparatesTangents
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelThreeSeparatesTangents
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:12.04866+00:00
-- url     : https://prove2.me/theorems/3811d4ec-4a99-452b-abc0-8a4fdc0178dd
-- title:
--   Level Three Separates Tangents
-- statement:
--   Definitions and structural lemmas for Level Three Separates Tangents, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LevelThreeSeparatesTangents.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2 Filter Topology
namespace GlobalTheory
section Affine
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
end Affine
variable {ι : Type} [Fintype ι]
end GlobalTheory


