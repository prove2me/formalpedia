-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianUnitaryGroupOneParameterChart
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianUnitaryGroupOneParameterChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:08:07.012434+00:00
-- url     : https://prove2.me/theorems/08760301-9af0-4582-b5ae-9e9cc934b6e4
-- title:
--   Hermitian Unitary Group One Parameter Chart
-- statement:
--   Definitions and structural lemmas for Hermitian Unitary Group One Parameter Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianUnitaryGroupOneParameterChart.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupSecondKindCoordinatesNearOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
noncomputable section
namespace GlobalTheory.UnitaryGroupChart
open Filter
section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end
end GlobalTheory.UnitaryGroupChart


