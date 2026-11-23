-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixOneParameterGroupEqExpOfContinuous
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixOneParameterGroupEqExpOfContinuous
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:06.832612+00:00
-- url     : https://prove2.me/theorems/2aa3add5-da12-4005-a1bb-020a68da828f
-- title:
--   Matrix One Parameter Group Eq Exp Of Continuous
-- statement:
--   Definitions and structural lemmas for Matrix One Parameter Group Eq Exp Of Continuous, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixOneParameterGroupEqExpOfContinuous.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtOneParameter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
namespace GlobalTheory.OneParamMatrix
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end GlobalTheory.OneParamMatrix


