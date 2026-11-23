-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryOrbitNormalFormUnitInvariant
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryOrbitNormalFormUnitInvariant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:42.383116+00:00
-- url     : https://prove2.me/theorems/e97bef10-97e0-4660-81be-3148d011c462
-- title:
--   Unitary Orbit Normal Form Unit Invariant
-- statement:
--   Definitions and structural lemmas for Unitary Orbit Normal Form Unit Invariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryOrbitNormalFormUnitInvariant.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjTransposeVecMulVecSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.JR.Step.UNormal
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
  [StarRing E] [Unram F E]
end GlobalTheory.JR.Step.UNormal
noncomputable section
namespace GlobalTheory.JR.Step.UNormal
section Full
variable {r : ℕ} {k : Type} [CommRing k]
end Full
end GlobalTheory.JR.Step.UNormal
noncomputable section
namespace GlobalTheory.JR.Step
end GlobalTheory.JR.Step


