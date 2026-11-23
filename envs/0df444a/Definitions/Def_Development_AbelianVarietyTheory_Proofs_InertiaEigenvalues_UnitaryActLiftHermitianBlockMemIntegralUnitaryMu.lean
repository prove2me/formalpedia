-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActLiftHermitianBlockMemIntegralUnitaryMu
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActLiftHermitianBlockMemIntegralUnitaryMu
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:42.312789+00:00
-- url     : https://prove2.me/theorems/45d54dae-d2cc-4e10-a3b6-96b4a62f21ce
-- title:
--   Unitary Act Lift Hermitian Block Mem Integral Unitary Mu
-- statement:
--   Definitions and structural lemmas for Unitary Act Lift Hermitian Block Mem Integral Unitary Mu, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActLiftHermitianBlockMemIntegralUnitaryMu.lean

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralUnitaryGroupTransitiveNormOneVectorsStatement
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
namespace GlobalTheory.JR.Step
section Blocks
variable {r : ℕ} {E : Type} [Field E]
end Blocks
end GlobalTheory.JR.Step
namespace GlobalTheory.JR.Step
section Main
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
  [StarRing E] [Unram F E]
end Main
end GlobalTheory.JR.Step


