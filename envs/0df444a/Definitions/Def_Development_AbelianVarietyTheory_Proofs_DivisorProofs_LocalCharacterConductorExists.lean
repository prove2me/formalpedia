-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalCharacterConductorExists
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalCharacterConductorExists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:53.863528+00:00
-- url     : https://prove2.me/theorems/1e15c32c-f852-4d1e-94ab-72037768bc9d
-- title:
--   Local Character Conductor Exists
-- statement:
--   Definitions and structural lemmas for Local Character Conductor Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalCharacterConductorExists.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel
open scoped Matrix Topology
noncomputable section
namespace GlobalTheory.CondRescale
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.CondRescale


