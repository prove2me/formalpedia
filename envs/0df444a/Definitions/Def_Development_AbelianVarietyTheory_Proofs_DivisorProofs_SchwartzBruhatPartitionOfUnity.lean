-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatPartitionOfUnity
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatPartitionOfUnity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:17.575463+00:00
-- url     : https://prove2.me/theorems/999c1d2d-279f-438e-9563-7781025234c8
-- title:
--   Schwartz Bruhat Partition Of Unity
-- statement:
--   Definitions and structural lemmas for Schwartz Bruhat Partition Of Unity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzBruhatPartitionOfUnity.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Matrix
open scoped Topology
noncomputable section
namespace GlobalTheory.CoverSB
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.CoverSB
namespace GlobalTheory.CoverSB
end GlobalTheory.CoverSB


