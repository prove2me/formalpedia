-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchroedingerOperatorHeisenbergPreservesSchwartzB
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchroedingerOperatorHeisenbergPreservesSchwartzB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:25.744903+00:00
-- url     : https://prove2.me/theorems/24302d2d-4afd-4c4e-8578-112e9e518563
-- title:
--   Schroedinger Operator Heisenberg Preserves Schwartz B
-- statement:
--   Definitions and structural lemmas for Schroedinger Operator Heisenberg Preserves Schwartz B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchroedingerOperatorHeisenbergPreservesSchwartzB.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsBisSide
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace SchrodingerSchwartzBruhat
section
open MeasureTheory Matrix
namespace GlobalTheory.CompanionTheory.SchrSB
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.CompanionTheory.SchrSB
end
end SchrodingerSchwartzBruhat
section
open MeasureTheory Matrix
end


