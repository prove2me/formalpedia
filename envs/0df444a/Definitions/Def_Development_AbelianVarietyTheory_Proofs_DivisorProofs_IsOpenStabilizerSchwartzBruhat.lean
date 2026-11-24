-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenStabilizerSchwartzBruhat
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenStabilizerSchwartzBruhat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:53.941799+00:00
-- url     : https://prove2.me/theorems/be2fedda-b814-4671-9a1d-35ee6fcf7136
-- title:
--   Is Open Stabilizer Schwartz Bruhat
-- statement:
--   Definitions and structural lemmas for Is Open Stabilizer Schwartz Bruhat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenStabilizerSchwartzBruhat.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM
namespace GlobalTheory.OmAStab
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.OmAStab


