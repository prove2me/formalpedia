-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreMemInducedSpace
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreMemInducedSpace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:13:20.469319+00:00
-- url     : https://prove2.me/theorems/b748e8e7-1acd-4205-a856-6e933ed0039f
-- title:
--   Fibre Mem Induced Space
-- statement:
--   Definitions and structural lemmas for Fibre Mem Induced Space, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FibreMemInducedSpace.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.WeilM
namespace GlobalTheory.RankFibre
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
local notation:70 M:70 " ⬝ₘ " N:71 => HMul.hMul (self := Matrix.instHMulOfFintypeOfMulOfAddCommMonoid) M N
variable [MeasurableSpace k] [BorelSpace k]
end GlobalTheory.RankFibre


