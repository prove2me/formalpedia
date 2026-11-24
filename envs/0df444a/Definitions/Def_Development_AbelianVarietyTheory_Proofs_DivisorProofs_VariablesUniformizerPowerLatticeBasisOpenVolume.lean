-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VariablesUniformizerPowerLatticeBasisOpenVolume
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_VariablesUniformizerPowerLatticeBasisOpenVolume
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T22:25:49.136317+00:00
-- url     : https://prove2.me/theorems/a34d4a9a-826b-41df-b81b-c8989b1007d1
-- title:
--   Variables Uniformizer Power Lattice Basis Open Volume
-- statement:
--   Definitions and structural lemmas for Variables Uniformizer Power Lattice Basis Open Volume, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/VariablesUniformizerPowerLatticeBasisOpenVolume.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemVarLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.UnfoldLoss
namespace GlobalTheory.UnfoldLoss.LatVol
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.UnfoldLoss.LatVol


