-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasGaussIntegralCompAddEquivRescaleStatement
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasGaussIntegralCompAddEquivRescaleStatement
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T21:22:52.529394+00:00
-- url     : https://prove2.me/theorems/af0d191b-6a37-4117-9f05-e47003f704d3
-- title:
--   Has Gauss Integral Comp Add Equiv Rescale Statement
-- statement:
--   Definitions and structural lemmas for Has Gauss Integral Comp Add Equiv Rescale Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasGaussIntegralCompAddEquivRescaleStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasGaussIntegralCompAddEquivRescale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)


