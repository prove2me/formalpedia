-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralFourSq
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralFourSq
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T21:36:34.74287+00:00
-- url     : https://prove2.me/theorems/0799c755-c7fb-4524-8489-517d8e35eae9
-- title:
--   Lintegral Four Sq
-- statement:
--   Definitions and structural lemmas for Lintegral Four Sq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralFourSq.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BicharacterFourierTransformMemSchwartzBruhatStatement
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
noncomputable section
namespace GlobalTheory.KSp.Planch
variable {X : Type} [AddCommGroup X] [TopologicalSpace X]
end GlobalTheory.KSp.Planch
end


