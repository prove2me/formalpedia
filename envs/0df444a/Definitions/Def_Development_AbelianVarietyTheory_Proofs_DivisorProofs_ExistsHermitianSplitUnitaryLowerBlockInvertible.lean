-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianSplitUnitaryLowerBlockInvertible
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianSplitUnitaryLowerBlockInvertible
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T21:10:38.380646+00:00
-- url     : https://prove2.me/theorems/37c21693-937d-4ab4-b309-e6d58d7421e8
-- title:
--   Exists Hermitian Split Unitary Lower Block Invertible
-- statement:
--   Definitions and structural lemmas for Exists Hermitian Split Unitary Lower Block Invertible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHermitianSplitUnitaryLowerBlockInvertible.lean

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
namespace GlobalTheory.KSp
section Transverse
variable {k : Type} [Field k] {ν : Type} [Fintype ν] [DecidableEq ν]
def transvRankOne (S : Matrix ν ν k) (j : ν) : Matrix ν ν k :=
  Matrix.of fun a b => if a = j then S b j else 0
end Transverse
end GlobalTheory.KSp
namespace GlobalTheory.KSp
end GlobalTheory.KSp


