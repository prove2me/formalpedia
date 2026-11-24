-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierIntertwinesWeylHeisenbergSchrodingerStatement
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierIntertwinesWeylHeisenbergSchrodingerStatement
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:08:26.948349+00:00
-- url     : https://prove2.me/theorems/6fddef8b-4e32-45e1-aeb8-4d711af35f53
-- title:
--   Fourier Intertwines Weyl Heisenberg Schrodinger Statement
-- statement:
--   Definitions and structural lemmas for Fourier Intertwines Weyl Heisenberg Schrodinger Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FourierIntertwinesWeylHeisenbergSchrodingerStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierIntertwinesWeylHeisenbergSchrodinger
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


