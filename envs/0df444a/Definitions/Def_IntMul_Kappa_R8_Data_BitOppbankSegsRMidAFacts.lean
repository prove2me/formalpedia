-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidAFacts
-- name    : IntMul_Kappa_R8_Data_BitOppbankSegsRMidAFacts
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T18:21:39.59439+00:00
-- url     : https://prove2.me/theorems/4698c358-4d38-4431-9bcb-214a47fc2e41
-- title:
--   SegsR midA facts: midANf_sum = 3713
-- statement:
--   # SegsR midA facts: midANf_sum = 3713
--
--   Length and fresh-bound facts for the densified midA pack: (midAPack.map gateNf).sum = 3713 and midASlotBound ≤ midAFreshEnd. Later-segs midA helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankSegsRMidAFacts`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankSegsRMidAFacts. Later-segs midA helper only; not a full-word W1F certificate. Uses densified MidADataD.

-- Later-segs midA helper only; not a full-word W1F / segsR / preloadHits certificate.
-- Imports densified MidADataD (not raw-n MidAData).
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidADataD

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Gen (genF genStepF mvF)
open IntMul.Kappa.R8.Bit.Oppbank.Lab (ValidOn MovesV)
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (nestOK argRel isND)
open IntMul.Kappa.R8.Bit.Oppbank.QHNetRecR

theorem midANf_sum : (midAPack.map gateNf).sum = 3713 := rfl

theorem midASlotBound_le_freshEnd : midASlotBound ≤ midAFreshEnd := by
  rw [midASlotBound_eq, midAFreshEnd_eq]
  omega


