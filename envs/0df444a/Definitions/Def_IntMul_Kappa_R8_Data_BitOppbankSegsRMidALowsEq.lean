-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsEq
-- name    : IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsEq
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T18:36:27.560203+00:00
-- url     : https://prove2.me/theorems/de6273cd-d122-4969-a59c-7171f6acf930
-- title:
--   SegsR midA lows: midALows equals explicit midALowsFlat
-- statement:
--   # SegsR midA lows: midALows equals explicit midALowsFlat
--
--   Equation `midALows = midALowsFlat`, identifying the densified midAPack flatMap with the explicit 3128-element list used by the index-perm Nodup packs. Later-segs midA helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsEq`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsEq. Later-segs midA helper only; not a full-word W1F certificate. Uses densified MidADataD / MidALowsIxData.

-- Later-segs midA helper only; not a full-word W1F certificate.
-- Equates midALows (flatMap of densified midAPack) with the explicit midALowsFlat list.
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsData
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsIxData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.QHNetRecR
open IntMul.Kappa.R8.Bit.Oppbank.MidALowsIxData

theorem midALows_eq_flat : midALows = midALowsFlat := rfl


