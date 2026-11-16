-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsData
-- name    : IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsData
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T18:22:26.982086+00:00
-- url     : https://prove2.me/theorems/ebe23aa2-7408-43f1-a5ec-a8280102bf78
-- title:
--   SegsR midA lows list and length
-- statement:
--   # SegsR midA lows list and length
--
--   The densified midA lows list `midALows = midAPack.flatMap (fun g => [gatePiv g, gateBp g - 1])` together with `midALows.length = 3128`. Nodup is proved in later split packs, not here. Later-segs midA helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsData`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsData. Later-segs midA helper only; not a full-word W1F certificate. Uses densified MidADataD.

-- Later-segs midA helper only; not a full-word W1F / segsR / preloadHits certificate.
-- Imports densified MidADataD (not raw-n MidAData).
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidADataD

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.QHNetRecR

/-- Pivot and bp-1 lows of densified midAPack, in pack order. -/
def midALows : List ℕ := midAPack.flatMap (fun g => [gatePiv g, gateBp g - 1])

theorem midALows_len : midALows.length = 3128 := rfl


