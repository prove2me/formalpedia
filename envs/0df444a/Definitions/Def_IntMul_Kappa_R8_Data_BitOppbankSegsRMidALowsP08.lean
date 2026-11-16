-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP08
-- name    : IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP08
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T18:36:30.95036+00:00
-- url     : https://prove2.me/theorems/d2b59e72-a66c-4f41-83b4-d57d46ee36f6
-- title:
--   SegsR midA lows isStrictSorted / index-perm chunk pack 08
-- statement:
--   # SegsR midA lows isStrictSorted / index-perm chunk pack 08
--
--   Chunk pack 08 of densified midA lows: `sort_c = jx.map (fun i => midALowsFlat[i]!)` by rfl, `isStrictSorted` by rfl, and bounded indices. No mergeSort decide and no monolith Nodup. Later-segs midA helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP08`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP08. Later-segs midA helper only; not a full-word W1F certificate. Uses densified MidADataD / MidALowsIxData.

-- Later-segs midA helper only; not a full-word W1F certificate.
-- Index-perm / isStrictSorted chunk pack. No mergeSort decide, no monolith Nodup.
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0LowsData
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsIxData

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option autoImplicit false
set_option linter.unusedSimpArgs false

open IntMul.Kappa.R8.Bit.Oppbank.Block0LowsData (isStrictSorted)
open IntMul.Kappa.R8.Bit.Oppbank.MidALowsIxData

namespace IntMul.Kappa.R8.Bit.Oppbank.MidALowsP08

theorem sort_c16_eq : sort_c16 = jx_c16.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c16_sorted : isStrictSorted sort_c16 = true := rfl

theorem jx_c16_all : jx_c16.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c16_ne : sort_c16 ≠ [] := List.cons_ne_nil _ _

theorem sort_c16_last : sort_c16.getLast sort_c16_ne = 8350 := rfl

theorem sort_c16_hd : sort_c16.head sort_c16_ne = 8162 := rfl

theorem sort_c17_eq : sort_c17 = jx_c17.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c17_sorted : isStrictSorted sort_c17 = true := rfl

theorem jx_c17_all : jx_c17.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c17_ne : sort_c17 ≠ [] := List.cons_ne_nil _ _

theorem sort_c17_last : sort_c17.getLast sort_c17_ne = 8545 := rfl

theorem sort_c17_hd : sort_c17.head sort_c17_ne = 8353 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.MidALowsP08


