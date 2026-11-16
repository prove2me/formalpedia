-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP00
-- name    : IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP00
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T18:36:09.157061+00:00
-- url     : https://prove2.me/theorems/e958ede8-04e6-4fab-a81f-022c6419f93e
-- title:
--   SegsR midA lows isStrictSorted / index-perm chunk pack 00
-- statement:
--   # SegsR midA lows isStrictSorted / index-perm chunk pack 00
--
--   Chunk pack 00 of densified midA lows: `sort_c = jx.map (fun i => midALowsFlat[i]!)` by rfl, `isStrictSorted` by rfl, and bounded indices. No mergeSort decide and no monolith Nodup. Later-segs midA helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP00`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP00. Later-segs midA helper only; not a full-word W1F certificate. Uses densified MidADataD / MidALowsIxData.

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

namespace IntMul.Kappa.R8.Bit.Oppbank.MidALowsP00

theorem sort_c00_eq : sort_c00 = jx_c00.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c00_sorted : isStrictSorted sort_c00 = true := rfl

theorem jx_c00_all : jx_c00.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c00_ne : sort_c00 ≠ [] := List.cons_ne_nil _ _

theorem sort_c00_last : sort_c00.getLast sort_c00_ne = 1116 := rfl

theorem sort_c00_hd : sort_c00.head sort_c00_ne = 33 := rfl

theorem sort_c01_eq : sort_c01 = jx_c01.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c01_sorted : isStrictSorted sort_c01 = true := rfl

theorem jx_c01_all : jx_c01.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c01_ne : sort_c01 ≠ [] := List.cons_ne_nil _ _

theorem sort_c01_last : sort_c01.getLast sort_c01_ne = 2136 := rfl

theorem sort_c01_hd : sort_c01.head sort_c01_ne = 1122 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.MidALowsP00


