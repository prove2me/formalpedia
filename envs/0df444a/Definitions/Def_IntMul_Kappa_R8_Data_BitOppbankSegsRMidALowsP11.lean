-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP11
-- name    : IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP11
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T18:37:12.562197+00:00
-- url     : https://prove2.me/theorems/6bcb9869-59c6-443d-9a75-6652cbb40a95
-- title:
--   SegsR midA lows isStrictSorted / index-perm chunk pack 11
-- statement:
--   # SegsR midA lows isStrictSorted / index-perm chunk pack 11
--
--   Chunk pack 11 of densified midA lows: `sort_c = jx.map (fun i => midALowsFlat[i]!)` by rfl, `isStrictSorted` by rfl, and bounded indices. No mergeSort decide and no monolith Nodup. Later-segs midA helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP11`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP11. Later-segs midA helper only; not a full-word W1F certificate. Uses densified MidADataD / MidALowsIxData.

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

namespace IntMul.Kappa.R8.Bit.Oppbank.MidALowsP11

theorem sort_c22_eq : sort_c22 = jx_c22.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c22_sorted : isStrictSorted sort_c22 = true := rfl

theorem jx_c22_all : jx_c22.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c22_ne : sort_c22 ≠ [] := List.cons_ne_nil _ _

theorem sort_c22_last : sort_c22.getLast sort_c22_ne = 9509 := rfl

theorem sort_c22_hd : sort_c22.head sort_c22_ne = 9309 := rfl

theorem sort_c23_eq : sort_c23 = jx_c23.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c23_sorted : isStrictSorted sort_c23 = true := rfl

theorem jx_c23_all : jx_c23.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c23_ne : sort_c23 ≠ [] := List.cons_ne_nil _ _

theorem sort_c23_last : sort_c23.getLast sort_c23_ne = 9697 := rfl

theorem sort_c23_hd : sort_c23.head sort_c23_ne = 9510 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.MidALowsP11


