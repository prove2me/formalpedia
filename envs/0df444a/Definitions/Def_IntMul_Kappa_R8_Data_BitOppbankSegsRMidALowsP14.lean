-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP14
-- name    : IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP14
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T18:37:53.630795+00:00
-- url     : https://prove2.me/theorems/56d1d80b-7b5a-4bee-b85b-bf915890190e
-- title:
--   SegsR midA lows isStrictSorted / index-perm chunk pack 14
-- statement:
--   # SegsR midA lows isStrictSorted / index-perm chunk pack 14
--
--   Chunk pack 14 of densified midA lows: `sort_c = jx.map (fun i => midALowsFlat[i]!)` by rfl, `isStrictSorted` by rfl, and bounded indices. No mergeSort decide and no monolith Nodup. Later-segs midA helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP14`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP14. Later-segs midA helper only; not a full-word W1F certificate. Uses densified MidADataD / MidALowsIxData.

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

namespace IntMul.Kappa.R8.Bit.Oppbank.MidALowsP14

theorem sort_c28_eq : sort_c28 = jx_c28.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c28_sorted : isStrictSorted sort_c28 = true := rfl

theorem jx_c28_all : jx_c28.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c28_ne : sort_c28 ≠ [] := List.cons_ne_nil _ _

theorem sort_c28_last : sort_c28.getLast sort_c28_ne = 10657 := rfl

theorem sort_c28_hd : sort_c28.head sort_c28_ne = 10466 := rfl

theorem sort_c29_eq : sort_c29 = jx_c29.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c29_sorted : isStrictSorted sort_c29 = true := rfl

theorem jx_c29_all : jx_c29.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c29_ne : sort_c29 ≠ [] := List.cons_ne_nil _ _

theorem sort_c29_last : sort_c29.getLast sort_c29_ne = 10843 := rfl

theorem sort_c29_hd : sort_c29.head sort_c29_ne = 10658 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.MidALowsP14


