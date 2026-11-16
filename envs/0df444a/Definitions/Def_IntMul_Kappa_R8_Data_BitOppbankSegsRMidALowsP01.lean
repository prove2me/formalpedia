-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP01
-- name    : IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP01
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T18:36:50.282304+00:00
-- url     : https://prove2.me/theorems/ffbb5950-21bf-4c72-9af8-91c0482f77a2
-- title:
--   SegsR midA lows isStrictSorted / index-perm chunk pack 01
-- statement:
--   # SegsR midA lows isStrictSorted / index-perm chunk pack 01
--
--   Chunk pack 01 of densified midA lows: `sort_c = jx.map (fun i => midALowsFlat[i]!)` by rfl, `isStrictSorted` by rfl, and bounded indices. No mergeSort decide and no monolith Nodup. Later-segs midA helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP01`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP01. Later-segs midA helper only; not a full-word W1F certificate. Uses densified MidADataD / MidALowsIxData.

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

namespace IntMul.Kappa.R8.Bit.Oppbank.MidALowsP01

theorem sort_c02_eq : sort_c02 = jx_c02.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c02_sorted : isStrictSorted sort_c02 = true := rfl

theorem jx_c02_all : jx_c02.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c02_ne : sort_c02 ≠ [] := List.cons_ne_nil _ _

theorem sort_c02_last : sort_c02.getLast sort_c02_ne = 2647 := rfl

theorem sort_c02_hd : sort_c02.head sort_c02_ne = 2142 := rfl

theorem sort_c03_eq : sort_c03 = jx_c03.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c03_sorted : isStrictSorted sort_c03 = true := rfl

theorem jx_c03_all : jx_c03.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c03_ne : sort_c03 ≠ [] := List.cons_ne_nil _ _

theorem sort_c03_last : sort_c03.getLast sort_c03_ne = 3489 := rfl

theorem sort_c03_hd : sort_c03.head sort_c03_ne = 2653 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.MidALowsP01


