-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP09
-- name    : IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP09
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T18:36:47.434695+00:00
-- url     : https://prove2.me/theorems/6f9ed353-3be9-4796-b087-36dea58d24ac
-- title:
--   SegsR midA lows isStrictSorted / index-perm chunk pack 09
-- statement:
--   # SegsR midA lows isStrictSorted / index-perm chunk pack 09
--
--   Chunk pack 09 of densified midA lows: `sort_c = jx.map (fun i => midALowsFlat[i]!)` by rfl, `isStrictSorted` by rfl, and bounded indices. No mergeSort decide and no monolith Nodup. Later-segs midA helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP09`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP09. Later-segs midA helper only; not a full-word W1F certificate. Uses densified MidADataD / MidALowsIxData.

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

namespace IntMul.Kappa.R8.Bit.Oppbank.MidALowsP09

theorem sort_c18_eq : sort_c18 = jx_c18.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c18_sorted : isStrictSorted sort_c18 = true := rfl

theorem jx_c18_all : jx_c18.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c18_ne : sort_c18 ≠ [] := List.cons_ne_nil _ _

theorem sort_c18_last : sort_c18.getLast sort_c18_ne = 8738 := rfl

theorem sort_c18_hd : sort_c18.head sort_c18_ne = 8547 := rfl

theorem sort_c19_eq : sort_c19 = jx_c19.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c19_sorted : isStrictSorted sort_c19 = true := rfl

theorem jx_c19_all : jx_c19.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c19_ne : sort_c19 ≠ [] := List.cons_ne_nil _ _

theorem sort_c19_last : sort_c19.getLast sort_c19_ne = 8931 := rfl

theorem sort_c19_hd : sort_c19.head sort_c19_ne = 8740 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.MidALowsP09


