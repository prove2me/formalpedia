-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP12
-- name    : IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP12
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T18:37:38.567856+00:00
-- url     : https://prove2.me/theorems/d408af27-f110-4862-bf0a-9e03a65103f9
-- title:
--   SegsR midA lows isStrictSorted / index-perm chunk pack 12
-- statement:
--   # SegsR midA lows isStrictSorted / index-perm chunk pack 12
--
--   Chunk pack 12 of densified midA lows: `sort_c = jx.map (fun i => midALowsFlat[i]!)` by rfl, `isStrictSorted` by rfl, and bounded indices. No mergeSort decide and no monolith Nodup. Later-segs midA helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP12`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP12. Later-segs midA helper only; not a full-word W1F certificate. Uses densified MidADataD / MidALowsIxData.

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

namespace IntMul.Kappa.R8.Bit.Oppbank.MidALowsP12

theorem sort_c24_eq : sort_c24 = jx_c24.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c24_sorted : isStrictSorted sort_c24 = true := rfl

theorem jx_c24_all : jx_c24.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c24_ne : sort_c24 ≠ [] := List.cons_ne_nil _ _

theorem sort_c24_last : sort_c24.getLast sort_c24_ne = 9892 := rfl

theorem sort_c24_hd : sort_c24.head sort_c24_ne = 9700 := rfl

theorem sort_c25_eq : sort_c25 = jx_c25.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c25_sorted : isStrictSorted sort_c25 = true := rfl

theorem jx_c25_all : jx_c25.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c25_ne : sort_c25 ≠ [] := List.cons_ne_nil _ _

theorem sort_c25_last : sort_c25.getLast sort_c25_ne = 10082 := rfl

theorem sort_c25_hd : sort_c25.head sort_c25_ne = 9893 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.MidALowsP12


