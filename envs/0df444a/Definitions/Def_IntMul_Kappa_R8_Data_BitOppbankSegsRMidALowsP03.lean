-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP03
-- name    : IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP03
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T18:37:13.01201+00:00
-- url     : https://prove2.me/theorems/66f2861c-2a0f-4916-a2f6-e427b85f7cba
-- title:
--   SegsR midA lows isStrictSorted / index-perm chunk pack 03
-- statement:
--   # SegsR midA lows isStrictSorted / index-perm chunk pack 03
--
--   Chunk pack 03 of densified midA lows: `sort_c = jx.map (fun i => midALowsFlat[i]!)` by rfl, `isStrictSorted` by rfl, and bounded indices. No mergeSort decide and no monolith Nodup. Later-segs midA helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP03`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP03. Later-segs midA helper only; not a full-word W1F certificate. Uses densified MidADataD / MidALowsIxData.

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

namespace IntMul.Kappa.R8.Bit.Oppbank.MidALowsP03

theorem sort_c06_eq : sort_c06 = jx_c06.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c06_sorted : isStrictSorted sort_c06 = true := rfl

theorem jx_c06_all : jx_c06.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c06_ne : sort_c06 ≠ [] := List.cons_ne_nil _ _

theorem sort_c06_last : sort_c06.getLast sort_c06_ne = 5393 := rfl

theorem sort_c06_hd : sort_c06.head sort_c06_ne = 4789 := rfl

theorem sort_c07_eq : sort_c07 = jx_c07.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c07_sorted : isStrictSorted sort_c07 = true := rfl

theorem jx_c07_all : jx_c07.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c07_ne : sort_c07 ≠ [] := List.cons_ne_nil _ _

theorem sort_c07_last : sort_c07.getLast sort_c07_ne = 5888 := rfl

theorem sort_c07_hd : sort_c07.head sort_c07_ne = 5399 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.MidALowsP03


