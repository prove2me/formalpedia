-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP10
-- name    : IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP10
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T18:37:21.64277+00:00
-- url     : https://prove2.me/theorems/7fc6c77e-5fc3-42a1-9e7e-e0313edaf78c
-- title:
--   SegsR midA lows isStrictSorted / index-perm chunk pack 10
-- statement:
--   # SegsR midA lows isStrictSorted / index-perm chunk pack 10
--
--   Chunk pack 10 of densified midA lows: `sort_c = jx.map (fun i => midALowsFlat[i]!)` by rfl, `isStrictSorted` by rfl, and bounded indices. No mergeSort decide and no monolith Nodup. Later-segs midA helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP10`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP10. Later-segs midA helper only; not a full-word W1F certificate. Uses densified MidADataD / MidALowsIxData.

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

namespace IntMul.Kappa.R8.Bit.Oppbank.MidALowsP10

theorem sort_c20_eq : sort_c20 = jx_c20.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c20_sorted : isStrictSorted sort_c20 = true := rfl

theorem jx_c20_all : jx_c20.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c20_ne : sort_c20 ≠ [] := List.cons_ne_nil _ _

theorem sort_c20_last : sort_c20.getLast sort_c20_ne = 9124 := rfl

theorem sort_c20_hd : sort_c20.head sort_c20_ne = 8932 := rfl

theorem sort_c21_eq : sort_c21 = jx_c21.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c21_sorted : isStrictSorted sort_c21 = true := rfl

theorem jx_c21_all : jx_c21.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c21_ne : sort_c21 ≠ [] := List.cons_ne_nil _ _

theorem sort_c21_last : sort_c21.getLast sort_c21_ne = 9308 := rfl

theorem sort_c21_hd : sort_c21.head sort_c21_ne = 9126 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.MidALowsP10


