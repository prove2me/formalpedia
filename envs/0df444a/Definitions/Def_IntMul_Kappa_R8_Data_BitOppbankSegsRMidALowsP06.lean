-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP06
-- name    : IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP06
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T18:36:02.615428+00:00
-- url     : https://prove2.me/theorems/d3d3a9c1-7240-4a1c-be33-891b0996637d
-- title:
--   SegsR midA lows isStrictSorted / index-perm chunk pack 06
-- statement:
--   # SegsR midA lows isStrictSorted / index-perm chunk pack 06
--
--   Chunk pack 06 of densified midA lows: `sort_c = jx.map (fun i => midALowsFlat[i]!)` by rfl, `isStrictSorted` by rfl, and bounded indices. No mergeSort decide and no monolith Nodup. Later-segs midA helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP06`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP06. Later-segs midA helper only; not a full-word W1F certificate. Uses densified MidADataD / MidALowsIxData.

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

namespace IntMul.Kappa.R8.Bit.Oppbank.MidALowsP06

theorem sort_c12_eq : sort_c12 = jx_c12.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c12_sorted : isStrictSorted sort_c12 = true := rfl

theorem jx_c12_all : jx_c12.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c12_ne : sort_c12 ≠ [] := List.cons_ne_nil _ _

theorem sort_c12_last : sort_c12.getLast sort_c12_ne = 7578 := rfl

theorem sort_c12_hd : sort_c12.head sort_c12_ne = 7390 := rfl

theorem sort_c13_eq : sort_c13 = jx_c13.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c13_sorted : isStrictSorted sort_c13 = true := rfl

theorem jx_c13_all : jx_c13.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c13_ne : sort_c13 ≠ [] := List.cons_ne_nil _ _

theorem sort_c13_last : sort_c13.getLast sort_c13_ne = 7774 := rfl

theorem sort_c13_hd : sort_c13.head sort_c13_ne = 7579 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.MidALowsP06


