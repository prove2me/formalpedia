-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP13
-- name    : IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP13
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T18:37:19.881885+00:00
-- url     : https://prove2.me/theorems/3be4cf7d-5ea6-480b-a1e4-8c645341c757
-- title:
--   SegsR midA lows isStrictSorted / index-perm chunk pack 13
-- statement:
--   # SegsR midA lows isStrictSorted / index-perm chunk pack 13
--
--   Chunk pack 13 of densified midA lows: `sort_c = jx.map (fun i => midALowsFlat[i]!)` by rfl, `isStrictSorted` by rfl, and bounded indices. No mergeSort decide and no monolith Nodup. Later-segs midA helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP13`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP13. Later-segs midA helper only; not a full-word W1F certificate. Uses densified MidADataD / MidALowsIxData.

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

namespace IntMul.Kappa.R8.Bit.Oppbank.MidALowsP13

theorem sort_c26_eq : sort_c26 = jx_c26.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c26_sorted : isStrictSorted sort_c26 = true := rfl

theorem jx_c26_all : jx_c26.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c26_ne : sort_c26 ≠ [] := List.cons_ne_nil _ _

theorem sort_c26_last : sort_c26.getLast sort_c26_ne = 10274 := rfl

theorem sort_c26_hd : sort_c26.head sort_c26_ne = 10084 := rfl

theorem sort_c27_eq : sort_c27 = jx_c27.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c27_sorted : isStrictSorted sort_c27 = true := rfl

theorem jx_c27_all : jx_c27.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c27_ne : sort_c27 ≠ [] := List.cons_ne_nil _ _

theorem sort_c27_last : sort_c27.getLast sort_c27_ne = 10465 := rfl

theorem sort_c27_hd : sort_c27.head sort_c27_ne = 10276 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.MidALowsP13


