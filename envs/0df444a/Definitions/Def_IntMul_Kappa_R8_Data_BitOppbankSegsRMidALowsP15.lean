-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP15
-- name    : IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP15
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T18:37:37.445536+00:00
-- url     : https://prove2.me/theorems/c15750c5-1963-4cd6-85f1-cf1d3a0df4d3
-- title:
--   SegsR midA lows isStrictSorted / index-perm chunk pack 15
-- statement:
--   # SegsR midA lows isStrictSorted / index-perm chunk pack 15
--
--   Chunk pack 15 of densified midA lows: `sort_c = jx.map (fun i => midALowsFlat[i]!)` by rfl, `isStrictSorted` by rfl, and bounded indices. No mergeSort decide and no monolith Nodup. Later-segs midA helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP15`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP15. Later-segs midA helper only; not a full-word W1F certificate. Uses densified MidADataD / MidALowsIxData.

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

namespace IntMul.Kappa.R8.Bit.Oppbank.MidALowsP15

theorem sort_c30_eq : sort_c30 = jx_c30.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c30_sorted : isStrictSorted sort_c30 = true := rfl

theorem jx_c30_all : jx_c30.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c30_ne : sort_c30 ≠ [] := List.cons_ne_nil _ _

theorem sort_c30_last : sort_c30.getLast sort_c30_ne = 11032 := rfl

theorem sort_c30_hd : sort_c30.head sort_c30_ne = 10845 := rfl

theorem sort_c31_eq : sort_c31 = jx_c31.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c31_sorted : isStrictSorted sort_c31 = true := rfl

theorem jx_c31_all : jx_c31.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c31_ne : sort_c31 ≠ [] := List.cons_ne_nil _ _

theorem sort_c31_last : sort_c31.getLast sort_c31_ne = 11087 := rfl

theorem sort_c31_hd : sort_c31.head sort_c31_ne = 11033 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.MidALowsP15


