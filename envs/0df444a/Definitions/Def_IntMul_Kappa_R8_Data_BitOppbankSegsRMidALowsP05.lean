-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP05
-- name    : IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP05
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T18:35:39.039019+00:00
-- url     : https://prove2.me/theorems/a2f8ef2b-f089-4ecf-b76b-5518d5e25523
-- title:
--   SegsR midA lows isStrictSorted / index-perm chunk pack 05
-- statement:
--   # SegsR midA lows isStrictSorted / index-perm chunk pack 05
--
--   Chunk pack 05 of densified midA lows: `sort_c = jx.map (fun i => midALowsFlat[i]!)` by rfl, `isStrictSorted` by rfl, and bounded indices. No mergeSort decide and no monolith Nodup. Later-segs midA helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP05`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP05. Later-segs midA helper only; not a full-word W1F certificate. Uses densified MidADataD / MidALowsIxData.

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

namespace IntMul.Kappa.R8.Bit.Oppbank.MidALowsP05

theorem sort_c10_eq : sort_c10 = jx_c10.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c10_sorted : isStrictSorted sort_c10 = true := rfl

theorem jx_c10_all : jx_c10.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c10_ne : sort_c10 ≠ [] := List.cons_ne_nil _ _

theorem sort_c10_last : sort_c10.getLast sort_c10_ne = 7118 := rfl

theorem sort_c10_hd : sort_c10.head sort_c10_ne = 6846 := rfl

theorem sort_c11_eq : sort_c11 = jx_c11.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c11_sorted : isStrictSorted sort_c11 = true := rfl

theorem jx_c11_all : jx_c11.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c11_ne : sort_c11 ≠ [] := List.cons_ne_nil _ _

theorem sort_c11_last : sort_c11.getLast sort_c11_ne = 7388 := rfl

theorem sort_c11_hd : sort_c11.head sort_c11_ne = 7120 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.MidALowsP05


