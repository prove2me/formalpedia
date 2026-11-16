-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP07
-- name    : IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP07
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T18:36:19.644494+00:00
-- url     : https://prove2.me/theorems/28c9db4f-b9ce-4b5c-b83d-1597f4547812
-- title:
--   SegsR midA lows isStrictSorted / index-perm chunk pack 07
-- statement:
--   # SegsR midA lows isStrictSorted / index-perm chunk pack 07
--
--   Chunk pack 07 of densified midA lows: `sort_c = jx.map (fun i => midALowsFlat[i]!)` by rfl, `isStrictSorted` by rfl, and bounded indices. No mergeSort decide and no monolith Nodup. Later-segs midA helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP07`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP07. Later-segs midA helper only; not a full-word W1F certificate. Uses densified MidADataD / MidALowsIxData.

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

namespace IntMul.Kappa.R8.Bit.Oppbank.MidALowsP07

theorem sort_c14_eq : sort_c14 = jx_c14.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c14_sorted : isStrictSorted sort_c14 = true := rfl

theorem jx_c14_all : jx_c14.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c14_ne : sort_c14 ≠ [] := List.cons_ne_nil _ _

theorem sort_c14_last : sort_c14.getLast sort_c14_ne = 7968 := rfl

theorem sort_c14_hd : sort_c14.head sort_c14_ne = 7775 := rfl

theorem sort_c15_eq : sort_c15 = jx_c15.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c15_sorted : isStrictSorted sort_c15 = true := rfl

theorem jx_c15_all : jx_c15.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c15_ne : sort_c15 ≠ [] := List.cons_ne_nil _ _

theorem sort_c15_last : sort_c15.getLast sort_c15_ne = 8161 := rfl

theorem sort_c15_hd : sort_c15.head sort_c15_ne = 7971 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.MidALowsP07


