-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP04
-- name    : IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP04
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T18:36:13.784199+00:00
-- url     : https://prove2.me/theorems/2db4060a-3d7a-4b26-897e-186f99ac2f17
-- title:
--   SegsR midA lows isStrictSorted / index-perm chunk pack 04
-- statement:
--   # SegsR midA lows isStrictSorted / index-perm chunk pack 04
--
--   Chunk pack 04 of densified midA lows: `sort_c = jx.map (fun i => midALowsFlat[i]!)` by rfl, `isStrictSorted` by rfl, and bounded indices. No mergeSort decide and no monolith Nodup. Later-segs midA helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP04`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP04. Later-segs midA helper only; not a full-word W1F certificate. Uses densified MidADataD / MidALowsIxData.

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

namespace IntMul.Kappa.R8.Bit.Oppbank.MidALowsP04

theorem sort_c08_eq : sort_c08 = jx_c08.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c08_sorted : isStrictSorted sort_c08 = true := rfl

theorem jx_c08_all : jx_c08.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c08_ne : sort_c08 ≠ [] := List.cons_ne_nil _ _

theorem sort_c08_last : sort_c08.getLast sort_c08_ne = 6484 := rfl

theorem sort_c08_hd : sort_c08.head sort_c08_ne = 5894 := rfl

theorem sort_c09_eq : sort_c09 = jx_c09.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c09_sorted : isStrictSorted sort_c09 = true := rfl

theorem jx_c09_all : jx_c09.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c09_ne : sort_c09 ≠ [] := List.cons_ne_nil _ _

theorem sort_c09_last : sort_c09.getLast sort_c09_ne = 6844 := rfl

theorem sort_c09_hd : sort_c09.head sort_c09_ne = 6485 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.MidALowsP04


