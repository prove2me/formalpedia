-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP02
-- name    : IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP02
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T18:36:47.851394+00:00
-- url     : https://prove2.me/theorems/74e1fee4-03b9-495f-aa89-e501a96967ae
-- title:
--   SegsR midA lows isStrictSorted / index-perm chunk pack 02
-- statement:
--   # SegsR midA lows isStrictSorted / index-perm chunk pack 02
--
--   Chunk pack 02 of densified midA lows: `sort_c = jx.map (fun i => midALowsFlat[i]!)` by rfl, `isStrictSorted` by rfl, and bounded indices. No mergeSort decide and no monolith Nodup. Later-segs midA helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP02`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankSegsRMidALowsP02. Later-segs midA helper only; not a full-word W1F certificate. Uses densified MidADataD / MidALowsIxData.

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

namespace IntMul.Kappa.R8.Bit.Oppbank.MidALowsP02

theorem sort_c04_eq : sort_c04 = jx_c04.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c04_sorted : isStrictSorted sort_c04 = true := rfl

theorem jx_c04_all : jx_c04.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c04_ne : sort_c04 ≠ [] := List.cons_ne_nil _ _

theorem sort_c04_last : sort_c04.getLast sort_c04_ne = 4267 := rfl

theorem sort_c04_hd : sort_c04.head sort_c04_ne = 3495 := rfl

theorem sort_c05_eq : sort_c05 = jx_c05.map (fun i => midALowsFlat[i]!) := rfl

theorem sort_c05_sorted : isStrictSorted sort_c05 = true := rfl

theorem jx_c05_all : jx_c05.all (fun i => decide (i < 3128)) = true := rfl

theorem sort_c05_ne : sort_c05 ≠ [] := List.cons_ne_nil _ _

theorem sort_c05_last : sort_c05.getLast sort_c05_ne = 4788 := rfl

theorem sort_c05_hd : sort_c05.head sort_c05_ne = 4273 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.MidALowsP02


