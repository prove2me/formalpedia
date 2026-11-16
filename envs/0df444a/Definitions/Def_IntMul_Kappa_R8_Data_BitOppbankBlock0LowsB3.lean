-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0LowsB3
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0LowsB3
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T16:34:12.092387+00:00
-- url     : https://prove2.me/theorems/16dabfa1-9319-4260-a102-4ed7f168493b
-- title:
--   Block-0 lows index certificates, chunks 15–17
-- statement:
--   # Block-0 lows certificates, chunks 15–17
--
--   Chunk certificates for the published `Block0LowsData` pack. Prefix / block-0 helper only; not a full-word W1F certificate.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: block-0 chunk certificates. Prefix / block-0 pack only; not a full-word W1F certificate.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0LowsData

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option autoImplicit false
set_option linter.unusedSimpArgs false

open IntMul.Kappa.R8.Bit.Oppbank.Block0LowsData

namespace IntMul.Kappa.R8.Bit.Oppbank.Block0LowsB3

theorem sort_c15_eq : sort_c15 = jx_c15.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c15_sorted : isStrictSorted sort_c15 = true := rfl

theorem jx_c15_all : jx_c15.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c15_ne : sort_c15 ≠ [] := List.cons_ne_nil _ _

theorem sort_c15_last : sort_c15.getLast sort_c15_ne = 4064 := rfl

theorem sort_c15_hd : sort_c15.head sort_c15_ne = 3832 := rfl

theorem sort_c16_eq : sort_c16 = jx_c16.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c16_sorted : isStrictSorted sort_c16 = true := rfl

theorem jx_c16_all : jx_c16.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c16_ne : sort_c16 ≠ [] := List.cons_ne_nil _ _

theorem sort_c16_last : sort_c16.getLast sort_c16_ne = 4288 := rfl

theorem sort_c16_hd : sort_c16.head sort_c16_ne = 4066 := rfl

theorem sort_c17_eq : sort_c17 = jx_c17.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c17_sorted : isStrictSorted sort_c17 = true := rfl

theorem jx_c17_all : jx_c17.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c17_ne : sort_c17 ≠ [] := List.cons_ne_nil _ _

theorem sort_c17_last : sort_c17.getLast sort_c17_ne = 4600 := rfl

theorem sort_c17_hd : sort_c17.head sort_c17_ne = 4289 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.Block0LowsB3


