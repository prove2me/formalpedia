-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0LowsC2
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0LowsC2
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T16:33:30.291885+00:00
-- url     : https://prove2.me/theorems/30836f8f-715b-47f0-bf01-a8a5e4c89ff8
-- title:
--   Block-0 lows index certificates, chunks 22–23
-- statement:
--   # Block-0 lows certificates, chunks 22–23
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

namespace IntMul.Kappa.R8.Bit.Oppbank.Block0LowsC2

theorem sort_c22_eq : sort_c22 = jx_c22.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c22_sorted : isStrictSorted sort_c22 = true := rfl

theorem jx_c22_all : jx_c22.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c22_ne : sort_c22 ≠ [] := List.cons_ne_nil _ _

theorem sort_c22_last : sort_c22.getLast sort_c22_ne = 6065 := rfl

theorem sort_c22_hd : sort_c22.head sort_c22_ne = 5790 := rfl

theorem sort_c23_eq : sort_c23 = jx_c23.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c23_sorted : isStrictSorted sort_c23 = true := rfl

theorem jx_c23_all : jx_c23.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c23_ne : sort_c23 ≠ [] := List.cons_ne_nil _ _

theorem sort_c23_last : sort_c23.getLast sort_c23_ne = 6377 := rfl

theorem sort_c23_hd : sort_c23.head sort_c23_ne = 6066 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.Block0LowsC2


