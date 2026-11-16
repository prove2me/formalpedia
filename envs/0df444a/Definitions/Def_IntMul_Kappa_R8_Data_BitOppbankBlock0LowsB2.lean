-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0LowsB2
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0LowsB2
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T16:32:46.784067+00:00
-- url     : https://prove2.me/theorems/5c55d0f1-7004-41ce-a91d-95fff46f3484
-- title:
--   Block-0 lows index certificates, chunks 13–14
-- statement:
--   # Block-0 lows certificates, chunks 13–14
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

namespace IntMul.Kappa.R8.Bit.Oppbank.Block0LowsB2

theorem sort_c13_eq : sort_c13 = jx_c13.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c13_sorted : isStrictSorted sort_c13 = true := rfl

theorem jx_c13_all : jx_c13.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c13_ne : sort_c13 ≠ [] := List.cons_ne_nil _ _

theorem sort_c13_last : sort_c13.getLast sort_c13_ne = 3511 := rfl

theorem sort_c13_hd : sort_c13.head sort_c13_ne = 3200 := rfl

theorem sort_c14_eq : sort_c14 = jx_c14.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c14_sorted : isStrictSorted sort_c14 = true := rfl

theorem jx_c14_all : jx_c14.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c14_ne : sort_c14 ≠ [] := List.cons_ne_nil _ _

theorem sort_c14_last : sort_c14.getLast sort_c14_ne = 3827 := rfl

theorem sort_c14_hd : sort_c14.head sort_c14_ne = 3512 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.Block0LowsB2


