-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0LowsC3
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0LowsC3
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T16:33:42.731822+00:00
-- url     : https://prove2.me/theorems/37e70f34-802d-4092-b641-9e4b445ed114
-- title:
--   Block-0 lows index certificates, chunks 20–21
-- statement:
--   # Block-0 lows certificates, chunks 20–21
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

namespace IntMul.Kappa.R8.Bit.Oppbank.Block0LowsC3

theorem sort_c20_eq : sort_c20 = jx_c20.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c20_sorted : isStrictSorted sort_c20 = true := rfl

theorem jx_c20_all : jx_c20.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c20_ne : sort_c20 ≠ [] := List.cons_ne_nil _ _

theorem sort_c20_last : sort_c20.getLast sort_c20_ne = 5476 := rfl

theorem sort_c20_hd : sort_c20.head sort_c20_ne = 5173 := rfl

theorem sort_c21_eq : sort_c21 = jx_c21.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c21_sorted : isStrictSorted sort_c21 = true := rfl

theorem jx_c21_all : jx_c21.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c21_ne : sort_c21 ≠ [] := List.cons_ne_nil _ _

theorem sort_c21_last : sort_c21.getLast sort_c21_ne = 5789 := rfl

theorem sort_c21_hd : sort_c21.head sort_c21_ne = 5477 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.Block0LowsC3


