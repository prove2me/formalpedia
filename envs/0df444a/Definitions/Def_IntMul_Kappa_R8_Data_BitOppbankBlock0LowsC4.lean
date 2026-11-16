-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0LowsC4
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0LowsC4
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T16:33:53.475539+00:00
-- url     : https://prove2.me/theorems/1035dd6b-4039-457f-90a1-922dba7b969c
-- title:
--   Block-0 lows index certificates, chunks 24–26
-- statement:
--   # Block-0 lows certificates, chunks 24–26
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

namespace IntMul.Kappa.R8.Bit.Oppbank.Block0LowsC4

theorem sort_c24_eq : sort_c24 = jx_c24.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c24_sorted : isStrictSorted sort_c24 = true := rfl

theorem jx_c24_all : jx_c24.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c24_ne : sort_c24 ≠ [] := List.cons_ne_nil _ _

theorem sort_c24_last : sort_c24.getLast sort_c24_ne = 6693 := rfl

theorem sort_c24_hd : sort_c24.head sort_c24_ne = 6378 := rfl

theorem sort_c25_eq : sort_c25 = jx_c25.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c25_sorted : isStrictSorted sort_c25 = true := rfl

theorem jx_c25_all : jx_c25.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c25_ne : sort_c25 ≠ [] := List.cons_ne_nil _ _

theorem sort_c25_last : sort_c25.getLast sort_c25_ne = 7363 := rfl

theorem sort_c25_hd : sort_c25.head sort_c25_ne = 6698 := rfl

theorem sort_c26_eq : sort_c26 = jx_c26.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c26_sorted : isStrictSorted sort_c26 = true := rfl

theorem jx_c26_all : jx_c26.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c26_ne : sort_c26 ≠ [] := List.cons_ne_nil _ _

theorem sort_c26_hd : sort_c26.head sort_c26_ne = 7369 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.Block0LowsC4


