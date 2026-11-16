-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0LowsC1
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0LowsC1
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T16:33:19.052279+00:00
-- url     : https://prove2.me/theorems/68755289-87e8-4884-9d21-7320bfceb9f4
-- title:
--   Block-0 lows index certificates, chunks 18–19
-- statement:
--   # Block-0 lows certificates, chunks 18–19
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

namespace IntMul.Kappa.R8.Bit.Oppbank.Block0LowsC1

theorem sort_c18_eq : sort_c18 = jx_c18.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c18_sorted : isStrictSorted sort_c18 = true := rfl

theorem jx_c18_all : jx_c18.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c18_ne : sort_c18 ≠ [] := List.cons_ne_nil _ _

theorem sort_c18_last : sort_c18.getLast sort_c18_ne = 4923 := rfl

theorem sort_c18_hd : sort_c18.head sort_c18_ne = 4601 := rfl

theorem sort_c19_eq : sort_c19 = jx_c19.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c19_sorted : isStrictSorted sort_c19 = true := rfl

theorem jx_c19_all : jx_c19.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c19_ne : sort_c19 ≠ [] := List.cons_ne_nil _ _

theorem sort_c19_last : sort_c19.getLast sort_c19_ne = 5171 := rfl

theorem sort_c19_hd : sort_c19.head sort_c19_ne = 4924 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.Block0LowsC1


