-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0LowsB1
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0LowsB1
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T16:28:27.433469+00:00
-- url     : https://prove2.me/theorems/92b05b37-f551-4ae9-a912-fbd9d397f9b1
-- title:
--   Block-0 lows index certificates, chunks 9–12
-- statement:
--   # Block-0 lows certificates, chunks 9–12
--
--   Index-certificate `rfl` equalities and head/last identities for chunks 9–12. Depends on published `Block0LowsData`. Prefix / block-0 helper only; not a full-word W1F certificate.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: block-0 chunk certificates. Prefix / block-0 pack only; not a full-word W1F certificate.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0LowsData

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option autoImplicit false
set_option linter.unusedSimpArgs false

open IntMul.Kappa.R8.Bit.Oppbank.Block0LowsData

namespace IntMul.Kappa.R8.Bit.Oppbank.Block0LowsB1

theorem sort_c09_eq : sort_c09 = jx_c09.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c09_sorted : isStrictSorted sort_c09 = true := rfl

theorem jx_c09_all : jx_c09.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c09_ne : sort_c09 ≠ [] := List.cons_ne_nil _ _

theorem sort_c09_last : sort_c09.getLast sort_c09_ne = 2459 := rfl

theorem sort_c09_hd : sort_c09.head sort_c09_ne = 2151 := rfl

theorem sort_c10_eq : sort_c10 = jx_c10.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c10_sorted : isStrictSorted sort_c10 = true := rfl

theorem jx_c10_all : jx_c10.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c10_ne : sort_c10 ≠ [] := List.cons_ne_nil _ _

theorem sort_c10_last : sort_c10.getLast sort_c10_ne = 2767 := rfl

theorem sort_c10_hd : sort_c10.head sort_c10_ne = 2464 := rfl

theorem sort_c11_eq : sort_c11 = jx_c11.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c11_sorted : isStrictSorted sort_c11 = true := rfl

theorem jx_c11_all : jx_c11.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c11_ne : sort_c11 ≠ [] := List.cons_ne_nil _ _

theorem sort_c11_last : sort_c11.getLast sort_c11_ne = 2987 := rfl

theorem sort_c11_hd : sort_c11.head sort_c11_ne = 2771 := rfl

theorem sort_c12_eq : sort_c12 = jx_c12.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c12_sorted : isStrictSorted sort_c12 = true := rfl

theorem jx_c12_all : jx_c12.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c12_ne : sort_c12 ≠ [] := List.cons_ne_nil _ _

theorem sort_c12_last : sort_c12.getLast sort_c12_ne = 3199 := rfl

theorem sort_c12_hd : sort_c12.head sort_c12_ne = 2989 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.Block0LowsB1


