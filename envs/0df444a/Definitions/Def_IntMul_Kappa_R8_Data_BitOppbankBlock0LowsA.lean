-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0LowsA
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0LowsA
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T16:14:57.817843+00:00
-- url     : https://prove2.me/theorems/a7e73f46-5abb-494e-b51d-9ebdc6c65379
-- title:
--   Block-0 lows index certificates, chunks 0–8
-- statement:
--   # Block-0 lows certificates, chunks 0–8
--
--   Index-certificate `rfl` equalities, per-chunk strict-sortedness, and head/last numeral identities for the first nine 100-row chunks of the 2602 block-0 gate lows. Depends on the published `Block0LowsData` pack. Prefix / block-0 helper only; not a full-word W1F certificate.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: block-0 lows chunk certificates. Prefix / block-0 pack only; not a full-word W1F certificate.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0LowsData

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option autoImplicit false
set_option linter.unusedSimpArgs false

open IntMul.Kappa.R8.Bit.Oppbank.Block0LowsData

namespace IntMul.Kappa.R8.Bit.Oppbank.Block0LowsA

theorem sort_c00_eq : sort_c00 = jx_c00.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c00_sorted : isStrictSorted sort_c00 = true := rfl

theorem jx_c00_all : jx_c00.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c00_ne : sort_c00 ≠ [] := List.cons_ne_nil _ _

theorem sort_c00_last : sort_c00.getLast sort_c00_ne = 217 := rfl

theorem sort_c01_eq : sort_c01 = jx_c01.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c01_sorted : isStrictSorted sort_c01 = true := rfl

theorem jx_c01_all : jx_c01.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c01_ne : sort_c01 ≠ [] := List.cons_ne_nil _ _

theorem sort_c01_last : sort_c01.getLast sort_c01_ne = 414 := rfl

theorem sort_c01_hd : sort_c01.head sort_c01_ne = 219 := rfl

theorem sort_c02_eq : sort_c02 = jx_c02.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c02_sorted : isStrictSorted sort_c02 = true := rfl

theorem jx_c02_all : jx_c02.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c02_ne : sort_c02 ≠ [] := List.cons_ne_nil _ _

theorem sort_c02_last : sort_c02.getLast sort_c02_ne = 615 := rfl

theorem sort_c02_hd : sort_c02.head sort_c02_ne = 417 := rfl

theorem sort_c03_eq : sort_c03 = jx_c03.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c03_sorted : isStrictSorted sort_c03 = true := rfl

theorem jx_c03_all : jx_c03.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c03_ne : sort_c03 ≠ [] := List.cons_ne_nil _ _

theorem sort_c03_last : sort_c03.getLast sort_c03_ne = 881 := rfl

theorem sort_c03_hd : sort_c03.head sort_c03_ne = 618 := rfl

theorem sort_c04_eq : sort_c04 = jx_c04.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c04_sorted : isStrictSorted sort_c04 = true := rfl

theorem jx_c04_all : jx_c04.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c04_ne : sort_c04 ≠ [] := List.cons_ne_nil _ _

theorem sort_c04_last : sort_c04.getLast sort_c04_ne = 1193 := rfl

theorem sort_c04_hd : sort_c04.head sort_c04_ne = 886 := rfl

theorem sort_c05_eq : sort_c05 = jx_c05.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c05_sorted : isStrictSorted sort_c05 = true := rfl

theorem jx_c05_all : jx_c05.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c05_ne : sort_c05 ≠ [] := List.cons_ne_nil _ _

theorem sort_c05_last : sort_c05.getLast sort_c05_ne = 1491 := rfl

theorem sort_c05_hd : sort_c05.head sort_c05_ne = 1198 := rfl

theorem sort_c06_eq : sort_c06 = jx_c06.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c06_sorted : isStrictSorted sort_c06 = true := rfl

theorem jx_c06_all : jx_c06.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c06_ne : sort_c06 ≠ [] := List.cons_ne_nil _ _

theorem sort_c06_last : sort_c06.getLast sort_c06_ne = 1689 := rfl

theorem sort_c06_hd : sort_c06.head sort_c06_ne = 1494 := rfl

theorem sort_c07_eq : sort_c07 = jx_c07.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c07_sorted : isStrictSorted sort_c07 = true := rfl

theorem jx_c07_all : jx_c07.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c07_ne : sort_c07 ≠ [] := List.cons_ne_nil _ _

theorem sort_c07_last : sort_c07.getLast sort_c07_ne = 1886 := rfl

theorem sort_c07_hd : sort_c07.head sort_c07_ne = 1690 := rfl

theorem sort_c08_eq : sort_c08 = jx_c08.map (fun i => lowsFlat[i]!) := rfl

theorem sort_c08_sorted : isStrictSorted sort_c08 = true := rfl

theorem jx_c08_all : jx_c08.all (fun i => decide (i < 2602)) = true := rfl

theorem sort_c08_ne : sort_c08 ≠ [] := List.cons_ne_nil _ _

theorem sort_c08_last : sort_c08.getLast sort_c08_ne = 2146 := rfl

theorem sort_c08_hd : sort_c08.head sort_c08_ne = 1889 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.Block0LowsA


