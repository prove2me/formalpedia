-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound5
-- name    : IntMul_Kappa_R8_Data_BitOppbankDimBound5
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:02:49.983541+00:00
-- url     : https://prove2.me/theorems/6c3700d9-6ad6-4c6c-8632-2d7d9e86cdaf
-- title:
--   Densified dimF $\le 22$ pack 5 ($[25000,30000)$)
-- statement:
--   Pack 5 of the densified dimension-field bound.
--
--   For every densified node index $n$ with $25000\le n<30000$, the 5-bit field $\mathrm{dimF}(n)$ extracted from $\mathrm{DIMT}$ satisfies
--   $$1\le \mathrm{dimF}(n)\le 22.$$
--   Proved by `decide` on successive `Fin 50` windows (no `native_decide`).
-- source:
--   R8 BitNB densified DIMT field bound; Fin-window decide packs

-- DimBound pack 5: dimF bounds on n ∈ [25000, 30000)

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.ChkBitArg
open IntMul.Kappa.R8.Bit.Oppbank.SupG

namespace IntMul.Kappa.R8.Bit.Oppbank.DimBound5

private theorem le_w500 : ∀ n : Fin 50, dimF (n.val + 25000) ≤ 22 := by decide
private theorem pos_w500 : ∀ n : Fin 50, 0 < dimF (n.val + 25000) := by decide
private theorem le_w501 : ∀ n : Fin 50, dimF (n.val + 25050) ≤ 22 := by decide
private theorem pos_w501 : ∀ n : Fin 50, 0 < dimF (n.val + 25050) := by decide
private theorem le_w502 : ∀ n : Fin 50, dimF (n.val + 25100) ≤ 22 := by decide
private theorem pos_w502 : ∀ n : Fin 50, 0 < dimF (n.val + 25100) := by decide
private theorem le_w503 : ∀ n : Fin 50, dimF (n.val + 25150) ≤ 22 := by decide
private theorem pos_w503 : ∀ n : Fin 50, 0 < dimF (n.val + 25150) := by decide
private theorem le_w504 : ∀ n : Fin 50, dimF (n.val + 25200) ≤ 22 := by decide
private theorem pos_w504 : ∀ n : Fin 50, 0 < dimF (n.val + 25200) := by decide
private theorem le_w505 : ∀ n : Fin 50, dimF (n.val + 25250) ≤ 22 := by decide
private theorem pos_w505 : ∀ n : Fin 50, 0 < dimF (n.val + 25250) := by decide
private theorem le_w506 : ∀ n : Fin 50, dimF (n.val + 25300) ≤ 22 := by decide
private theorem pos_w506 : ∀ n : Fin 50, 0 < dimF (n.val + 25300) := by decide
private theorem le_w507 : ∀ n : Fin 50, dimF (n.val + 25350) ≤ 22 := by decide
private theorem pos_w507 : ∀ n : Fin 50, 0 < dimF (n.val + 25350) := by decide
private theorem le_w508 : ∀ n : Fin 50, dimF (n.val + 25400) ≤ 22 := by decide
private theorem pos_w508 : ∀ n : Fin 50, 0 < dimF (n.val + 25400) := by decide
private theorem le_w509 : ∀ n : Fin 50, dimF (n.val + 25450) ≤ 22 := by decide
private theorem pos_w509 : ∀ n : Fin 50, 0 < dimF (n.val + 25450) := by decide
private theorem le_w510 : ∀ n : Fin 50, dimF (n.val + 25500) ≤ 22 := by decide
private theorem pos_w510 : ∀ n : Fin 50, 0 < dimF (n.val + 25500) := by decide
private theorem le_w511 : ∀ n : Fin 50, dimF (n.val + 25550) ≤ 22 := by decide
private theorem pos_w511 : ∀ n : Fin 50, 0 < dimF (n.val + 25550) := by decide
private theorem le_w512 : ∀ n : Fin 50, dimF (n.val + 25600) ≤ 22 := by decide
private theorem pos_w512 : ∀ n : Fin 50, 0 < dimF (n.val + 25600) := by decide
private theorem le_w513 : ∀ n : Fin 50, dimF (n.val + 25650) ≤ 22 := by decide
private theorem pos_w513 : ∀ n : Fin 50, 0 < dimF (n.val + 25650) := by decide
private theorem le_w514 : ∀ n : Fin 50, dimF (n.val + 25700) ≤ 22 := by decide
private theorem pos_w514 : ∀ n : Fin 50, 0 < dimF (n.val + 25700) := by decide
private theorem le_w515 : ∀ n : Fin 50, dimF (n.val + 25750) ≤ 22 := by decide
private theorem pos_w515 : ∀ n : Fin 50, 0 < dimF (n.val + 25750) := by decide
private theorem le_w516 : ∀ n : Fin 50, dimF (n.val + 25800) ≤ 22 := by decide
private theorem pos_w516 : ∀ n : Fin 50, 0 < dimF (n.val + 25800) := by decide
private theorem le_w517 : ∀ n : Fin 50, dimF (n.val + 25850) ≤ 22 := by decide
private theorem pos_w517 : ∀ n : Fin 50, 0 < dimF (n.val + 25850) := by decide
private theorem le_w518 : ∀ n : Fin 50, dimF (n.val + 25900) ≤ 22 := by decide
private theorem pos_w518 : ∀ n : Fin 50, 0 < dimF (n.val + 25900) := by decide
private theorem le_w519 : ∀ n : Fin 50, dimF (n.val + 25950) ≤ 22 := by decide
private theorem pos_w519 : ∀ n : Fin 50, 0 < dimF (n.val + 25950) := by decide
private theorem le_w520 : ∀ n : Fin 50, dimF (n.val + 26000) ≤ 22 := by decide
private theorem pos_w520 : ∀ n : Fin 50, 0 < dimF (n.val + 26000) := by decide
private theorem le_w521 : ∀ n : Fin 50, dimF (n.val + 26050) ≤ 22 := by decide
private theorem pos_w521 : ∀ n : Fin 50, 0 < dimF (n.val + 26050) := by decide
private theorem le_w522 : ∀ n : Fin 50, dimF (n.val + 26100) ≤ 22 := by decide
private theorem pos_w522 : ∀ n : Fin 50, 0 < dimF (n.val + 26100) := by decide
private theorem le_w523 : ∀ n : Fin 50, dimF (n.val + 26150) ≤ 22 := by decide
private theorem pos_w523 : ∀ n : Fin 50, 0 < dimF (n.val + 26150) := by decide
private theorem le_w524 : ∀ n : Fin 50, dimF (n.val + 26200) ≤ 22 := by decide
private theorem pos_w524 : ∀ n : Fin 50, 0 < dimF (n.val + 26200) := by decide
private theorem le_w525 : ∀ n : Fin 50, dimF (n.val + 26250) ≤ 22 := by decide
private theorem pos_w525 : ∀ n : Fin 50, 0 < dimF (n.val + 26250) := by decide
private theorem le_w526 : ∀ n : Fin 50, dimF (n.val + 26300) ≤ 22 := by decide
private theorem pos_w526 : ∀ n : Fin 50, 0 < dimF (n.val + 26300) := by decide
private theorem le_w527 : ∀ n : Fin 50, dimF (n.val + 26350) ≤ 22 := by decide
private theorem pos_w527 : ∀ n : Fin 50, 0 < dimF (n.val + 26350) := by decide
private theorem le_w528 : ∀ n : Fin 50, dimF (n.val + 26400) ≤ 22 := by decide
private theorem pos_w528 : ∀ n : Fin 50, 0 < dimF (n.val + 26400) := by decide
private theorem le_w529 : ∀ n : Fin 50, dimF (n.val + 26450) ≤ 22 := by decide
private theorem pos_w529 : ∀ n : Fin 50, 0 < dimF (n.val + 26450) := by decide
private theorem le_w530 : ∀ n : Fin 50, dimF (n.val + 26500) ≤ 22 := by decide
private theorem pos_w530 : ∀ n : Fin 50, 0 < dimF (n.val + 26500) := by decide
private theorem le_w531 : ∀ n : Fin 50, dimF (n.val + 26550) ≤ 22 := by decide
private theorem pos_w531 : ∀ n : Fin 50, 0 < dimF (n.val + 26550) := by decide
private theorem le_w532 : ∀ n : Fin 50, dimF (n.val + 26600) ≤ 22 := by decide
private theorem pos_w532 : ∀ n : Fin 50, 0 < dimF (n.val + 26600) := by decide
private theorem le_w533 : ∀ n : Fin 50, dimF (n.val + 26650) ≤ 22 := by decide
private theorem pos_w533 : ∀ n : Fin 50, 0 < dimF (n.val + 26650) := by decide
private theorem le_w534 : ∀ n : Fin 50, dimF (n.val + 26700) ≤ 22 := by decide
private theorem pos_w534 : ∀ n : Fin 50, 0 < dimF (n.val + 26700) := by decide
private theorem le_w535 : ∀ n : Fin 50, dimF (n.val + 26750) ≤ 22 := by decide
private theorem pos_w535 : ∀ n : Fin 50, 0 < dimF (n.val + 26750) := by decide
private theorem le_w536 : ∀ n : Fin 50, dimF (n.val + 26800) ≤ 22 := by decide
private theorem pos_w536 : ∀ n : Fin 50, 0 < dimF (n.val + 26800) := by decide
private theorem le_w537 : ∀ n : Fin 50, dimF (n.val + 26850) ≤ 22 := by decide
private theorem pos_w537 : ∀ n : Fin 50, 0 < dimF (n.val + 26850) := by decide
private theorem le_w538 : ∀ n : Fin 50, dimF (n.val + 26900) ≤ 22 := by decide
private theorem pos_w538 : ∀ n : Fin 50, 0 < dimF (n.val + 26900) := by decide
private theorem le_w539 : ∀ n : Fin 50, dimF (n.val + 26950) ≤ 22 := by decide
private theorem pos_w539 : ∀ n : Fin 50, 0 < dimF (n.val + 26950) := by decide
private theorem le_w540 : ∀ n : Fin 50, dimF (n.val + 27000) ≤ 22 := by decide
private theorem pos_w540 : ∀ n : Fin 50, 0 < dimF (n.val + 27000) := by decide
private theorem le_w541 : ∀ n : Fin 50, dimF (n.val + 27050) ≤ 22 := by decide
private theorem pos_w541 : ∀ n : Fin 50, 0 < dimF (n.val + 27050) := by decide
private theorem le_w542 : ∀ n : Fin 50, dimF (n.val + 27100) ≤ 22 := by decide
private theorem pos_w542 : ∀ n : Fin 50, 0 < dimF (n.val + 27100) := by decide
private theorem le_w543 : ∀ n : Fin 50, dimF (n.val + 27150) ≤ 22 := by decide
private theorem pos_w543 : ∀ n : Fin 50, 0 < dimF (n.val + 27150) := by decide
private theorem le_w544 : ∀ n : Fin 50, dimF (n.val + 27200) ≤ 22 := by decide
private theorem pos_w544 : ∀ n : Fin 50, 0 < dimF (n.val + 27200) := by decide
private theorem le_w545 : ∀ n : Fin 50, dimF (n.val + 27250) ≤ 22 := by decide
private theorem pos_w545 : ∀ n : Fin 50, 0 < dimF (n.val + 27250) := by decide
private theorem le_w546 : ∀ n : Fin 50, dimF (n.val + 27300) ≤ 22 := by decide
private theorem pos_w546 : ∀ n : Fin 50, 0 < dimF (n.val + 27300) := by decide
private theorem le_w547 : ∀ n : Fin 50, dimF (n.val + 27350) ≤ 22 := by decide
private theorem pos_w547 : ∀ n : Fin 50, 0 < dimF (n.val + 27350) := by decide
private theorem le_w548 : ∀ n : Fin 50, dimF (n.val + 27400) ≤ 22 := by decide
private theorem pos_w548 : ∀ n : Fin 50, 0 < dimF (n.val + 27400) := by decide
private theorem le_w549 : ∀ n : Fin 50, dimF (n.val + 27450) ≤ 22 := by decide
private theorem pos_w549 : ∀ n : Fin 50, 0 < dimF (n.val + 27450) := by decide
private theorem le_w550 : ∀ n : Fin 50, dimF (n.val + 27500) ≤ 22 := by decide
private theorem pos_w550 : ∀ n : Fin 50, 0 < dimF (n.val + 27500) := by decide
private theorem le_w551 : ∀ n : Fin 50, dimF (n.val + 27550) ≤ 22 := by decide
private theorem pos_w551 : ∀ n : Fin 50, 0 < dimF (n.val + 27550) := by decide
private theorem le_w552 : ∀ n : Fin 50, dimF (n.val + 27600) ≤ 22 := by decide
private theorem pos_w552 : ∀ n : Fin 50, 0 < dimF (n.val + 27600) := by decide
private theorem le_w553 : ∀ n : Fin 50, dimF (n.val + 27650) ≤ 22 := by decide
private theorem pos_w553 : ∀ n : Fin 50, 0 < dimF (n.val + 27650) := by decide
private theorem le_w554 : ∀ n : Fin 50, dimF (n.val + 27700) ≤ 22 := by decide
private theorem pos_w554 : ∀ n : Fin 50, 0 < dimF (n.val + 27700) := by decide
private theorem le_w555 : ∀ n : Fin 50, dimF (n.val + 27750) ≤ 22 := by decide
private theorem pos_w555 : ∀ n : Fin 50, 0 < dimF (n.val + 27750) := by decide
private theorem le_w556 : ∀ n : Fin 50, dimF (n.val + 27800) ≤ 22 := by decide
private theorem pos_w556 : ∀ n : Fin 50, 0 < dimF (n.val + 27800) := by decide
private theorem le_w557 : ∀ n : Fin 50, dimF (n.val + 27850) ≤ 22 := by decide
private theorem pos_w557 : ∀ n : Fin 50, 0 < dimF (n.val + 27850) := by decide
private theorem le_w558 : ∀ n : Fin 50, dimF (n.val + 27900) ≤ 22 := by decide
private theorem pos_w558 : ∀ n : Fin 50, 0 < dimF (n.val + 27900) := by decide
private theorem le_w559 : ∀ n : Fin 50, dimF (n.val + 27950) ≤ 22 := by decide
private theorem pos_w559 : ∀ n : Fin 50, 0 < dimF (n.val + 27950) := by decide
private theorem le_w560 : ∀ n : Fin 50, dimF (n.val + 28000) ≤ 22 := by decide
private theorem pos_w560 : ∀ n : Fin 50, 0 < dimF (n.val + 28000) := by decide
private theorem le_w561 : ∀ n : Fin 50, dimF (n.val + 28050) ≤ 22 := by decide
private theorem pos_w561 : ∀ n : Fin 50, 0 < dimF (n.val + 28050) := by decide
private theorem le_w562 : ∀ n : Fin 50, dimF (n.val + 28100) ≤ 22 := by decide
private theorem pos_w562 : ∀ n : Fin 50, 0 < dimF (n.val + 28100) := by decide
private theorem le_w563 : ∀ n : Fin 50, dimF (n.val + 28150) ≤ 22 := by decide
private theorem pos_w563 : ∀ n : Fin 50, 0 < dimF (n.val + 28150) := by decide
private theorem le_w564 : ∀ n : Fin 50, dimF (n.val + 28200) ≤ 22 := by decide
private theorem pos_w564 : ∀ n : Fin 50, 0 < dimF (n.val + 28200) := by decide
private theorem le_w565 : ∀ n : Fin 50, dimF (n.val + 28250) ≤ 22 := by decide
private theorem pos_w565 : ∀ n : Fin 50, 0 < dimF (n.val + 28250) := by decide
private theorem le_w566 : ∀ n : Fin 50, dimF (n.val + 28300) ≤ 22 := by decide
private theorem pos_w566 : ∀ n : Fin 50, 0 < dimF (n.val + 28300) := by decide
private theorem le_w567 : ∀ n : Fin 50, dimF (n.val + 28350) ≤ 22 := by decide
private theorem pos_w567 : ∀ n : Fin 50, 0 < dimF (n.val + 28350) := by decide
private theorem le_w568 : ∀ n : Fin 50, dimF (n.val + 28400) ≤ 22 := by decide
private theorem pos_w568 : ∀ n : Fin 50, 0 < dimF (n.val + 28400) := by decide
private theorem le_w569 : ∀ n : Fin 50, dimF (n.val + 28450) ≤ 22 := by decide
private theorem pos_w569 : ∀ n : Fin 50, 0 < dimF (n.val + 28450) := by decide
private theorem le_w570 : ∀ n : Fin 50, dimF (n.val + 28500) ≤ 22 := by decide
private theorem pos_w570 : ∀ n : Fin 50, 0 < dimF (n.val + 28500) := by decide
private theorem le_w571 : ∀ n : Fin 50, dimF (n.val + 28550) ≤ 22 := by decide
private theorem pos_w571 : ∀ n : Fin 50, 0 < dimF (n.val + 28550) := by decide
private theorem le_w572 : ∀ n : Fin 50, dimF (n.val + 28600) ≤ 22 := by decide
private theorem pos_w572 : ∀ n : Fin 50, 0 < dimF (n.val + 28600) := by decide
private theorem le_w573 : ∀ n : Fin 50, dimF (n.val + 28650) ≤ 22 := by decide
private theorem pos_w573 : ∀ n : Fin 50, 0 < dimF (n.val + 28650) := by decide
private theorem le_w574 : ∀ n : Fin 50, dimF (n.val + 28700) ≤ 22 := by decide
private theorem pos_w574 : ∀ n : Fin 50, 0 < dimF (n.val + 28700) := by decide
private theorem le_w575 : ∀ n : Fin 50, dimF (n.val + 28750) ≤ 22 := by decide
private theorem pos_w575 : ∀ n : Fin 50, 0 < dimF (n.val + 28750) := by decide
private theorem le_w576 : ∀ n : Fin 50, dimF (n.val + 28800) ≤ 22 := by decide
private theorem pos_w576 : ∀ n : Fin 50, 0 < dimF (n.val + 28800) := by decide
private theorem le_w577 : ∀ n : Fin 50, dimF (n.val + 28850) ≤ 22 := by decide
private theorem pos_w577 : ∀ n : Fin 50, 0 < dimF (n.val + 28850) := by decide
private theorem le_w578 : ∀ n : Fin 50, dimF (n.val + 28900) ≤ 22 := by decide
private theorem pos_w578 : ∀ n : Fin 50, 0 < dimF (n.val + 28900) := by decide
private theorem le_w579 : ∀ n : Fin 50, dimF (n.val + 28950) ≤ 22 := by decide
private theorem pos_w579 : ∀ n : Fin 50, 0 < dimF (n.val + 28950) := by decide
private theorem le_w580 : ∀ n : Fin 50, dimF (n.val + 29000) ≤ 22 := by decide
private theorem pos_w580 : ∀ n : Fin 50, 0 < dimF (n.val + 29000) := by decide
private theorem le_w581 : ∀ n : Fin 50, dimF (n.val + 29050) ≤ 22 := by decide
private theorem pos_w581 : ∀ n : Fin 50, 0 < dimF (n.val + 29050) := by decide
private theorem le_w582 : ∀ n : Fin 50, dimF (n.val + 29100) ≤ 22 := by decide
private theorem pos_w582 : ∀ n : Fin 50, 0 < dimF (n.val + 29100) := by decide
private theorem le_w583 : ∀ n : Fin 50, dimF (n.val + 29150) ≤ 22 := by decide
private theorem pos_w583 : ∀ n : Fin 50, 0 < dimF (n.val + 29150) := by decide
private theorem le_w584 : ∀ n : Fin 50, dimF (n.val + 29200) ≤ 22 := by decide
private theorem pos_w584 : ∀ n : Fin 50, 0 < dimF (n.val + 29200) := by decide
private theorem le_w585 : ∀ n : Fin 50, dimF (n.val + 29250) ≤ 22 := by decide
private theorem pos_w585 : ∀ n : Fin 50, 0 < dimF (n.val + 29250) := by decide
private theorem le_w586 : ∀ n : Fin 50, dimF (n.val + 29300) ≤ 22 := by decide
private theorem pos_w586 : ∀ n : Fin 50, 0 < dimF (n.val + 29300) := by decide
private theorem le_w587 : ∀ n : Fin 50, dimF (n.val + 29350) ≤ 22 := by decide
private theorem pos_w587 : ∀ n : Fin 50, 0 < dimF (n.val + 29350) := by decide
private theorem le_w588 : ∀ n : Fin 50, dimF (n.val + 29400) ≤ 22 := by decide
private theorem pos_w588 : ∀ n : Fin 50, 0 < dimF (n.val + 29400) := by decide
private theorem le_w589 : ∀ n : Fin 50, dimF (n.val + 29450) ≤ 22 := by decide
private theorem pos_w589 : ∀ n : Fin 50, 0 < dimF (n.val + 29450) := by decide
private theorem le_w590 : ∀ n : Fin 50, dimF (n.val + 29500) ≤ 22 := by decide
private theorem pos_w590 : ∀ n : Fin 50, 0 < dimF (n.val + 29500) := by decide
private theorem le_w591 : ∀ n : Fin 50, dimF (n.val + 29550) ≤ 22 := by decide
private theorem pos_w591 : ∀ n : Fin 50, 0 < dimF (n.val + 29550) := by decide
private theorem le_w592 : ∀ n : Fin 50, dimF (n.val + 29600) ≤ 22 := by decide
private theorem pos_w592 : ∀ n : Fin 50, 0 < dimF (n.val + 29600) := by decide
private theorem le_w593 : ∀ n : Fin 50, dimF (n.val + 29650) ≤ 22 := by decide
private theorem pos_w593 : ∀ n : Fin 50, 0 < dimF (n.val + 29650) := by decide
private theorem le_w594 : ∀ n : Fin 50, dimF (n.val + 29700) ≤ 22 := by decide
private theorem pos_w594 : ∀ n : Fin 50, 0 < dimF (n.val + 29700) := by decide
private theorem le_w595 : ∀ n : Fin 50, dimF (n.val + 29750) ≤ 22 := by decide
private theorem pos_w595 : ∀ n : Fin 50, 0 < dimF (n.val + 29750) := by decide
private theorem le_w596 : ∀ n : Fin 50, dimF (n.val + 29800) ≤ 22 := by decide
private theorem pos_w596 : ∀ n : Fin 50, 0 < dimF (n.val + 29800) := by decide
private theorem le_w597 : ∀ n : Fin 50, dimF (n.val + 29850) ≤ 22 := by decide
private theorem pos_w597 : ∀ n : Fin 50, 0 < dimF (n.val + 29850) := by decide
private theorem le_w598 : ∀ n : Fin 50, dimF (n.val + 29900) ≤ 22 := by decide
private theorem pos_w598 : ∀ n : Fin 50, 0 < dimF (n.val + 29900) := by decide
private theorem le_w599 : ∀ n : Fin 50, dimF (n.val + 29950) ≤ 22 := by decide
private theorem pos_w599 : ∀ n : Fin 50, 0 < dimF (n.val + 29950) := by decide

theorem dimF_le_22_range : ∀ n, 25000 ≤ n → n < 30000 → dimF n ≤ 22 := by
  intro n hlo hhi
  by_cases h0 : n < 25050
  · have hr : n - 25000 < 50 := by omega
    have heq : n = (n - 25000) + 25000 := by omega
    rw [heq]
    exact le_w500 ⟨n - 25000, hr⟩
  · by_cases h1 : n < 25100
    · have hr : n - 25050 < 50 := by omega
      have heq : n = (n - 25050) + 25050 := by omega
      rw [heq]
      exact le_w501 ⟨n - 25050, hr⟩
    · by_cases h2 : n < 25150
      · have hr : n - 25100 < 50 := by omega
        have heq : n = (n - 25100) + 25100 := by omega
        rw [heq]
        exact le_w502 ⟨n - 25100, hr⟩
      · by_cases h3 : n < 25200
        · have hr : n - 25150 < 50 := by omega
          have heq : n = (n - 25150) + 25150 := by omega
          rw [heq]
          exact le_w503 ⟨n - 25150, hr⟩
        · by_cases h4 : n < 25250
          · have hr : n - 25200 < 50 := by omega
            have heq : n = (n - 25200) + 25200 := by omega
            rw [heq]
            exact le_w504 ⟨n - 25200, hr⟩
          · by_cases h5 : n < 25300
            · have hr : n - 25250 < 50 := by omega
              have heq : n = (n - 25250) + 25250 := by omega
              rw [heq]
              exact le_w505 ⟨n - 25250, hr⟩
            · by_cases h6 : n < 25350
              · have hr : n - 25300 < 50 := by omega
                have heq : n = (n - 25300) + 25300 := by omega
                rw [heq]
                exact le_w506 ⟨n - 25300, hr⟩
              · by_cases h7 : n < 25400
                · have hr : n - 25350 < 50 := by omega
                  have heq : n = (n - 25350) + 25350 := by omega
                  rw [heq]
                  exact le_w507 ⟨n - 25350, hr⟩
                · by_cases h8 : n < 25450
                  · have hr : n - 25400 < 50 := by omega
                    have heq : n = (n - 25400) + 25400 := by omega
                    rw [heq]
                    exact le_w508 ⟨n - 25400, hr⟩
                  · by_cases h9 : n < 25500
                    · have hr : n - 25450 < 50 := by omega
                      have heq : n = (n - 25450) + 25450 := by omega
                      rw [heq]
                      exact le_w509 ⟨n - 25450, hr⟩
                    · by_cases h10 : n < 25550
                      · have hr : n - 25500 < 50 := by omega
                        have heq : n = (n - 25500) + 25500 := by omega
                        rw [heq]
                        exact le_w510 ⟨n - 25500, hr⟩
                      · by_cases h11 : n < 25600
                        · have hr : n - 25550 < 50 := by omega
                          have heq : n = (n - 25550) + 25550 := by omega
                          rw [heq]
                          exact le_w511 ⟨n - 25550, hr⟩
                        · by_cases h12 : n < 25650
                          · have hr : n - 25600 < 50 := by omega
                            have heq : n = (n - 25600) + 25600 := by omega
                            rw [heq]
                            exact le_w512 ⟨n - 25600, hr⟩
                          · by_cases h13 : n < 25700
                            · have hr : n - 25650 < 50 := by omega
                              have heq : n = (n - 25650) + 25650 := by omega
                              rw [heq]
                              exact le_w513 ⟨n - 25650, hr⟩
                            · by_cases h14 : n < 25750
                              · have hr : n - 25700 < 50 := by omega
                                have heq : n = (n - 25700) + 25700 := by omega
                                rw [heq]
                                exact le_w514 ⟨n - 25700, hr⟩
                              · by_cases h15 : n < 25800
                                · have hr : n - 25750 < 50 := by omega
                                  have heq : n = (n - 25750) + 25750 := by omega
                                  rw [heq]
                                  exact le_w515 ⟨n - 25750, hr⟩
                                · by_cases h16 : n < 25850
                                  · have hr : n - 25800 < 50 := by omega
                                    have heq : n = (n - 25800) + 25800 := by omega
                                    rw [heq]
                                    exact le_w516 ⟨n - 25800, hr⟩
                                  · by_cases h17 : n < 25900
                                    · have hr : n - 25850 < 50 := by omega
                                      have heq : n = (n - 25850) + 25850 := by omega
                                      rw [heq]
                                      exact le_w517 ⟨n - 25850, hr⟩
                                    · by_cases h18 : n < 25950
                                      · have hr : n - 25900 < 50 := by omega
                                        have heq : n = (n - 25900) + 25900 := by omega
                                        rw [heq]
                                        exact le_w518 ⟨n - 25900, hr⟩
                                      · by_cases h19 : n < 26000
                                        · have hr : n - 25950 < 50 := by omega
                                          have heq : n = (n - 25950) + 25950 := by omega
                                          rw [heq]
                                          exact le_w519 ⟨n - 25950, hr⟩
                                        · by_cases h20 : n < 26050
                                          · have hr : n - 26000 < 50 := by omega
                                            have heq : n = (n - 26000) + 26000 := by omega
                                            rw [heq]
                                            exact le_w520 ⟨n - 26000, hr⟩
                                          · by_cases h21 : n < 26100
                                            · have hr : n - 26050 < 50 := by omega
                                              have heq : n = (n - 26050) + 26050 := by omega
                                              rw [heq]
                                              exact le_w521 ⟨n - 26050, hr⟩
                                            · by_cases h22 : n < 26150
                                              · have hr : n - 26100 < 50 := by omega
                                                have heq : n = (n - 26100) + 26100 := by omega
                                                rw [heq]
                                                exact le_w522 ⟨n - 26100, hr⟩
                                              · by_cases h23 : n < 26200
                                                · have hr : n - 26150 < 50 := by omega
                                                  have heq : n = (n - 26150) + 26150 := by omega
                                                  rw [heq]
                                                  exact le_w523 ⟨n - 26150, hr⟩
                                                · by_cases h24 : n < 26250
                                                  · have hr : n - 26200 < 50 := by omega
                                                    have heq : n = (n - 26200) + 26200 := by omega
                                                    rw [heq]
                                                    exact le_w524 ⟨n - 26200, hr⟩
                                                  · by_cases h25 : n < 26300
                                                    · have hr : n - 26250 < 50 := by omega
                                                      have heq : n = (n - 26250) + 26250 := by omega
                                                      rw [heq]
                                                      exact le_w525 ⟨n - 26250, hr⟩
                                                    · by_cases h26 : n < 26350
                                                      · have hr : n - 26300 < 50 := by omega
                                                        have heq : n = (n - 26300) + 26300 := by omega
                                                        rw [heq]
                                                        exact le_w526 ⟨n - 26300, hr⟩
                                                      · by_cases h27 : n < 26400
                                                        · have hr : n - 26350 < 50 := by omega
                                                          have heq : n = (n - 26350) + 26350 := by omega
                                                          rw [heq]
                                                          exact le_w527 ⟨n - 26350, hr⟩
                                                        · by_cases h28 : n < 26450
                                                          · have hr : n - 26400 < 50 := by omega
                                                            have heq : n = (n - 26400) + 26400 := by omega
                                                            rw [heq]
                                                            exact le_w528 ⟨n - 26400, hr⟩
                                                          · by_cases h29 : n < 26500
                                                            · have hr : n - 26450 < 50 := by omega
                                                              have heq : n = (n - 26450) + 26450 := by omega
                                                              rw [heq]
                                                              exact le_w529 ⟨n - 26450, hr⟩
                                                            · by_cases h30 : n < 26550
                                                              · have hr : n - 26500 < 50 := by omega
                                                                have heq : n = (n - 26500) + 26500 := by omega
                                                                rw [heq]
                                                                exact le_w530 ⟨n - 26500, hr⟩
                                                              · by_cases h31 : n < 26600
                                                                · have hr : n - 26550 < 50 := by omega
                                                                  have heq : n = (n - 26550) + 26550 := by omega
                                                                  rw [heq]
                                                                  exact le_w531 ⟨n - 26550, hr⟩
                                                                · by_cases h32 : n < 26650
                                                                  · have hr : n - 26600 < 50 := by omega
                                                                    have heq : n = (n - 26600) + 26600 := by omega
                                                                    rw [heq]
                                                                    exact le_w532 ⟨n - 26600, hr⟩
                                                                  · by_cases h33 : n < 26700
                                                                    · have hr : n - 26650 < 50 := by omega
                                                                      have heq : n = (n - 26650) + 26650 := by omega
                                                                      rw [heq]
                                                                      exact le_w533 ⟨n - 26650, hr⟩
                                                                    · by_cases h34 : n < 26750
                                                                      · have hr : n - 26700 < 50 := by omega
                                                                        have heq : n = (n - 26700) + 26700 := by omega
                                                                        rw [heq]
                                                                        exact le_w534 ⟨n - 26700, hr⟩
                                                                      · by_cases h35 : n < 26800
                                                                        · have hr : n - 26750 < 50 := by omega
                                                                          have heq : n = (n - 26750) + 26750 := by omega
                                                                          rw [heq]
                                                                          exact le_w535 ⟨n - 26750, hr⟩
                                                                        · by_cases h36 : n < 26850
                                                                          · have hr : n - 26800 < 50 := by omega
                                                                            have heq : n = (n - 26800) + 26800 := by omega
                                                                            rw [heq]
                                                                            exact le_w536 ⟨n - 26800, hr⟩
                                                                          · by_cases h37 : n < 26900
                                                                            · have hr : n - 26850 < 50 := by omega
                                                                              have heq : n = (n - 26850) + 26850 := by omega
                                                                              rw [heq]
                                                                              exact le_w537 ⟨n - 26850, hr⟩
                                                                            · by_cases h38 : n < 26950
                                                                              · have hr : n - 26900 < 50 := by omega
                                                                                have heq : n = (n - 26900) + 26900 := by omega
                                                                                rw [heq]
                                                                                exact le_w538 ⟨n - 26900, hr⟩
                                                                              · by_cases h39 : n < 27000
                                                                                · have hr : n - 26950 < 50 := by omega
                                                                                  have heq : n = (n - 26950) + 26950 := by omega
                                                                                  rw [heq]
                                                                                  exact le_w539 ⟨n - 26950, hr⟩
                                                                                · by_cases h40 : n < 27050
                                                                                  · have hr : n - 27000 < 50 := by omega
                                                                                    have heq : n = (n - 27000) + 27000 := by omega
                                                                                    rw [heq]
                                                                                    exact le_w540 ⟨n - 27000, hr⟩
                                                                                  · by_cases h41 : n < 27100
                                                                                    · have hr : n - 27050 < 50 := by omega
                                                                                      have heq : n = (n - 27050) + 27050 := by omega
                                                                                      rw [heq]
                                                                                      exact le_w541 ⟨n - 27050, hr⟩
                                                                                    · by_cases h42 : n < 27150
                                                                                      · have hr : n - 27100 < 50 := by omega
                                                                                        have heq : n = (n - 27100) + 27100 := by omega
                                                                                        rw [heq]
                                                                                        exact le_w542 ⟨n - 27100, hr⟩
                                                                                      · by_cases h43 : n < 27200
                                                                                        · have hr : n - 27150 < 50 := by omega
                                                                                          have heq : n = (n - 27150) + 27150 := by omega
                                                                                          rw [heq]
                                                                                          exact le_w543 ⟨n - 27150, hr⟩
                                                                                        · by_cases h44 : n < 27250
                                                                                          · have hr : n - 27200 < 50 := by omega
                                                                                            have heq : n = (n - 27200) + 27200 := by omega
                                                                                            rw [heq]
                                                                                            exact le_w544 ⟨n - 27200, hr⟩
                                                                                          · by_cases h45 : n < 27300
                                                                                            · have hr : n - 27250 < 50 := by omega
                                                                                              have heq : n = (n - 27250) + 27250 := by omega
                                                                                              rw [heq]
                                                                                              exact le_w545 ⟨n - 27250, hr⟩
                                                                                            · by_cases h46 : n < 27350
                                                                                              · have hr : n - 27300 < 50 := by omega
                                                                                                have heq : n = (n - 27300) + 27300 := by omega
                                                                                                rw [heq]
                                                                                                exact le_w546 ⟨n - 27300, hr⟩
                                                                                              · by_cases h47 : n < 27400
                                                                                                · have hr : n - 27350 < 50 := by omega
                                                                                                  have heq : n = (n - 27350) + 27350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact le_w547 ⟨n - 27350, hr⟩
                                                                                                · by_cases h48 : n < 27450
                                                                                                  · have hr : n - 27400 < 50 := by omega
                                                                                                    have heq : n = (n - 27400) + 27400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact le_w548 ⟨n - 27400, hr⟩
                                                                                                  · by_cases h49 : n < 27500
                                                                                                    · have hr : n - 27450 < 50 := by omega
                                                                                                      have heq : n = (n - 27450) + 27450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact le_w549 ⟨n - 27450, hr⟩
                                                                                                    · by_cases h50 : n < 27550
                                                                                                      · have hr : n - 27500 < 50 := by omega
                                                                                                        have heq : n = (n - 27500) + 27500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact le_w550 ⟨n - 27500, hr⟩
                                                                                                      · by_cases h51 : n < 27600
                                                                                                        · have hr : n - 27550 < 50 := by omega
                                                                                                          have heq : n = (n - 27550) + 27550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact le_w551 ⟨n - 27550, hr⟩
                                                                                                        · by_cases h52 : n < 27650
                                                                                                          · have hr : n - 27600 < 50 := by omega
                                                                                                            have heq : n = (n - 27600) + 27600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact le_w552 ⟨n - 27600, hr⟩
                                                                                                          · by_cases h53 : n < 27700
                                                                                                            · have hr : n - 27650 < 50 := by omega
                                                                                                              have heq : n = (n - 27650) + 27650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact le_w553 ⟨n - 27650, hr⟩
                                                                                                            · by_cases h54 : n < 27750
                                                                                                              · have hr : n - 27700 < 50 := by omega
                                                                                                                have heq : n = (n - 27700) + 27700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact le_w554 ⟨n - 27700, hr⟩
                                                                                                              · by_cases h55 : n < 27800
                                                                                                                · have hr : n - 27750 < 50 := by omega
                                                                                                                  have heq : n = (n - 27750) + 27750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact le_w555 ⟨n - 27750, hr⟩
                                                                                                                · by_cases h56 : n < 27850
                                                                                                                  · have hr : n - 27800 < 50 := by omega
                                                                                                                    have heq : n = (n - 27800) + 27800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact le_w556 ⟨n - 27800, hr⟩
                                                                                                                  · by_cases h57 : n < 27900
                                                                                                                    · have hr : n - 27850 < 50 := by omega
                                                                                                                      have heq : n = (n - 27850) + 27850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact le_w557 ⟨n - 27850, hr⟩
                                                                                                                    · by_cases h58 : n < 27950
                                                                                                                      · have hr : n - 27900 < 50 := by omega
                                                                                                                        have heq : n = (n - 27900) + 27900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact le_w558 ⟨n - 27900, hr⟩
                                                                                                                      · by_cases h59 : n < 28000
                                                                                                                        · have hr : n - 27950 < 50 := by omega
                                                                                                                          have heq : n = (n - 27950) + 27950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact le_w559 ⟨n - 27950, hr⟩
                                                                                                                        · by_cases h60 : n < 28050
                                                                                                                          · have hr : n - 28000 < 50 := by omega
                                                                                                                            have heq : n = (n - 28000) + 28000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact le_w560 ⟨n - 28000, hr⟩
                                                                                                                          · by_cases h61 : n < 28100
                                                                                                                            · have hr : n - 28050 < 50 := by omega
                                                                                                                              have heq : n = (n - 28050) + 28050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact le_w561 ⟨n - 28050, hr⟩
                                                                                                                            · by_cases h62 : n < 28150
                                                                                                                              · have hr : n - 28100 < 50 := by omega
                                                                                                                                have heq : n = (n - 28100) + 28100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact le_w562 ⟨n - 28100, hr⟩
                                                                                                                              · by_cases h63 : n < 28200
                                                                                                                                · have hr : n - 28150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 28150) + 28150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact le_w563 ⟨n - 28150, hr⟩
                                                                                                                                · by_cases h64 : n < 28250
                                                                                                                                  · have hr : n - 28200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 28200) + 28200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact le_w564 ⟨n - 28200, hr⟩
                                                                                                                                  · by_cases h65 : n < 28300
                                                                                                                                    · have hr : n - 28250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 28250) + 28250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact le_w565 ⟨n - 28250, hr⟩
                                                                                                                                    · by_cases h66 : n < 28350
                                                                                                                                      · have hr : n - 28300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 28300) + 28300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact le_w566 ⟨n - 28300, hr⟩
                                                                                                                                      · by_cases h67 : n < 28400
                                                                                                                                        · have hr : n - 28350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 28350) + 28350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact le_w567 ⟨n - 28350, hr⟩
                                                                                                                                        · by_cases h68 : n < 28450
                                                                                                                                          · have hr : n - 28400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 28400) + 28400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact le_w568 ⟨n - 28400, hr⟩
                                                                                                                                          · by_cases h69 : n < 28500
                                                                                                                                            · have hr : n - 28450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 28450) + 28450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact le_w569 ⟨n - 28450, hr⟩
                                                                                                                                            · by_cases h70 : n < 28550
                                                                                                                                              · have hr : n - 28500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 28500) + 28500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact le_w570 ⟨n - 28500, hr⟩
                                                                                                                                              · by_cases h71 : n < 28600
                                                                                                                                                · have hr : n - 28550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 28550) + 28550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact le_w571 ⟨n - 28550, hr⟩
                                                                                                                                                · by_cases h72 : n < 28650
                                                                                                                                                  · have hr : n - 28600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 28600) + 28600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact le_w572 ⟨n - 28600, hr⟩
                                                                                                                                                  · by_cases h73 : n < 28700
                                                                                                                                                    · have hr : n - 28650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 28650) + 28650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact le_w573 ⟨n - 28650, hr⟩
                                                                                                                                                    · by_cases h74 : n < 28750
                                                                                                                                                      · have hr : n - 28700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 28700) + 28700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact le_w574 ⟨n - 28700, hr⟩
                                                                                                                                                      · by_cases h75 : n < 28800
                                                                                                                                                        · have hr : n - 28750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 28750) + 28750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact le_w575 ⟨n - 28750, hr⟩
                                                                                                                                                        · by_cases h76 : n < 28850
                                                                                                                                                          · have hr : n - 28800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 28800) + 28800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact le_w576 ⟨n - 28800, hr⟩
                                                                                                                                                          · by_cases h77 : n < 28900
                                                                                                                                                            · have hr : n - 28850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 28850) + 28850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact le_w577 ⟨n - 28850, hr⟩
                                                                                                                                                            · by_cases h78 : n < 28950
                                                                                                                                                              · have hr : n - 28900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 28900) + 28900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact le_w578 ⟨n - 28900, hr⟩
                                                                                                                                                              · by_cases h79 : n < 29000
                                                                                                                                                                · have hr : n - 28950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 28950) + 28950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact le_w579 ⟨n - 28950, hr⟩
                                                                                                                                                                · by_cases h80 : n < 29050
                                                                                                                                                                  · have hr : n - 29000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 29000) + 29000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact le_w580 ⟨n - 29000, hr⟩
                                                                                                                                                                  · by_cases h81 : n < 29100
                                                                                                                                                                    · have hr : n - 29050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 29050) + 29050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact le_w581 ⟨n - 29050, hr⟩
                                                                                                                                                                    · by_cases h82 : n < 29150
                                                                                                                                                                      · have hr : n - 29100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 29100) + 29100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact le_w582 ⟨n - 29100, hr⟩
                                                                                                                                                                      · by_cases h83 : n < 29200
                                                                                                                                                                        · have hr : n - 29150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 29150) + 29150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact le_w583 ⟨n - 29150, hr⟩
                                                                                                                                                                        · by_cases h84 : n < 29250
                                                                                                                                                                          · have hr : n - 29200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 29200) + 29200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact le_w584 ⟨n - 29200, hr⟩
                                                                                                                                                                          · by_cases h85 : n < 29300
                                                                                                                                                                            · have hr : n - 29250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 29250) + 29250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact le_w585 ⟨n - 29250, hr⟩
                                                                                                                                                                            · by_cases h86 : n < 29350
                                                                                                                                                                              · have hr : n - 29300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 29300) + 29300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact le_w586 ⟨n - 29300, hr⟩
                                                                                                                                                                              · by_cases h87 : n < 29400
                                                                                                                                                                                · have hr : n - 29350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 29350) + 29350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact le_w587 ⟨n - 29350, hr⟩
                                                                                                                                                                                · by_cases h88 : n < 29450
                                                                                                                                                                                  · have hr : n - 29400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 29400) + 29400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact le_w588 ⟨n - 29400, hr⟩
                                                                                                                                                                                  · by_cases h89 : n < 29500
                                                                                                                                                                                    · have hr : n - 29450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 29450) + 29450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact le_w589 ⟨n - 29450, hr⟩
                                                                                                                                                                                    · by_cases h90 : n < 29550
                                                                                                                                                                                      · have hr : n - 29500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 29500) + 29500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact le_w590 ⟨n - 29500, hr⟩
                                                                                                                                                                                      · by_cases h91 : n < 29600
                                                                                                                                                                                        · have hr : n - 29550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 29550) + 29550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact le_w591 ⟨n - 29550, hr⟩
                                                                                                                                                                                        · by_cases h92 : n < 29650
                                                                                                                                                                                          · have hr : n - 29600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 29600) + 29600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact le_w592 ⟨n - 29600, hr⟩
                                                                                                                                                                                          · by_cases h93 : n < 29700
                                                                                                                                                                                            · have hr : n - 29650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 29650) + 29650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact le_w593 ⟨n - 29650, hr⟩
                                                                                                                                                                                            · by_cases h94 : n < 29750
                                                                                                                                                                                              · have hr : n - 29700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 29700) + 29700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact le_w594 ⟨n - 29700, hr⟩
                                                                                                                                                                                              · by_cases h95 : n < 29800
                                                                                                                                                                                                · have hr : n - 29750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 29750) + 29750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact le_w595 ⟨n - 29750, hr⟩
                                                                                                                                                                                                · by_cases h96 : n < 29850
                                                                                                                                                                                                  · have hr : n - 29800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 29800) + 29800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact le_w596 ⟨n - 29800, hr⟩
                                                                                                                                                                                                  · by_cases h97 : n < 29900
                                                                                                                                                                                                    · have hr : n - 29850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 29850) + 29850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact le_w597 ⟨n - 29850, hr⟩
                                                                                                                                                                                                    · by_cases h98 : n < 29950
                                                                                                                                                                                                      · have hr : n - 29900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 29900) + 29900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact le_w598 ⟨n - 29900, hr⟩
                                                                                                                                                                                                      · by_cases h99 : n < 30000
                                                                                                                                                                                                        · have hr : n - 29950 < 50 := by omega
                                                                                                                                                                                                          have heq : n = (n - 29950) + 29950 := by omega
                                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                                          exact le_w599 ⟨n - 29950, hr⟩
                                                                                                                                                                                                        · omega

theorem dimF_pos_range : ∀ n, 25000 ≤ n → n < 30000 → 0 < dimF n := by
  intro n hlo hhi
  by_cases h0 : n < 25050
  · have hr : n - 25000 < 50 := by omega
    have heq : n = (n - 25000) + 25000 := by omega
    rw [heq]
    exact pos_w500 ⟨n - 25000, hr⟩
  · by_cases h1 : n < 25100
    · have hr : n - 25050 < 50 := by omega
      have heq : n = (n - 25050) + 25050 := by omega
      rw [heq]
      exact pos_w501 ⟨n - 25050, hr⟩
    · by_cases h2 : n < 25150
      · have hr : n - 25100 < 50 := by omega
        have heq : n = (n - 25100) + 25100 := by omega
        rw [heq]
        exact pos_w502 ⟨n - 25100, hr⟩
      · by_cases h3 : n < 25200
        · have hr : n - 25150 < 50 := by omega
          have heq : n = (n - 25150) + 25150 := by omega
          rw [heq]
          exact pos_w503 ⟨n - 25150, hr⟩
        · by_cases h4 : n < 25250
          · have hr : n - 25200 < 50 := by omega
            have heq : n = (n - 25200) + 25200 := by omega
            rw [heq]
            exact pos_w504 ⟨n - 25200, hr⟩
          · by_cases h5 : n < 25300
            · have hr : n - 25250 < 50 := by omega
              have heq : n = (n - 25250) + 25250 := by omega
              rw [heq]
              exact pos_w505 ⟨n - 25250, hr⟩
            · by_cases h6 : n < 25350
              · have hr : n - 25300 < 50 := by omega
                have heq : n = (n - 25300) + 25300 := by omega
                rw [heq]
                exact pos_w506 ⟨n - 25300, hr⟩
              · by_cases h7 : n < 25400
                · have hr : n - 25350 < 50 := by omega
                  have heq : n = (n - 25350) + 25350 := by omega
                  rw [heq]
                  exact pos_w507 ⟨n - 25350, hr⟩
                · by_cases h8 : n < 25450
                  · have hr : n - 25400 < 50 := by omega
                    have heq : n = (n - 25400) + 25400 := by omega
                    rw [heq]
                    exact pos_w508 ⟨n - 25400, hr⟩
                  · by_cases h9 : n < 25500
                    · have hr : n - 25450 < 50 := by omega
                      have heq : n = (n - 25450) + 25450 := by omega
                      rw [heq]
                      exact pos_w509 ⟨n - 25450, hr⟩
                    · by_cases h10 : n < 25550
                      · have hr : n - 25500 < 50 := by omega
                        have heq : n = (n - 25500) + 25500 := by omega
                        rw [heq]
                        exact pos_w510 ⟨n - 25500, hr⟩
                      · by_cases h11 : n < 25600
                        · have hr : n - 25550 < 50 := by omega
                          have heq : n = (n - 25550) + 25550 := by omega
                          rw [heq]
                          exact pos_w511 ⟨n - 25550, hr⟩
                        · by_cases h12 : n < 25650
                          · have hr : n - 25600 < 50 := by omega
                            have heq : n = (n - 25600) + 25600 := by omega
                            rw [heq]
                            exact pos_w512 ⟨n - 25600, hr⟩
                          · by_cases h13 : n < 25700
                            · have hr : n - 25650 < 50 := by omega
                              have heq : n = (n - 25650) + 25650 := by omega
                              rw [heq]
                              exact pos_w513 ⟨n - 25650, hr⟩
                            · by_cases h14 : n < 25750
                              · have hr : n - 25700 < 50 := by omega
                                have heq : n = (n - 25700) + 25700 := by omega
                                rw [heq]
                                exact pos_w514 ⟨n - 25700, hr⟩
                              · by_cases h15 : n < 25800
                                · have hr : n - 25750 < 50 := by omega
                                  have heq : n = (n - 25750) + 25750 := by omega
                                  rw [heq]
                                  exact pos_w515 ⟨n - 25750, hr⟩
                                · by_cases h16 : n < 25850
                                  · have hr : n - 25800 < 50 := by omega
                                    have heq : n = (n - 25800) + 25800 := by omega
                                    rw [heq]
                                    exact pos_w516 ⟨n - 25800, hr⟩
                                  · by_cases h17 : n < 25900
                                    · have hr : n - 25850 < 50 := by omega
                                      have heq : n = (n - 25850) + 25850 := by omega
                                      rw [heq]
                                      exact pos_w517 ⟨n - 25850, hr⟩
                                    · by_cases h18 : n < 25950
                                      · have hr : n - 25900 < 50 := by omega
                                        have heq : n = (n - 25900) + 25900 := by omega
                                        rw [heq]
                                        exact pos_w518 ⟨n - 25900, hr⟩
                                      · by_cases h19 : n < 26000
                                        · have hr : n - 25950 < 50 := by omega
                                          have heq : n = (n - 25950) + 25950 := by omega
                                          rw [heq]
                                          exact pos_w519 ⟨n - 25950, hr⟩
                                        · by_cases h20 : n < 26050
                                          · have hr : n - 26000 < 50 := by omega
                                            have heq : n = (n - 26000) + 26000 := by omega
                                            rw [heq]
                                            exact pos_w520 ⟨n - 26000, hr⟩
                                          · by_cases h21 : n < 26100
                                            · have hr : n - 26050 < 50 := by omega
                                              have heq : n = (n - 26050) + 26050 := by omega
                                              rw [heq]
                                              exact pos_w521 ⟨n - 26050, hr⟩
                                            · by_cases h22 : n < 26150
                                              · have hr : n - 26100 < 50 := by omega
                                                have heq : n = (n - 26100) + 26100 := by omega
                                                rw [heq]
                                                exact pos_w522 ⟨n - 26100, hr⟩
                                              · by_cases h23 : n < 26200
                                                · have hr : n - 26150 < 50 := by omega
                                                  have heq : n = (n - 26150) + 26150 := by omega
                                                  rw [heq]
                                                  exact pos_w523 ⟨n - 26150, hr⟩
                                                · by_cases h24 : n < 26250
                                                  · have hr : n - 26200 < 50 := by omega
                                                    have heq : n = (n - 26200) + 26200 := by omega
                                                    rw [heq]
                                                    exact pos_w524 ⟨n - 26200, hr⟩
                                                  · by_cases h25 : n < 26300
                                                    · have hr : n - 26250 < 50 := by omega
                                                      have heq : n = (n - 26250) + 26250 := by omega
                                                      rw [heq]
                                                      exact pos_w525 ⟨n - 26250, hr⟩
                                                    · by_cases h26 : n < 26350
                                                      · have hr : n - 26300 < 50 := by omega
                                                        have heq : n = (n - 26300) + 26300 := by omega
                                                        rw [heq]
                                                        exact pos_w526 ⟨n - 26300, hr⟩
                                                      · by_cases h27 : n < 26400
                                                        · have hr : n - 26350 < 50 := by omega
                                                          have heq : n = (n - 26350) + 26350 := by omega
                                                          rw [heq]
                                                          exact pos_w527 ⟨n - 26350, hr⟩
                                                        · by_cases h28 : n < 26450
                                                          · have hr : n - 26400 < 50 := by omega
                                                            have heq : n = (n - 26400) + 26400 := by omega
                                                            rw [heq]
                                                            exact pos_w528 ⟨n - 26400, hr⟩
                                                          · by_cases h29 : n < 26500
                                                            · have hr : n - 26450 < 50 := by omega
                                                              have heq : n = (n - 26450) + 26450 := by omega
                                                              rw [heq]
                                                              exact pos_w529 ⟨n - 26450, hr⟩
                                                            · by_cases h30 : n < 26550
                                                              · have hr : n - 26500 < 50 := by omega
                                                                have heq : n = (n - 26500) + 26500 := by omega
                                                                rw [heq]
                                                                exact pos_w530 ⟨n - 26500, hr⟩
                                                              · by_cases h31 : n < 26600
                                                                · have hr : n - 26550 < 50 := by omega
                                                                  have heq : n = (n - 26550) + 26550 := by omega
                                                                  rw [heq]
                                                                  exact pos_w531 ⟨n - 26550, hr⟩
                                                                · by_cases h32 : n < 26650
                                                                  · have hr : n - 26600 < 50 := by omega
                                                                    have heq : n = (n - 26600) + 26600 := by omega
                                                                    rw [heq]
                                                                    exact pos_w532 ⟨n - 26600, hr⟩
                                                                  · by_cases h33 : n < 26700
                                                                    · have hr : n - 26650 < 50 := by omega
                                                                      have heq : n = (n - 26650) + 26650 := by omega
                                                                      rw [heq]
                                                                      exact pos_w533 ⟨n - 26650, hr⟩
                                                                    · by_cases h34 : n < 26750
                                                                      · have hr : n - 26700 < 50 := by omega
                                                                        have heq : n = (n - 26700) + 26700 := by omega
                                                                        rw [heq]
                                                                        exact pos_w534 ⟨n - 26700, hr⟩
                                                                      · by_cases h35 : n < 26800
                                                                        · have hr : n - 26750 < 50 := by omega
                                                                          have heq : n = (n - 26750) + 26750 := by omega
                                                                          rw [heq]
                                                                          exact pos_w535 ⟨n - 26750, hr⟩
                                                                        · by_cases h36 : n < 26850
                                                                          · have hr : n - 26800 < 50 := by omega
                                                                            have heq : n = (n - 26800) + 26800 := by omega
                                                                            rw [heq]
                                                                            exact pos_w536 ⟨n - 26800, hr⟩
                                                                          · by_cases h37 : n < 26900
                                                                            · have hr : n - 26850 < 50 := by omega
                                                                              have heq : n = (n - 26850) + 26850 := by omega
                                                                              rw [heq]
                                                                              exact pos_w537 ⟨n - 26850, hr⟩
                                                                            · by_cases h38 : n < 26950
                                                                              · have hr : n - 26900 < 50 := by omega
                                                                                have heq : n = (n - 26900) + 26900 := by omega
                                                                                rw [heq]
                                                                                exact pos_w538 ⟨n - 26900, hr⟩
                                                                              · by_cases h39 : n < 27000
                                                                                · have hr : n - 26950 < 50 := by omega
                                                                                  have heq : n = (n - 26950) + 26950 := by omega
                                                                                  rw [heq]
                                                                                  exact pos_w539 ⟨n - 26950, hr⟩
                                                                                · by_cases h40 : n < 27050
                                                                                  · have hr : n - 27000 < 50 := by omega
                                                                                    have heq : n = (n - 27000) + 27000 := by omega
                                                                                    rw [heq]
                                                                                    exact pos_w540 ⟨n - 27000, hr⟩
                                                                                  · by_cases h41 : n < 27100
                                                                                    · have hr : n - 27050 < 50 := by omega
                                                                                      have heq : n = (n - 27050) + 27050 := by omega
                                                                                      rw [heq]
                                                                                      exact pos_w541 ⟨n - 27050, hr⟩
                                                                                    · by_cases h42 : n < 27150
                                                                                      · have hr : n - 27100 < 50 := by omega
                                                                                        have heq : n = (n - 27100) + 27100 := by omega
                                                                                        rw [heq]
                                                                                        exact pos_w542 ⟨n - 27100, hr⟩
                                                                                      · by_cases h43 : n < 27200
                                                                                        · have hr : n - 27150 < 50 := by omega
                                                                                          have heq : n = (n - 27150) + 27150 := by omega
                                                                                          rw [heq]
                                                                                          exact pos_w543 ⟨n - 27150, hr⟩
                                                                                        · by_cases h44 : n < 27250
                                                                                          · have hr : n - 27200 < 50 := by omega
                                                                                            have heq : n = (n - 27200) + 27200 := by omega
                                                                                            rw [heq]
                                                                                            exact pos_w544 ⟨n - 27200, hr⟩
                                                                                          · by_cases h45 : n < 27300
                                                                                            · have hr : n - 27250 < 50 := by omega
                                                                                              have heq : n = (n - 27250) + 27250 := by omega
                                                                                              rw [heq]
                                                                                              exact pos_w545 ⟨n - 27250, hr⟩
                                                                                            · by_cases h46 : n < 27350
                                                                                              · have hr : n - 27300 < 50 := by omega
                                                                                                have heq : n = (n - 27300) + 27300 := by omega
                                                                                                rw [heq]
                                                                                                exact pos_w546 ⟨n - 27300, hr⟩
                                                                                              · by_cases h47 : n < 27400
                                                                                                · have hr : n - 27350 < 50 := by omega
                                                                                                  have heq : n = (n - 27350) + 27350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact pos_w547 ⟨n - 27350, hr⟩
                                                                                                · by_cases h48 : n < 27450
                                                                                                  · have hr : n - 27400 < 50 := by omega
                                                                                                    have heq : n = (n - 27400) + 27400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact pos_w548 ⟨n - 27400, hr⟩
                                                                                                  · by_cases h49 : n < 27500
                                                                                                    · have hr : n - 27450 < 50 := by omega
                                                                                                      have heq : n = (n - 27450) + 27450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact pos_w549 ⟨n - 27450, hr⟩
                                                                                                    · by_cases h50 : n < 27550
                                                                                                      · have hr : n - 27500 < 50 := by omega
                                                                                                        have heq : n = (n - 27500) + 27500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact pos_w550 ⟨n - 27500, hr⟩
                                                                                                      · by_cases h51 : n < 27600
                                                                                                        · have hr : n - 27550 < 50 := by omega
                                                                                                          have heq : n = (n - 27550) + 27550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact pos_w551 ⟨n - 27550, hr⟩
                                                                                                        · by_cases h52 : n < 27650
                                                                                                          · have hr : n - 27600 < 50 := by omega
                                                                                                            have heq : n = (n - 27600) + 27600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact pos_w552 ⟨n - 27600, hr⟩
                                                                                                          · by_cases h53 : n < 27700
                                                                                                            · have hr : n - 27650 < 50 := by omega
                                                                                                              have heq : n = (n - 27650) + 27650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact pos_w553 ⟨n - 27650, hr⟩
                                                                                                            · by_cases h54 : n < 27750
                                                                                                              · have hr : n - 27700 < 50 := by omega
                                                                                                                have heq : n = (n - 27700) + 27700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact pos_w554 ⟨n - 27700, hr⟩
                                                                                                              · by_cases h55 : n < 27800
                                                                                                                · have hr : n - 27750 < 50 := by omega
                                                                                                                  have heq : n = (n - 27750) + 27750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact pos_w555 ⟨n - 27750, hr⟩
                                                                                                                · by_cases h56 : n < 27850
                                                                                                                  · have hr : n - 27800 < 50 := by omega
                                                                                                                    have heq : n = (n - 27800) + 27800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact pos_w556 ⟨n - 27800, hr⟩
                                                                                                                  · by_cases h57 : n < 27900
                                                                                                                    · have hr : n - 27850 < 50 := by omega
                                                                                                                      have heq : n = (n - 27850) + 27850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact pos_w557 ⟨n - 27850, hr⟩
                                                                                                                    · by_cases h58 : n < 27950
                                                                                                                      · have hr : n - 27900 < 50 := by omega
                                                                                                                        have heq : n = (n - 27900) + 27900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact pos_w558 ⟨n - 27900, hr⟩
                                                                                                                      · by_cases h59 : n < 28000
                                                                                                                        · have hr : n - 27950 < 50 := by omega
                                                                                                                          have heq : n = (n - 27950) + 27950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact pos_w559 ⟨n - 27950, hr⟩
                                                                                                                        · by_cases h60 : n < 28050
                                                                                                                          · have hr : n - 28000 < 50 := by omega
                                                                                                                            have heq : n = (n - 28000) + 28000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact pos_w560 ⟨n - 28000, hr⟩
                                                                                                                          · by_cases h61 : n < 28100
                                                                                                                            · have hr : n - 28050 < 50 := by omega
                                                                                                                              have heq : n = (n - 28050) + 28050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact pos_w561 ⟨n - 28050, hr⟩
                                                                                                                            · by_cases h62 : n < 28150
                                                                                                                              · have hr : n - 28100 < 50 := by omega
                                                                                                                                have heq : n = (n - 28100) + 28100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact pos_w562 ⟨n - 28100, hr⟩
                                                                                                                              · by_cases h63 : n < 28200
                                                                                                                                · have hr : n - 28150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 28150) + 28150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact pos_w563 ⟨n - 28150, hr⟩
                                                                                                                                · by_cases h64 : n < 28250
                                                                                                                                  · have hr : n - 28200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 28200) + 28200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact pos_w564 ⟨n - 28200, hr⟩
                                                                                                                                  · by_cases h65 : n < 28300
                                                                                                                                    · have hr : n - 28250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 28250) + 28250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact pos_w565 ⟨n - 28250, hr⟩
                                                                                                                                    · by_cases h66 : n < 28350
                                                                                                                                      · have hr : n - 28300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 28300) + 28300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact pos_w566 ⟨n - 28300, hr⟩
                                                                                                                                      · by_cases h67 : n < 28400
                                                                                                                                        · have hr : n - 28350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 28350) + 28350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact pos_w567 ⟨n - 28350, hr⟩
                                                                                                                                        · by_cases h68 : n < 28450
                                                                                                                                          · have hr : n - 28400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 28400) + 28400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact pos_w568 ⟨n - 28400, hr⟩
                                                                                                                                          · by_cases h69 : n < 28500
                                                                                                                                            · have hr : n - 28450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 28450) + 28450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact pos_w569 ⟨n - 28450, hr⟩
                                                                                                                                            · by_cases h70 : n < 28550
                                                                                                                                              · have hr : n - 28500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 28500) + 28500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact pos_w570 ⟨n - 28500, hr⟩
                                                                                                                                              · by_cases h71 : n < 28600
                                                                                                                                                · have hr : n - 28550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 28550) + 28550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact pos_w571 ⟨n - 28550, hr⟩
                                                                                                                                                · by_cases h72 : n < 28650
                                                                                                                                                  · have hr : n - 28600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 28600) + 28600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact pos_w572 ⟨n - 28600, hr⟩
                                                                                                                                                  · by_cases h73 : n < 28700
                                                                                                                                                    · have hr : n - 28650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 28650) + 28650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact pos_w573 ⟨n - 28650, hr⟩
                                                                                                                                                    · by_cases h74 : n < 28750
                                                                                                                                                      · have hr : n - 28700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 28700) + 28700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact pos_w574 ⟨n - 28700, hr⟩
                                                                                                                                                      · by_cases h75 : n < 28800
                                                                                                                                                        · have hr : n - 28750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 28750) + 28750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact pos_w575 ⟨n - 28750, hr⟩
                                                                                                                                                        · by_cases h76 : n < 28850
                                                                                                                                                          · have hr : n - 28800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 28800) + 28800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact pos_w576 ⟨n - 28800, hr⟩
                                                                                                                                                          · by_cases h77 : n < 28900
                                                                                                                                                            · have hr : n - 28850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 28850) + 28850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact pos_w577 ⟨n - 28850, hr⟩
                                                                                                                                                            · by_cases h78 : n < 28950
                                                                                                                                                              · have hr : n - 28900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 28900) + 28900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact pos_w578 ⟨n - 28900, hr⟩
                                                                                                                                                              · by_cases h79 : n < 29000
                                                                                                                                                                · have hr : n - 28950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 28950) + 28950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact pos_w579 ⟨n - 28950, hr⟩
                                                                                                                                                                · by_cases h80 : n < 29050
                                                                                                                                                                  · have hr : n - 29000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 29000) + 29000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact pos_w580 ⟨n - 29000, hr⟩
                                                                                                                                                                  · by_cases h81 : n < 29100
                                                                                                                                                                    · have hr : n - 29050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 29050) + 29050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact pos_w581 ⟨n - 29050, hr⟩
                                                                                                                                                                    · by_cases h82 : n < 29150
                                                                                                                                                                      · have hr : n - 29100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 29100) + 29100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact pos_w582 ⟨n - 29100, hr⟩
                                                                                                                                                                      · by_cases h83 : n < 29200
                                                                                                                                                                        · have hr : n - 29150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 29150) + 29150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact pos_w583 ⟨n - 29150, hr⟩
                                                                                                                                                                        · by_cases h84 : n < 29250
                                                                                                                                                                          · have hr : n - 29200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 29200) + 29200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact pos_w584 ⟨n - 29200, hr⟩
                                                                                                                                                                          · by_cases h85 : n < 29300
                                                                                                                                                                            · have hr : n - 29250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 29250) + 29250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact pos_w585 ⟨n - 29250, hr⟩
                                                                                                                                                                            · by_cases h86 : n < 29350
                                                                                                                                                                              · have hr : n - 29300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 29300) + 29300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact pos_w586 ⟨n - 29300, hr⟩
                                                                                                                                                                              · by_cases h87 : n < 29400
                                                                                                                                                                                · have hr : n - 29350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 29350) + 29350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact pos_w587 ⟨n - 29350, hr⟩
                                                                                                                                                                                · by_cases h88 : n < 29450
                                                                                                                                                                                  · have hr : n - 29400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 29400) + 29400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact pos_w588 ⟨n - 29400, hr⟩
                                                                                                                                                                                  · by_cases h89 : n < 29500
                                                                                                                                                                                    · have hr : n - 29450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 29450) + 29450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact pos_w589 ⟨n - 29450, hr⟩
                                                                                                                                                                                    · by_cases h90 : n < 29550
                                                                                                                                                                                      · have hr : n - 29500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 29500) + 29500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact pos_w590 ⟨n - 29500, hr⟩
                                                                                                                                                                                      · by_cases h91 : n < 29600
                                                                                                                                                                                        · have hr : n - 29550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 29550) + 29550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact pos_w591 ⟨n - 29550, hr⟩
                                                                                                                                                                                        · by_cases h92 : n < 29650
                                                                                                                                                                                          · have hr : n - 29600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 29600) + 29600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact pos_w592 ⟨n - 29600, hr⟩
                                                                                                                                                                                          · by_cases h93 : n < 29700
                                                                                                                                                                                            · have hr : n - 29650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 29650) + 29650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact pos_w593 ⟨n - 29650, hr⟩
                                                                                                                                                                                            · by_cases h94 : n < 29750
                                                                                                                                                                                              · have hr : n - 29700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 29700) + 29700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact pos_w594 ⟨n - 29700, hr⟩
                                                                                                                                                                                              · by_cases h95 : n < 29800
                                                                                                                                                                                                · have hr : n - 29750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 29750) + 29750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact pos_w595 ⟨n - 29750, hr⟩
                                                                                                                                                                                                · by_cases h96 : n < 29850
                                                                                                                                                                                                  · have hr : n - 29800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 29800) + 29800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact pos_w596 ⟨n - 29800, hr⟩
                                                                                                                                                                                                  · by_cases h97 : n < 29900
                                                                                                                                                                                                    · have hr : n - 29850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 29850) + 29850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact pos_w597 ⟨n - 29850, hr⟩
                                                                                                                                                                                                    · by_cases h98 : n < 29950
                                                                                                                                                                                                      · have hr : n - 29900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 29900) + 29900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact pos_w598 ⟨n - 29900, hr⟩
                                                                                                                                                                                                      · by_cases h99 : n < 30000
                                                                                                                                                                                                        · have hr : n - 29950 < 50 := by omega
                                                                                                                                                                                                          have heq : n = (n - 29950) + 29950 := by omega
                                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                                          exact pos_w599 ⟨n - 29950, hr⟩
                                                                                                                                                                                                        · omega

end IntMul.Kappa.R8.Bit.Oppbank.DimBound5


