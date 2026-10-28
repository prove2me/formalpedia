-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound6
-- name    : IntMul_Kappa_R8_Data_BitOppbankDimBound6
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:02:37.569861+00:00
-- url     : https://prove2.me/theorems/56a62393-e8ac-465d-aa53-f4aea256fe4d
-- title:
--   Densified dimF $\le 22$ pack 6 ($[30000,35000)$)
-- statement:
--   Pack 6 of the densified dimension-field bound.
--
--   For every densified node index $n$ with $30000\le n<35000$, the 5-bit field $\mathrm{dimF}(n)$ extracted from $\mathrm{DIMT}$ satisfies
--   $$1\le \mathrm{dimF}(n)\le 22.$$
--   Proved by `decide` on successive `Fin 50` windows (no `native_decide`).
-- source:
--   R8 BitNB densified DIMT field bound; Fin-window decide packs

-- DimBound pack 6: dimF bounds on n ∈ [30000, 35000)

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

namespace IntMul.Kappa.R8.Bit.Oppbank.DimBound6

private theorem le_w600 : ∀ n : Fin 50, dimF (n.val + 30000) ≤ 22 := by decide
private theorem pos_w600 : ∀ n : Fin 50, 0 < dimF (n.val + 30000) := by decide
private theorem le_w601 : ∀ n : Fin 50, dimF (n.val + 30050) ≤ 22 := by decide
private theorem pos_w601 : ∀ n : Fin 50, 0 < dimF (n.val + 30050) := by decide
private theorem le_w602 : ∀ n : Fin 50, dimF (n.val + 30100) ≤ 22 := by decide
private theorem pos_w602 : ∀ n : Fin 50, 0 < dimF (n.val + 30100) := by decide
private theorem le_w603 : ∀ n : Fin 50, dimF (n.val + 30150) ≤ 22 := by decide
private theorem pos_w603 : ∀ n : Fin 50, 0 < dimF (n.val + 30150) := by decide
private theorem le_w604 : ∀ n : Fin 50, dimF (n.val + 30200) ≤ 22 := by decide
private theorem pos_w604 : ∀ n : Fin 50, 0 < dimF (n.val + 30200) := by decide
private theorem le_w605 : ∀ n : Fin 50, dimF (n.val + 30250) ≤ 22 := by decide
private theorem pos_w605 : ∀ n : Fin 50, 0 < dimF (n.val + 30250) := by decide
private theorem le_w606 : ∀ n : Fin 50, dimF (n.val + 30300) ≤ 22 := by decide
private theorem pos_w606 : ∀ n : Fin 50, 0 < dimF (n.val + 30300) := by decide
private theorem le_w607 : ∀ n : Fin 50, dimF (n.val + 30350) ≤ 22 := by decide
private theorem pos_w607 : ∀ n : Fin 50, 0 < dimF (n.val + 30350) := by decide
private theorem le_w608 : ∀ n : Fin 50, dimF (n.val + 30400) ≤ 22 := by decide
private theorem pos_w608 : ∀ n : Fin 50, 0 < dimF (n.val + 30400) := by decide
private theorem le_w609 : ∀ n : Fin 50, dimF (n.val + 30450) ≤ 22 := by decide
private theorem pos_w609 : ∀ n : Fin 50, 0 < dimF (n.val + 30450) := by decide
private theorem le_w610 : ∀ n : Fin 50, dimF (n.val + 30500) ≤ 22 := by decide
private theorem pos_w610 : ∀ n : Fin 50, 0 < dimF (n.val + 30500) := by decide
private theorem le_w611 : ∀ n : Fin 50, dimF (n.val + 30550) ≤ 22 := by decide
private theorem pos_w611 : ∀ n : Fin 50, 0 < dimF (n.val + 30550) := by decide
private theorem le_w612 : ∀ n : Fin 50, dimF (n.val + 30600) ≤ 22 := by decide
private theorem pos_w612 : ∀ n : Fin 50, 0 < dimF (n.val + 30600) := by decide
private theorem le_w613 : ∀ n : Fin 50, dimF (n.val + 30650) ≤ 22 := by decide
private theorem pos_w613 : ∀ n : Fin 50, 0 < dimF (n.val + 30650) := by decide
private theorem le_w614 : ∀ n : Fin 50, dimF (n.val + 30700) ≤ 22 := by decide
private theorem pos_w614 : ∀ n : Fin 50, 0 < dimF (n.val + 30700) := by decide
private theorem le_w615 : ∀ n : Fin 50, dimF (n.val + 30750) ≤ 22 := by decide
private theorem pos_w615 : ∀ n : Fin 50, 0 < dimF (n.val + 30750) := by decide
private theorem le_w616 : ∀ n : Fin 50, dimF (n.val + 30800) ≤ 22 := by decide
private theorem pos_w616 : ∀ n : Fin 50, 0 < dimF (n.val + 30800) := by decide
private theorem le_w617 : ∀ n : Fin 50, dimF (n.val + 30850) ≤ 22 := by decide
private theorem pos_w617 : ∀ n : Fin 50, 0 < dimF (n.val + 30850) := by decide
private theorem le_w618 : ∀ n : Fin 50, dimF (n.val + 30900) ≤ 22 := by decide
private theorem pos_w618 : ∀ n : Fin 50, 0 < dimF (n.val + 30900) := by decide
private theorem le_w619 : ∀ n : Fin 50, dimF (n.val + 30950) ≤ 22 := by decide
private theorem pos_w619 : ∀ n : Fin 50, 0 < dimF (n.val + 30950) := by decide
private theorem le_w620 : ∀ n : Fin 50, dimF (n.val + 31000) ≤ 22 := by decide
private theorem pos_w620 : ∀ n : Fin 50, 0 < dimF (n.val + 31000) := by decide
private theorem le_w621 : ∀ n : Fin 50, dimF (n.val + 31050) ≤ 22 := by decide
private theorem pos_w621 : ∀ n : Fin 50, 0 < dimF (n.val + 31050) := by decide
private theorem le_w622 : ∀ n : Fin 50, dimF (n.val + 31100) ≤ 22 := by decide
private theorem pos_w622 : ∀ n : Fin 50, 0 < dimF (n.val + 31100) := by decide
private theorem le_w623 : ∀ n : Fin 50, dimF (n.val + 31150) ≤ 22 := by decide
private theorem pos_w623 : ∀ n : Fin 50, 0 < dimF (n.val + 31150) := by decide
private theorem le_w624 : ∀ n : Fin 50, dimF (n.val + 31200) ≤ 22 := by decide
private theorem pos_w624 : ∀ n : Fin 50, 0 < dimF (n.val + 31200) := by decide
private theorem le_w625 : ∀ n : Fin 50, dimF (n.val + 31250) ≤ 22 := by decide
private theorem pos_w625 : ∀ n : Fin 50, 0 < dimF (n.val + 31250) := by decide
private theorem le_w626 : ∀ n : Fin 50, dimF (n.val + 31300) ≤ 22 := by decide
private theorem pos_w626 : ∀ n : Fin 50, 0 < dimF (n.val + 31300) := by decide
private theorem le_w627 : ∀ n : Fin 50, dimF (n.val + 31350) ≤ 22 := by decide
private theorem pos_w627 : ∀ n : Fin 50, 0 < dimF (n.val + 31350) := by decide
private theorem le_w628 : ∀ n : Fin 50, dimF (n.val + 31400) ≤ 22 := by decide
private theorem pos_w628 : ∀ n : Fin 50, 0 < dimF (n.val + 31400) := by decide
private theorem le_w629 : ∀ n : Fin 50, dimF (n.val + 31450) ≤ 22 := by decide
private theorem pos_w629 : ∀ n : Fin 50, 0 < dimF (n.val + 31450) := by decide
private theorem le_w630 : ∀ n : Fin 50, dimF (n.val + 31500) ≤ 22 := by decide
private theorem pos_w630 : ∀ n : Fin 50, 0 < dimF (n.val + 31500) := by decide
private theorem le_w631 : ∀ n : Fin 50, dimF (n.val + 31550) ≤ 22 := by decide
private theorem pos_w631 : ∀ n : Fin 50, 0 < dimF (n.val + 31550) := by decide
private theorem le_w632 : ∀ n : Fin 50, dimF (n.val + 31600) ≤ 22 := by decide
private theorem pos_w632 : ∀ n : Fin 50, 0 < dimF (n.val + 31600) := by decide
private theorem le_w633 : ∀ n : Fin 50, dimF (n.val + 31650) ≤ 22 := by decide
private theorem pos_w633 : ∀ n : Fin 50, 0 < dimF (n.val + 31650) := by decide
private theorem le_w634 : ∀ n : Fin 50, dimF (n.val + 31700) ≤ 22 := by decide
private theorem pos_w634 : ∀ n : Fin 50, 0 < dimF (n.val + 31700) := by decide
private theorem le_w635 : ∀ n : Fin 50, dimF (n.val + 31750) ≤ 22 := by decide
private theorem pos_w635 : ∀ n : Fin 50, 0 < dimF (n.val + 31750) := by decide
private theorem le_w636 : ∀ n : Fin 50, dimF (n.val + 31800) ≤ 22 := by decide
private theorem pos_w636 : ∀ n : Fin 50, 0 < dimF (n.val + 31800) := by decide
private theorem le_w637 : ∀ n : Fin 50, dimF (n.val + 31850) ≤ 22 := by decide
private theorem pos_w637 : ∀ n : Fin 50, 0 < dimF (n.val + 31850) := by decide
private theorem le_w638 : ∀ n : Fin 50, dimF (n.val + 31900) ≤ 22 := by decide
private theorem pos_w638 : ∀ n : Fin 50, 0 < dimF (n.val + 31900) := by decide
private theorem le_w639 : ∀ n : Fin 50, dimF (n.val + 31950) ≤ 22 := by decide
private theorem pos_w639 : ∀ n : Fin 50, 0 < dimF (n.val + 31950) := by decide
private theorem le_w640 : ∀ n : Fin 50, dimF (n.val + 32000) ≤ 22 := by decide
private theorem pos_w640 : ∀ n : Fin 50, 0 < dimF (n.val + 32000) := by decide
private theorem le_w641 : ∀ n : Fin 50, dimF (n.val + 32050) ≤ 22 := by decide
private theorem pos_w641 : ∀ n : Fin 50, 0 < dimF (n.val + 32050) := by decide
private theorem le_w642 : ∀ n : Fin 50, dimF (n.val + 32100) ≤ 22 := by decide
private theorem pos_w642 : ∀ n : Fin 50, 0 < dimF (n.val + 32100) := by decide
private theorem le_w643 : ∀ n : Fin 50, dimF (n.val + 32150) ≤ 22 := by decide
private theorem pos_w643 : ∀ n : Fin 50, 0 < dimF (n.val + 32150) := by decide
private theorem le_w644 : ∀ n : Fin 50, dimF (n.val + 32200) ≤ 22 := by decide
private theorem pos_w644 : ∀ n : Fin 50, 0 < dimF (n.val + 32200) := by decide
private theorem le_w645 : ∀ n : Fin 50, dimF (n.val + 32250) ≤ 22 := by decide
private theorem pos_w645 : ∀ n : Fin 50, 0 < dimF (n.val + 32250) := by decide
private theorem le_w646 : ∀ n : Fin 50, dimF (n.val + 32300) ≤ 22 := by decide
private theorem pos_w646 : ∀ n : Fin 50, 0 < dimF (n.val + 32300) := by decide
private theorem le_w647 : ∀ n : Fin 50, dimF (n.val + 32350) ≤ 22 := by decide
private theorem pos_w647 : ∀ n : Fin 50, 0 < dimF (n.val + 32350) := by decide
private theorem le_w648 : ∀ n : Fin 50, dimF (n.val + 32400) ≤ 22 := by decide
private theorem pos_w648 : ∀ n : Fin 50, 0 < dimF (n.val + 32400) := by decide
private theorem le_w649 : ∀ n : Fin 50, dimF (n.val + 32450) ≤ 22 := by decide
private theorem pos_w649 : ∀ n : Fin 50, 0 < dimF (n.val + 32450) := by decide
private theorem le_w650 : ∀ n : Fin 50, dimF (n.val + 32500) ≤ 22 := by decide
private theorem pos_w650 : ∀ n : Fin 50, 0 < dimF (n.val + 32500) := by decide
private theorem le_w651 : ∀ n : Fin 50, dimF (n.val + 32550) ≤ 22 := by decide
private theorem pos_w651 : ∀ n : Fin 50, 0 < dimF (n.val + 32550) := by decide
private theorem le_w652 : ∀ n : Fin 50, dimF (n.val + 32600) ≤ 22 := by decide
private theorem pos_w652 : ∀ n : Fin 50, 0 < dimF (n.val + 32600) := by decide
private theorem le_w653 : ∀ n : Fin 50, dimF (n.val + 32650) ≤ 22 := by decide
private theorem pos_w653 : ∀ n : Fin 50, 0 < dimF (n.val + 32650) := by decide
private theorem le_w654 : ∀ n : Fin 50, dimF (n.val + 32700) ≤ 22 := by decide
private theorem pos_w654 : ∀ n : Fin 50, 0 < dimF (n.val + 32700) := by decide
private theorem le_w655 : ∀ n : Fin 50, dimF (n.val + 32750) ≤ 22 := by decide
private theorem pos_w655 : ∀ n : Fin 50, 0 < dimF (n.val + 32750) := by decide
private theorem le_w656 : ∀ n : Fin 50, dimF (n.val + 32800) ≤ 22 := by decide
private theorem pos_w656 : ∀ n : Fin 50, 0 < dimF (n.val + 32800) := by decide
private theorem le_w657 : ∀ n : Fin 50, dimF (n.val + 32850) ≤ 22 := by decide
private theorem pos_w657 : ∀ n : Fin 50, 0 < dimF (n.val + 32850) := by decide
private theorem le_w658 : ∀ n : Fin 50, dimF (n.val + 32900) ≤ 22 := by decide
private theorem pos_w658 : ∀ n : Fin 50, 0 < dimF (n.val + 32900) := by decide
private theorem le_w659 : ∀ n : Fin 50, dimF (n.val + 32950) ≤ 22 := by decide
private theorem pos_w659 : ∀ n : Fin 50, 0 < dimF (n.val + 32950) := by decide
private theorem le_w660 : ∀ n : Fin 50, dimF (n.val + 33000) ≤ 22 := by decide
private theorem pos_w660 : ∀ n : Fin 50, 0 < dimF (n.val + 33000) := by decide
private theorem le_w661 : ∀ n : Fin 50, dimF (n.val + 33050) ≤ 22 := by decide
private theorem pos_w661 : ∀ n : Fin 50, 0 < dimF (n.val + 33050) := by decide
private theorem le_w662 : ∀ n : Fin 50, dimF (n.val + 33100) ≤ 22 := by decide
private theorem pos_w662 : ∀ n : Fin 50, 0 < dimF (n.val + 33100) := by decide
private theorem le_w663 : ∀ n : Fin 50, dimF (n.val + 33150) ≤ 22 := by decide
private theorem pos_w663 : ∀ n : Fin 50, 0 < dimF (n.val + 33150) := by decide
private theorem le_w664 : ∀ n : Fin 50, dimF (n.val + 33200) ≤ 22 := by decide
private theorem pos_w664 : ∀ n : Fin 50, 0 < dimF (n.val + 33200) := by decide
private theorem le_w665 : ∀ n : Fin 50, dimF (n.val + 33250) ≤ 22 := by decide
private theorem pos_w665 : ∀ n : Fin 50, 0 < dimF (n.val + 33250) := by decide
private theorem le_w666 : ∀ n : Fin 50, dimF (n.val + 33300) ≤ 22 := by decide
private theorem pos_w666 : ∀ n : Fin 50, 0 < dimF (n.val + 33300) := by decide
private theorem le_w667 : ∀ n : Fin 50, dimF (n.val + 33350) ≤ 22 := by decide
private theorem pos_w667 : ∀ n : Fin 50, 0 < dimF (n.val + 33350) := by decide
private theorem le_w668 : ∀ n : Fin 50, dimF (n.val + 33400) ≤ 22 := by decide
private theorem pos_w668 : ∀ n : Fin 50, 0 < dimF (n.val + 33400) := by decide
private theorem le_w669 : ∀ n : Fin 50, dimF (n.val + 33450) ≤ 22 := by decide
private theorem pos_w669 : ∀ n : Fin 50, 0 < dimF (n.val + 33450) := by decide
private theorem le_w670 : ∀ n : Fin 50, dimF (n.val + 33500) ≤ 22 := by decide
private theorem pos_w670 : ∀ n : Fin 50, 0 < dimF (n.val + 33500) := by decide
private theorem le_w671 : ∀ n : Fin 50, dimF (n.val + 33550) ≤ 22 := by decide
private theorem pos_w671 : ∀ n : Fin 50, 0 < dimF (n.val + 33550) := by decide
private theorem le_w672 : ∀ n : Fin 50, dimF (n.val + 33600) ≤ 22 := by decide
private theorem pos_w672 : ∀ n : Fin 50, 0 < dimF (n.val + 33600) := by decide
private theorem le_w673 : ∀ n : Fin 50, dimF (n.val + 33650) ≤ 22 := by decide
private theorem pos_w673 : ∀ n : Fin 50, 0 < dimF (n.val + 33650) := by decide
private theorem le_w674 : ∀ n : Fin 50, dimF (n.val + 33700) ≤ 22 := by decide
private theorem pos_w674 : ∀ n : Fin 50, 0 < dimF (n.val + 33700) := by decide
private theorem le_w675 : ∀ n : Fin 50, dimF (n.val + 33750) ≤ 22 := by decide
private theorem pos_w675 : ∀ n : Fin 50, 0 < dimF (n.val + 33750) := by decide
private theorem le_w676 : ∀ n : Fin 50, dimF (n.val + 33800) ≤ 22 := by decide
private theorem pos_w676 : ∀ n : Fin 50, 0 < dimF (n.val + 33800) := by decide
private theorem le_w677 : ∀ n : Fin 50, dimF (n.val + 33850) ≤ 22 := by decide
private theorem pos_w677 : ∀ n : Fin 50, 0 < dimF (n.val + 33850) := by decide
private theorem le_w678 : ∀ n : Fin 50, dimF (n.val + 33900) ≤ 22 := by decide
private theorem pos_w678 : ∀ n : Fin 50, 0 < dimF (n.val + 33900) := by decide
private theorem le_w679 : ∀ n : Fin 50, dimF (n.val + 33950) ≤ 22 := by decide
private theorem pos_w679 : ∀ n : Fin 50, 0 < dimF (n.val + 33950) := by decide
private theorem le_w680 : ∀ n : Fin 50, dimF (n.val + 34000) ≤ 22 := by decide
private theorem pos_w680 : ∀ n : Fin 50, 0 < dimF (n.val + 34000) := by decide
private theorem le_w681 : ∀ n : Fin 50, dimF (n.val + 34050) ≤ 22 := by decide
private theorem pos_w681 : ∀ n : Fin 50, 0 < dimF (n.val + 34050) := by decide
private theorem le_w682 : ∀ n : Fin 50, dimF (n.val + 34100) ≤ 22 := by decide
private theorem pos_w682 : ∀ n : Fin 50, 0 < dimF (n.val + 34100) := by decide
private theorem le_w683 : ∀ n : Fin 50, dimF (n.val + 34150) ≤ 22 := by decide
private theorem pos_w683 : ∀ n : Fin 50, 0 < dimF (n.val + 34150) := by decide
private theorem le_w684 : ∀ n : Fin 50, dimF (n.val + 34200) ≤ 22 := by decide
private theorem pos_w684 : ∀ n : Fin 50, 0 < dimF (n.val + 34200) := by decide
private theorem le_w685 : ∀ n : Fin 50, dimF (n.val + 34250) ≤ 22 := by decide
private theorem pos_w685 : ∀ n : Fin 50, 0 < dimF (n.val + 34250) := by decide
private theorem le_w686 : ∀ n : Fin 50, dimF (n.val + 34300) ≤ 22 := by decide
private theorem pos_w686 : ∀ n : Fin 50, 0 < dimF (n.val + 34300) := by decide
private theorem le_w687 : ∀ n : Fin 50, dimF (n.val + 34350) ≤ 22 := by decide
private theorem pos_w687 : ∀ n : Fin 50, 0 < dimF (n.val + 34350) := by decide
private theorem le_w688 : ∀ n : Fin 50, dimF (n.val + 34400) ≤ 22 := by decide
private theorem pos_w688 : ∀ n : Fin 50, 0 < dimF (n.val + 34400) := by decide
private theorem le_w689 : ∀ n : Fin 50, dimF (n.val + 34450) ≤ 22 := by decide
private theorem pos_w689 : ∀ n : Fin 50, 0 < dimF (n.val + 34450) := by decide
private theorem le_w690 : ∀ n : Fin 50, dimF (n.val + 34500) ≤ 22 := by decide
private theorem pos_w690 : ∀ n : Fin 50, 0 < dimF (n.val + 34500) := by decide
private theorem le_w691 : ∀ n : Fin 50, dimF (n.val + 34550) ≤ 22 := by decide
private theorem pos_w691 : ∀ n : Fin 50, 0 < dimF (n.val + 34550) := by decide
private theorem le_w692 : ∀ n : Fin 50, dimF (n.val + 34600) ≤ 22 := by decide
private theorem pos_w692 : ∀ n : Fin 50, 0 < dimF (n.val + 34600) := by decide
private theorem le_w693 : ∀ n : Fin 50, dimF (n.val + 34650) ≤ 22 := by decide
private theorem pos_w693 : ∀ n : Fin 50, 0 < dimF (n.val + 34650) := by decide
private theorem le_w694 : ∀ n : Fin 50, dimF (n.val + 34700) ≤ 22 := by decide
private theorem pos_w694 : ∀ n : Fin 50, 0 < dimF (n.val + 34700) := by decide
private theorem le_w695 : ∀ n : Fin 50, dimF (n.val + 34750) ≤ 22 := by decide
private theorem pos_w695 : ∀ n : Fin 50, 0 < dimF (n.val + 34750) := by decide
private theorem le_w696 : ∀ n : Fin 50, dimF (n.val + 34800) ≤ 22 := by decide
private theorem pos_w696 : ∀ n : Fin 50, 0 < dimF (n.val + 34800) := by decide
private theorem le_w697 : ∀ n : Fin 50, dimF (n.val + 34850) ≤ 22 := by decide
private theorem pos_w697 : ∀ n : Fin 50, 0 < dimF (n.val + 34850) := by decide
private theorem le_w698 : ∀ n : Fin 50, dimF (n.val + 34900) ≤ 22 := by decide
private theorem pos_w698 : ∀ n : Fin 50, 0 < dimF (n.val + 34900) := by decide
private theorem le_w699 : ∀ n : Fin 50, dimF (n.val + 34950) ≤ 22 := by decide
private theorem pos_w699 : ∀ n : Fin 50, 0 < dimF (n.val + 34950) := by decide

theorem dimF_le_22_range : ∀ n, 30000 ≤ n → n < 35000 → dimF n ≤ 22 := by
  intro n hlo hhi
  by_cases h0 : n < 30050
  · have hr : n - 30000 < 50 := by omega
    have heq : n = (n - 30000) + 30000 := by omega
    rw [heq]
    exact le_w600 ⟨n - 30000, hr⟩
  · by_cases h1 : n < 30100
    · have hr : n - 30050 < 50 := by omega
      have heq : n = (n - 30050) + 30050 := by omega
      rw [heq]
      exact le_w601 ⟨n - 30050, hr⟩
    · by_cases h2 : n < 30150
      · have hr : n - 30100 < 50 := by omega
        have heq : n = (n - 30100) + 30100 := by omega
        rw [heq]
        exact le_w602 ⟨n - 30100, hr⟩
      · by_cases h3 : n < 30200
        · have hr : n - 30150 < 50 := by omega
          have heq : n = (n - 30150) + 30150 := by omega
          rw [heq]
          exact le_w603 ⟨n - 30150, hr⟩
        · by_cases h4 : n < 30250
          · have hr : n - 30200 < 50 := by omega
            have heq : n = (n - 30200) + 30200 := by omega
            rw [heq]
            exact le_w604 ⟨n - 30200, hr⟩
          · by_cases h5 : n < 30300
            · have hr : n - 30250 < 50 := by omega
              have heq : n = (n - 30250) + 30250 := by omega
              rw [heq]
              exact le_w605 ⟨n - 30250, hr⟩
            · by_cases h6 : n < 30350
              · have hr : n - 30300 < 50 := by omega
                have heq : n = (n - 30300) + 30300 := by omega
                rw [heq]
                exact le_w606 ⟨n - 30300, hr⟩
              · by_cases h7 : n < 30400
                · have hr : n - 30350 < 50 := by omega
                  have heq : n = (n - 30350) + 30350 := by omega
                  rw [heq]
                  exact le_w607 ⟨n - 30350, hr⟩
                · by_cases h8 : n < 30450
                  · have hr : n - 30400 < 50 := by omega
                    have heq : n = (n - 30400) + 30400 := by omega
                    rw [heq]
                    exact le_w608 ⟨n - 30400, hr⟩
                  · by_cases h9 : n < 30500
                    · have hr : n - 30450 < 50 := by omega
                      have heq : n = (n - 30450) + 30450 := by omega
                      rw [heq]
                      exact le_w609 ⟨n - 30450, hr⟩
                    · by_cases h10 : n < 30550
                      · have hr : n - 30500 < 50 := by omega
                        have heq : n = (n - 30500) + 30500 := by omega
                        rw [heq]
                        exact le_w610 ⟨n - 30500, hr⟩
                      · by_cases h11 : n < 30600
                        · have hr : n - 30550 < 50 := by omega
                          have heq : n = (n - 30550) + 30550 := by omega
                          rw [heq]
                          exact le_w611 ⟨n - 30550, hr⟩
                        · by_cases h12 : n < 30650
                          · have hr : n - 30600 < 50 := by omega
                            have heq : n = (n - 30600) + 30600 := by omega
                            rw [heq]
                            exact le_w612 ⟨n - 30600, hr⟩
                          · by_cases h13 : n < 30700
                            · have hr : n - 30650 < 50 := by omega
                              have heq : n = (n - 30650) + 30650 := by omega
                              rw [heq]
                              exact le_w613 ⟨n - 30650, hr⟩
                            · by_cases h14 : n < 30750
                              · have hr : n - 30700 < 50 := by omega
                                have heq : n = (n - 30700) + 30700 := by omega
                                rw [heq]
                                exact le_w614 ⟨n - 30700, hr⟩
                              · by_cases h15 : n < 30800
                                · have hr : n - 30750 < 50 := by omega
                                  have heq : n = (n - 30750) + 30750 := by omega
                                  rw [heq]
                                  exact le_w615 ⟨n - 30750, hr⟩
                                · by_cases h16 : n < 30850
                                  · have hr : n - 30800 < 50 := by omega
                                    have heq : n = (n - 30800) + 30800 := by omega
                                    rw [heq]
                                    exact le_w616 ⟨n - 30800, hr⟩
                                  · by_cases h17 : n < 30900
                                    · have hr : n - 30850 < 50 := by omega
                                      have heq : n = (n - 30850) + 30850 := by omega
                                      rw [heq]
                                      exact le_w617 ⟨n - 30850, hr⟩
                                    · by_cases h18 : n < 30950
                                      · have hr : n - 30900 < 50 := by omega
                                        have heq : n = (n - 30900) + 30900 := by omega
                                        rw [heq]
                                        exact le_w618 ⟨n - 30900, hr⟩
                                      · by_cases h19 : n < 31000
                                        · have hr : n - 30950 < 50 := by omega
                                          have heq : n = (n - 30950) + 30950 := by omega
                                          rw [heq]
                                          exact le_w619 ⟨n - 30950, hr⟩
                                        · by_cases h20 : n < 31050
                                          · have hr : n - 31000 < 50 := by omega
                                            have heq : n = (n - 31000) + 31000 := by omega
                                            rw [heq]
                                            exact le_w620 ⟨n - 31000, hr⟩
                                          · by_cases h21 : n < 31100
                                            · have hr : n - 31050 < 50 := by omega
                                              have heq : n = (n - 31050) + 31050 := by omega
                                              rw [heq]
                                              exact le_w621 ⟨n - 31050, hr⟩
                                            · by_cases h22 : n < 31150
                                              · have hr : n - 31100 < 50 := by omega
                                                have heq : n = (n - 31100) + 31100 := by omega
                                                rw [heq]
                                                exact le_w622 ⟨n - 31100, hr⟩
                                              · by_cases h23 : n < 31200
                                                · have hr : n - 31150 < 50 := by omega
                                                  have heq : n = (n - 31150) + 31150 := by omega
                                                  rw [heq]
                                                  exact le_w623 ⟨n - 31150, hr⟩
                                                · by_cases h24 : n < 31250
                                                  · have hr : n - 31200 < 50 := by omega
                                                    have heq : n = (n - 31200) + 31200 := by omega
                                                    rw [heq]
                                                    exact le_w624 ⟨n - 31200, hr⟩
                                                  · by_cases h25 : n < 31300
                                                    · have hr : n - 31250 < 50 := by omega
                                                      have heq : n = (n - 31250) + 31250 := by omega
                                                      rw [heq]
                                                      exact le_w625 ⟨n - 31250, hr⟩
                                                    · by_cases h26 : n < 31350
                                                      · have hr : n - 31300 < 50 := by omega
                                                        have heq : n = (n - 31300) + 31300 := by omega
                                                        rw [heq]
                                                        exact le_w626 ⟨n - 31300, hr⟩
                                                      · by_cases h27 : n < 31400
                                                        · have hr : n - 31350 < 50 := by omega
                                                          have heq : n = (n - 31350) + 31350 := by omega
                                                          rw [heq]
                                                          exact le_w627 ⟨n - 31350, hr⟩
                                                        · by_cases h28 : n < 31450
                                                          · have hr : n - 31400 < 50 := by omega
                                                            have heq : n = (n - 31400) + 31400 := by omega
                                                            rw [heq]
                                                            exact le_w628 ⟨n - 31400, hr⟩
                                                          · by_cases h29 : n < 31500
                                                            · have hr : n - 31450 < 50 := by omega
                                                              have heq : n = (n - 31450) + 31450 := by omega
                                                              rw [heq]
                                                              exact le_w629 ⟨n - 31450, hr⟩
                                                            · by_cases h30 : n < 31550
                                                              · have hr : n - 31500 < 50 := by omega
                                                                have heq : n = (n - 31500) + 31500 := by omega
                                                                rw [heq]
                                                                exact le_w630 ⟨n - 31500, hr⟩
                                                              · by_cases h31 : n < 31600
                                                                · have hr : n - 31550 < 50 := by omega
                                                                  have heq : n = (n - 31550) + 31550 := by omega
                                                                  rw [heq]
                                                                  exact le_w631 ⟨n - 31550, hr⟩
                                                                · by_cases h32 : n < 31650
                                                                  · have hr : n - 31600 < 50 := by omega
                                                                    have heq : n = (n - 31600) + 31600 := by omega
                                                                    rw [heq]
                                                                    exact le_w632 ⟨n - 31600, hr⟩
                                                                  · by_cases h33 : n < 31700
                                                                    · have hr : n - 31650 < 50 := by omega
                                                                      have heq : n = (n - 31650) + 31650 := by omega
                                                                      rw [heq]
                                                                      exact le_w633 ⟨n - 31650, hr⟩
                                                                    · by_cases h34 : n < 31750
                                                                      · have hr : n - 31700 < 50 := by omega
                                                                        have heq : n = (n - 31700) + 31700 := by omega
                                                                        rw [heq]
                                                                        exact le_w634 ⟨n - 31700, hr⟩
                                                                      · by_cases h35 : n < 31800
                                                                        · have hr : n - 31750 < 50 := by omega
                                                                          have heq : n = (n - 31750) + 31750 := by omega
                                                                          rw [heq]
                                                                          exact le_w635 ⟨n - 31750, hr⟩
                                                                        · by_cases h36 : n < 31850
                                                                          · have hr : n - 31800 < 50 := by omega
                                                                            have heq : n = (n - 31800) + 31800 := by omega
                                                                            rw [heq]
                                                                            exact le_w636 ⟨n - 31800, hr⟩
                                                                          · by_cases h37 : n < 31900
                                                                            · have hr : n - 31850 < 50 := by omega
                                                                              have heq : n = (n - 31850) + 31850 := by omega
                                                                              rw [heq]
                                                                              exact le_w637 ⟨n - 31850, hr⟩
                                                                            · by_cases h38 : n < 31950
                                                                              · have hr : n - 31900 < 50 := by omega
                                                                                have heq : n = (n - 31900) + 31900 := by omega
                                                                                rw [heq]
                                                                                exact le_w638 ⟨n - 31900, hr⟩
                                                                              · by_cases h39 : n < 32000
                                                                                · have hr : n - 31950 < 50 := by omega
                                                                                  have heq : n = (n - 31950) + 31950 := by omega
                                                                                  rw [heq]
                                                                                  exact le_w639 ⟨n - 31950, hr⟩
                                                                                · by_cases h40 : n < 32050
                                                                                  · have hr : n - 32000 < 50 := by omega
                                                                                    have heq : n = (n - 32000) + 32000 := by omega
                                                                                    rw [heq]
                                                                                    exact le_w640 ⟨n - 32000, hr⟩
                                                                                  · by_cases h41 : n < 32100
                                                                                    · have hr : n - 32050 < 50 := by omega
                                                                                      have heq : n = (n - 32050) + 32050 := by omega
                                                                                      rw [heq]
                                                                                      exact le_w641 ⟨n - 32050, hr⟩
                                                                                    · by_cases h42 : n < 32150
                                                                                      · have hr : n - 32100 < 50 := by omega
                                                                                        have heq : n = (n - 32100) + 32100 := by omega
                                                                                        rw [heq]
                                                                                        exact le_w642 ⟨n - 32100, hr⟩
                                                                                      · by_cases h43 : n < 32200
                                                                                        · have hr : n - 32150 < 50 := by omega
                                                                                          have heq : n = (n - 32150) + 32150 := by omega
                                                                                          rw [heq]
                                                                                          exact le_w643 ⟨n - 32150, hr⟩
                                                                                        · by_cases h44 : n < 32250
                                                                                          · have hr : n - 32200 < 50 := by omega
                                                                                            have heq : n = (n - 32200) + 32200 := by omega
                                                                                            rw [heq]
                                                                                            exact le_w644 ⟨n - 32200, hr⟩
                                                                                          · by_cases h45 : n < 32300
                                                                                            · have hr : n - 32250 < 50 := by omega
                                                                                              have heq : n = (n - 32250) + 32250 := by omega
                                                                                              rw [heq]
                                                                                              exact le_w645 ⟨n - 32250, hr⟩
                                                                                            · by_cases h46 : n < 32350
                                                                                              · have hr : n - 32300 < 50 := by omega
                                                                                                have heq : n = (n - 32300) + 32300 := by omega
                                                                                                rw [heq]
                                                                                                exact le_w646 ⟨n - 32300, hr⟩
                                                                                              · by_cases h47 : n < 32400
                                                                                                · have hr : n - 32350 < 50 := by omega
                                                                                                  have heq : n = (n - 32350) + 32350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact le_w647 ⟨n - 32350, hr⟩
                                                                                                · by_cases h48 : n < 32450
                                                                                                  · have hr : n - 32400 < 50 := by omega
                                                                                                    have heq : n = (n - 32400) + 32400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact le_w648 ⟨n - 32400, hr⟩
                                                                                                  · by_cases h49 : n < 32500
                                                                                                    · have hr : n - 32450 < 50 := by omega
                                                                                                      have heq : n = (n - 32450) + 32450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact le_w649 ⟨n - 32450, hr⟩
                                                                                                    · by_cases h50 : n < 32550
                                                                                                      · have hr : n - 32500 < 50 := by omega
                                                                                                        have heq : n = (n - 32500) + 32500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact le_w650 ⟨n - 32500, hr⟩
                                                                                                      · by_cases h51 : n < 32600
                                                                                                        · have hr : n - 32550 < 50 := by omega
                                                                                                          have heq : n = (n - 32550) + 32550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact le_w651 ⟨n - 32550, hr⟩
                                                                                                        · by_cases h52 : n < 32650
                                                                                                          · have hr : n - 32600 < 50 := by omega
                                                                                                            have heq : n = (n - 32600) + 32600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact le_w652 ⟨n - 32600, hr⟩
                                                                                                          · by_cases h53 : n < 32700
                                                                                                            · have hr : n - 32650 < 50 := by omega
                                                                                                              have heq : n = (n - 32650) + 32650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact le_w653 ⟨n - 32650, hr⟩
                                                                                                            · by_cases h54 : n < 32750
                                                                                                              · have hr : n - 32700 < 50 := by omega
                                                                                                                have heq : n = (n - 32700) + 32700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact le_w654 ⟨n - 32700, hr⟩
                                                                                                              · by_cases h55 : n < 32800
                                                                                                                · have hr : n - 32750 < 50 := by omega
                                                                                                                  have heq : n = (n - 32750) + 32750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact le_w655 ⟨n - 32750, hr⟩
                                                                                                                · by_cases h56 : n < 32850
                                                                                                                  · have hr : n - 32800 < 50 := by omega
                                                                                                                    have heq : n = (n - 32800) + 32800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact le_w656 ⟨n - 32800, hr⟩
                                                                                                                  · by_cases h57 : n < 32900
                                                                                                                    · have hr : n - 32850 < 50 := by omega
                                                                                                                      have heq : n = (n - 32850) + 32850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact le_w657 ⟨n - 32850, hr⟩
                                                                                                                    · by_cases h58 : n < 32950
                                                                                                                      · have hr : n - 32900 < 50 := by omega
                                                                                                                        have heq : n = (n - 32900) + 32900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact le_w658 ⟨n - 32900, hr⟩
                                                                                                                      · by_cases h59 : n < 33000
                                                                                                                        · have hr : n - 32950 < 50 := by omega
                                                                                                                          have heq : n = (n - 32950) + 32950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact le_w659 ⟨n - 32950, hr⟩
                                                                                                                        · by_cases h60 : n < 33050
                                                                                                                          · have hr : n - 33000 < 50 := by omega
                                                                                                                            have heq : n = (n - 33000) + 33000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact le_w660 ⟨n - 33000, hr⟩
                                                                                                                          · by_cases h61 : n < 33100
                                                                                                                            · have hr : n - 33050 < 50 := by omega
                                                                                                                              have heq : n = (n - 33050) + 33050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact le_w661 ⟨n - 33050, hr⟩
                                                                                                                            · by_cases h62 : n < 33150
                                                                                                                              · have hr : n - 33100 < 50 := by omega
                                                                                                                                have heq : n = (n - 33100) + 33100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact le_w662 ⟨n - 33100, hr⟩
                                                                                                                              · by_cases h63 : n < 33200
                                                                                                                                · have hr : n - 33150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 33150) + 33150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact le_w663 ⟨n - 33150, hr⟩
                                                                                                                                · by_cases h64 : n < 33250
                                                                                                                                  · have hr : n - 33200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 33200) + 33200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact le_w664 ⟨n - 33200, hr⟩
                                                                                                                                  · by_cases h65 : n < 33300
                                                                                                                                    · have hr : n - 33250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 33250) + 33250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact le_w665 ⟨n - 33250, hr⟩
                                                                                                                                    · by_cases h66 : n < 33350
                                                                                                                                      · have hr : n - 33300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 33300) + 33300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact le_w666 ⟨n - 33300, hr⟩
                                                                                                                                      · by_cases h67 : n < 33400
                                                                                                                                        · have hr : n - 33350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 33350) + 33350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact le_w667 ⟨n - 33350, hr⟩
                                                                                                                                        · by_cases h68 : n < 33450
                                                                                                                                          · have hr : n - 33400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 33400) + 33400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact le_w668 ⟨n - 33400, hr⟩
                                                                                                                                          · by_cases h69 : n < 33500
                                                                                                                                            · have hr : n - 33450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 33450) + 33450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact le_w669 ⟨n - 33450, hr⟩
                                                                                                                                            · by_cases h70 : n < 33550
                                                                                                                                              · have hr : n - 33500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 33500) + 33500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact le_w670 ⟨n - 33500, hr⟩
                                                                                                                                              · by_cases h71 : n < 33600
                                                                                                                                                · have hr : n - 33550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 33550) + 33550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact le_w671 ⟨n - 33550, hr⟩
                                                                                                                                                · by_cases h72 : n < 33650
                                                                                                                                                  · have hr : n - 33600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 33600) + 33600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact le_w672 ⟨n - 33600, hr⟩
                                                                                                                                                  · by_cases h73 : n < 33700
                                                                                                                                                    · have hr : n - 33650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 33650) + 33650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact le_w673 ⟨n - 33650, hr⟩
                                                                                                                                                    · by_cases h74 : n < 33750
                                                                                                                                                      · have hr : n - 33700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 33700) + 33700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact le_w674 ⟨n - 33700, hr⟩
                                                                                                                                                      · by_cases h75 : n < 33800
                                                                                                                                                        · have hr : n - 33750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 33750) + 33750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact le_w675 ⟨n - 33750, hr⟩
                                                                                                                                                        · by_cases h76 : n < 33850
                                                                                                                                                          · have hr : n - 33800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 33800) + 33800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact le_w676 ⟨n - 33800, hr⟩
                                                                                                                                                          · by_cases h77 : n < 33900
                                                                                                                                                            · have hr : n - 33850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 33850) + 33850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact le_w677 ⟨n - 33850, hr⟩
                                                                                                                                                            · by_cases h78 : n < 33950
                                                                                                                                                              · have hr : n - 33900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 33900) + 33900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact le_w678 ⟨n - 33900, hr⟩
                                                                                                                                                              · by_cases h79 : n < 34000
                                                                                                                                                                · have hr : n - 33950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 33950) + 33950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact le_w679 ⟨n - 33950, hr⟩
                                                                                                                                                                · by_cases h80 : n < 34050
                                                                                                                                                                  · have hr : n - 34000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 34000) + 34000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact le_w680 ⟨n - 34000, hr⟩
                                                                                                                                                                  · by_cases h81 : n < 34100
                                                                                                                                                                    · have hr : n - 34050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 34050) + 34050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact le_w681 ⟨n - 34050, hr⟩
                                                                                                                                                                    · by_cases h82 : n < 34150
                                                                                                                                                                      · have hr : n - 34100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 34100) + 34100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact le_w682 ⟨n - 34100, hr⟩
                                                                                                                                                                      · by_cases h83 : n < 34200
                                                                                                                                                                        · have hr : n - 34150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 34150) + 34150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact le_w683 ⟨n - 34150, hr⟩
                                                                                                                                                                        · by_cases h84 : n < 34250
                                                                                                                                                                          · have hr : n - 34200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 34200) + 34200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact le_w684 ⟨n - 34200, hr⟩
                                                                                                                                                                          · by_cases h85 : n < 34300
                                                                                                                                                                            · have hr : n - 34250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 34250) + 34250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact le_w685 ⟨n - 34250, hr⟩
                                                                                                                                                                            · by_cases h86 : n < 34350
                                                                                                                                                                              · have hr : n - 34300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 34300) + 34300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact le_w686 ⟨n - 34300, hr⟩
                                                                                                                                                                              · by_cases h87 : n < 34400
                                                                                                                                                                                · have hr : n - 34350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 34350) + 34350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact le_w687 ⟨n - 34350, hr⟩
                                                                                                                                                                                · by_cases h88 : n < 34450
                                                                                                                                                                                  · have hr : n - 34400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 34400) + 34400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact le_w688 ⟨n - 34400, hr⟩
                                                                                                                                                                                  · by_cases h89 : n < 34500
                                                                                                                                                                                    · have hr : n - 34450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 34450) + 34450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact le_w689 ⟨n - 34450, hr⟩
                                                                                                                                                                                    · by_cases h90 : n < 34550
                                                                                                                                                                                      · have hr : n - 34500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 34500) + 34500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact le_w690 ⟨n - 34500, hr⟩
                                                                                                                                                                                      · by_cases h91 : n < 34600
                                                                                                                                                                                        · have hr : n - 34550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 34550) + 34550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact le_w691 ⟨n - 34550, hr⟩
                                                                                                                                                                                        · by_cases h92 : n < 34650
                                                                                                                                                                                          · have hr : n - 34600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 34600) + 34600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact le_w692 ⟨n - 34600, hr⟩
                                                                                                                                                                                          · by_cases h93 : n < 34700
                                                                                                                                                                                            · have hr : n - 34650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 34650) + 34650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact le_w693 ⟨n - 34650, hr⟩
                                                                                                                                                                                            · by_cases h94 : n < 34750
                                                                                                                                                                                              · have hr : n - 34700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 34700) + 34700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact le_w694 ⟨n - 34700, hr⟩
                                                                                                                                                                                              · by_cases h95 : n < 34800
                                                                                                                                                                                                · have hr : n - 34750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 34750) + 34750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact le_w695 ⟨n - 34750, hr⟩
                                                                                                                                                                                                · by_cases h96 : n < 34850
                                                                                                                                                                                                  · have hr : n - 34800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 34800) + 34800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact le_w696 ⟨n - 34800, hr⟩
                                                                                                                                                                                                  · by_cases h97 : n < 34900
                                                                                                                                                                                                    · have hr : n - 34850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 34850) + 34850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact le_w697 ⟨n - 34850, hr⟩
                                                                                                                                                                                                    · by_cases h98 : n < 34950
                                                                                                                                                                                                      · have hr : n - 34900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 34900) + 34900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact le_w698 ⟨n - 34900, hr⟩
                                                                                                                                                                                                      · by_cases h99 : n < 35000
                                                                                                                                                                                                        · have hr : n - 34950 < 50 := by omega
                                                                                                                                                                                                          have heq : n = (n - 34950) + 34950 := by omega
                                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                                          exact le_w699 ⟨n - 34950, hr⟩
                                                                                                                                                                                                        · omega

theorem dimF_pos_range : ∀ n, 30000 ≤ n → n < 35000 → 0 < dimF n := by
  intro n hlo hhi
  by_cases h0 : n < 30050
  · have hr : n - 30000 < 50 := by omega
    have heq : n = (n - 30000) + 30000 := by omega
    rw [heq]
    exact pos_w600 ⟨n - 30000, hr⟩
  · by_cases h1 : n < 30100
    · have hr : n - 30050 < 50 := by omega
      have heq : n = (n - 30050) + 30050 := by omega
      rw [heq]
      exact pos_w601 ⟨n - 30050, hr⟩
    · by_cases h2 : n < 30150
      · have hr : n - 30100 < 50 := by omega
        have heq : n = (n - 30100) + 30100 := by omega
        rw [heq]
        exact pos_w602 ⟨n - 30100, hr⟩
      · by_cases h3 : n < 30200
        · have hr : n - 30150 < 50 := by omega
          have heq : n = (n - 30150) + 30150 := by omega
          rw [heq]
          exact pos_w603 ⟨n - 30150, hr⟩
        · by_cases h4 : n < 30250
          · have hr : n - 30200 < 50 := by omega
            have heq : n = (n - 30200) + 30200 := by omega
            rw [heq]
            exact pos_w604 ⟨n - 30200, hr⟩
          · by_cases h5 : n < 30300
            · have hr : n - 30250 < 50 := by omega
              have heq : n = (n - 30250) + 30250 := by omega
              rw [heq]
              exact pos_w605 ⟨n - 30250, hr⟩
            · by_cases h6 : n < 30350
              · have hr : n - 30300 < 50 := by omega
                have heq : n = (n - 30300) + 30300 := by omega
                rw [heq]
                exact pos_w606 ⟨n - 30300, hr⟩
              · by_cases h7 : n < 30400
                · have hr : n - 30350 < 50 := by omega
                  have heq : n = (n - 30350) + 30350 := by omega
                  rw [heq]
                  exact pos_w607 ⟨n - 30350, hr⟩
                · by_cases h8 : n < 30450
                  · have hr : n - 30400 < 50 := by omega
                    have heq : n = (n - 30400) + 30400 := by omega
                    rw [heq]
                    exact pos_w608 ⟨n - 30400, hr⟩
                  · by_cases h9 : n < 30500
                    · have hr : n - 30450 < 50 := by omega
                      have heq : n = (n - 30450) + 30450 := by omega
                      rw [heq]
                      exact pos_w609 ⟨n - 30450, hr⟩
                    · by_cases h10 : n < 30550
                      · have hr : n - 30500 < 50 := by omega
                        have heq : n = (n - 30500) + 30500 := by omega
                        rw [heq]
                        exact pos_w610 ⟨n - 30500, hr⟩
                      · by_cases h11 : n < 30600
                        · have hr : n - 30550 < 50 := by omega
                          have heq : n = (n - 30550) + 30550 := by omega
                          rw [heq]
                          exact pos_w611 ⟨n - 30550, hr⟩
                        · by_cases h12 : n < 30650
                          · have hr : n - 30600 < 50 := by omega
                            have heq : n = (n - 30600) + 30600 := by omega
                            rw [heq]
                            exact pos_w612 ⟨n - 30600, hr⟩
                          · by_cases h13 : n < 30700
                            · have hr : n - 30650 < 50 := by omega
                              have heq : n = (n - 30650) + 30650 := by omega
                              rw [heq]
                              exact pos_w613 ⟨n - 30650, hr⟩
                            · by_cases h14 : n < 30750
                              · have hr : n - 30700 < 50 := by omega
                                have heq : n = (n - 30700) + 30700 := by omega
                                rw [heq]
                                exact pos_w614 ⟨n - 30700, hr⟩
                              · by_cases h15 : n < 30800
                                · have hr : n - 30750 < 50 := by omega
                                  have heq : n = (n - 30750) + 30750 := by omega
                                  rw [heq]
                                  exact pos_w615 ⟨n - 30750, hr⟩
                                · by_cases h16 : n < 30850
                                  · have hr : n - 30800 < 50 := by omega
                                    have heq : n = (n - 30800) + 30800 := by omega
                                    rw [heq]
                                    exact pos_w616 ⟨n - 30800, hr⟩
                                  · by_cases h17 : n < 30900
                                    · have hr : n - 30850 < 50 := by omega
                                      have heq : n = (n - 30850) + 30850 := by omega
                                      rw [heq]
                                      exact pos_w617 ⟨n - 30850, hr⟩
                                    · by_cases h18 : n < 30950
                                      · have hr : n - 30900 < 50 := by omega
                                        have heq : n = (n - 30900) + 30900 := by omega
                                        rw [heq]
                                        exact pos_w618 ⟨n - 30900, hr⟩
                                      · by_cases h19 : n < 31000
                                        · have hr : n - 30950 < 50 := by omega
                                          have heq : n = (n - 30950) + 30950 := by omega
                                          rw [heq]
                                          exact pos_w619 ⟨n - 30950, hr⟩
                                        · by_cases h20 : n < 31050
                                          · have hr : n - 31000 < 50 := by omega
                                            have heq : n = (n - 31000) + 31000 := by omega
                                            rw [heq]
                                            exact pos_w620 ⟨n - 31000, hr⟩
                                          · by_cases h21 : n < 31100
                                            · have hr : n - 31050 < 50 := by omega
                                              have heq : n = (n - 31050) + 31050 := by omega
                                              rw [heq]
                                              exact pos_w621 ⟨n - 31050, hr⟩
                                            · by_cases h22 : n < 31150
                                              · have hr : n - 31100 < 50 := by omega
                                                have heq : n = (n - 31100) + 31100 := by omega
                                                rw [heq]
                                                exact pos_w622 ⟨n - 31100, hr⟩
                                              · by_cases h23 : n < 31200
                                                · have hr : n - 31150 < 50 := by omega
                                                  have heq : n = (n - 31150) + 31150 := by omega
                                                  rw [heq]
                                                  exact pos_w623 ⟨n - 31150, hr⟩
                                                · by_cases h24 : n < 31250
                                                  · have hr : n - 31200 < 50 := by omega
                                                    have heq : n = (n - 31200) + 31200 := by omega
                                                    rw [heq]
                                                    exact pos_w624 ⟨n - 31200, hr⟩
                                                  · by_cases h25 : n < 31300
                                                    · have hr : n - 31250 < 50 := by omega
                                                      have heq : n = (n - 31250) + 31250 := by omega
                                                      rw [heq]
                                                      exact pos_w625 ⟨n - 31250, hr⟩
                                                    · by_cases h26 : n < 31350
                                                      · have hr : n - 31300 < 50 := by omega
                                                        have heq : n = (n - 31300) + 31300 := by omega
                                                        rw [heq]
                                                        exact pos_w626 ⟨n - 31300, hr⟩
                                                      · by_cases h27 : n < 31400
                                                        · have hr : n - 31350 < 50 := by omega
                                                          have heq : n = (n - 31350) + 31350 := by omega
                                                          rw [heq]
                                                          exact pos_w627 ⟨n - 31350, hr⟩
                                                        · by_cases h28 : n < 31450
                                                          · have hr : n - 31400 < 50 := by omega
                                                            have heq : n = (n - 31400) + 31400 := by omega
                                                            rw [heq]
                                                            exact pos_w628 ⟨n - 31400, hr⟩
                                                          · by_cases h29 : n < 31500
                                                            · have hr : n - 31450 < 50 := by omega
                                                              have heq : n = (n - 31450) + 31450 := by omega
                                                              rw [heq]
                                                              exact pos_w629 ⟨n - 31450, hr⟩
                                                            · by_cases h30 : n < 31550
                                                              · have hr : n - 31500 < 50 := by omega
                                                                have heq : n = (n - 31500) + 31500 := by omega
                                                                rw [heq]
                                                                exact pos_w630 ⟨n - 31500, hr⟩
                                                              · by_cases h31 : n < 31600
                                                                · have hr : n - 31550 < 50 := by omega
                                                                  have heq : n = (n - 31550) + 31550 := by omega
                                                                  rw [heq]
                                                                  exact pos_w631 ⟨n - 31550, hr⟩
                                                                · by_cases h32 : n < 31650
                                                                  · have hr : n - 31600 < 50 := by omega
                                                                    have heq : n = (n - 31600) + 31600 := by omega
                                                                    rw [heq]
                                                                    exact pos_w632 ⟨n - 31600, hr⟩
                                                                  · by_cases h33 : n < 31700
                                                                    · have hr : n - 31650 < 50 := by omega
                                                                      have heq : n = (n - 31650) + 31650 := by omega
                                                                      rw [heq]
                                                                      exact pos_w633 ⟨n - 31650, hr⟩
                                                                    · by_cases h34 : n < 31750
                                                                      · have hr : n - 31700 < 50 := by omega
                                                                        have heq : n = (n - 31700) + 31700 := by omega
                                                                        rw [heq]
                                                                        exact pos_w634 ⟨n - 31700, hr⟩
                                                                      · by_cases h35 : n < 31800
                                                                        · have hr : n - 31750 < 50 := by omega
                                                                          have heq : n = (n - 31750) + 31750 := by omega
                                                                          rw [heq]
                                                                          exact pos_w635 ⟨n - 31750, hr⟩
                                                                        · by_cases h36 : n < 31850
                                                                          · have hr : n - 31800 < 50 := by omega
                                                                            have heq : n = (n - 31800) + 31800 := by omega
                                                                            rw [heq]
                                                                            exact pos_w636 ⟨n - 31800, hr⟩
                                                                          · by_cases h37 : n < 31900
                                                                            · have hr : n - 31850 < 50 := by omega
                                                                              have heq : n = (n - 31850) + 31850 := by omega
                                                                              rw [heq]
                                                                              exact pos_w637 ⟨n - 31850, hr⟩
                                                                            · by_cases h38 : n < 31950
                                                                              · have hr : n - 31900 < 50 := by omega
                                                                                have heq : n = (n - 31900) + 31900 := by omega
                                                                                rw [heq]
                                                                                exact pos_w638 ⟨n - 31900, hr⟩
                                                                              · by_cases h39 : n < 32000
                                                                                · have hr : n - 31950 < 50 := by omega
                                                                                  have heq : n = (n - 31950) + 31950 := by omega
                                                                                  rw [heq]
                                                                                  exact pos_w639 ⟨n - 31950, hr⟩
                                                                                · by_cases h40 : n < 32050
                                                                                  · have hr : n - 32000 < 50 := by omega
                                                                                    have heq : n = (n - 32000) + 32000 := by omega
                                                                                    rw [heq]
                                                                                    exact pos_w640 ⟨n - 32000, hr⟩
                                                                                  · by_cases h41 : n < 32100
                                                                                    · have hr : n - 32050 < 50 := by omega
                                                                                      have heq : n = (n - 32050) + 32050 := by omega
                                                                                      rw [heq]
                                                                                      exact pos_w641 ⟨n - 32050, hr⟩
                                                                                    · by_cases h42 : n < 32150
                                                                                      · have hr : n - 32100 < 50 := by omega
                                                                                        have heq : n = (n - 32100) + 32100 := by omega
                                                                                        rw [heq]
                                                                                        exact pos_w642 ⟨n - 32100, hr⟩
                                                                                      · by_cases h43 : n < 32200
                                                                                        · have hr : n - 32150 < 50 := by omega
                                                                                          have heq : n = (n - 32150) + 32150 := by omega
                                                                                          rw [heq]
                                                                                          exact pos_w643 ⟨n - 32150, hr⟩
                                                                                        · by_cases h44 : n < 32250
                                                                                          · have hr : n - 32200 < 50 := by omega
                                                                                            have heq : n = (n - 32200) + 32200 := by omega
                                                                                            rw [heq]
                                                                                            exact pos_w644 ⟨n - 32200, hr⟩
                                                                                          · by_cases h45 : n < 32300
                                                                                            · have hr : n - 32250 < 50 := by omega
                                                                                              have heq : n = (n - 32250) + 32250 := by omega
                                                                                              rw [heq]
                                                                                              exact pos_w645 ⟨n - 32250, hr⟩
                                                                                            · by_cases h46 : n < 32350
                                                                                              · have hr : n - 32300 < 50 := by omega
                                                                                                have heq : n = (n - 32300) + 32300 := by omega
                                                                                                rw [heq]
                                                                                                exact pos_w646 ⟨n - 32300, hr⟩
                                                                                              · by_cases h47 : n < 32400
                                                                                                · have hr : n - 32350 < 50 := by omega
                                                                                                  have heq : n = (n - 32350) + 32350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact pos_w647 ⟨n - 32350, hr⟩
                                                                                                · by_cases h48 : n < 32450
                                                                                                  · have hr : n - 32400 < 50 := by omega
                                                                                                    have heq : n = (n - 32400) + 32400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact pos_w648 ⟨n - 32400, hr⟩
                                                                                                  · by_cases h49 : n < 32500
                                                                                                    · have hr : n - 32450 < 50 := by omega
                                                                                                      have heq : n = (n - 32450) + 32450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact pos_w649 ⟨n - 32450, hr⟩
                                                                                                    · by_cases h50 : n < 32550
                                                                                                      · have hr : n - 32500 < 50 := by omega
                                                                                                        have heq : n = (n - 32500) + 32500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact pos_w650 ⟨n - 32500, hr⟩
                                                                                                      · by_cases h51 : n < 32600
                                                                                                        · have hr : n - 32550 < 50 := by omega
                                                                                                          have heq : n = (n - 32550) + 32550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact pos_w651 ⟨n - 32550, hr⟩
                                                                                                        · by_cases h52 : n < 32650
                                                                                                          · have hr : n - 32600 < 50 := by omega
                                                                                                            have heq : n = (n - 32600) + 32600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact pos_w652 ⟨n - 32600, hr⟩
                                                                                                          · by_cases h53 : n < 32700
                                                                                                            · have hr : n - 32650 < 50 := by omega
                                                                                                              have heq : n = (n - 32650) + 32650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact pos_w653 ⟨n - 32650, hr⟩
                                                                                                            · by_cases h54 : n < 32750
                                                                                                              · have hr : n - 32700 < 50 := by omega
                                                                                                                have heq : n = (n - 32700) + 32700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact pos_w654 ⟨n - 32700, hr⟩
                                                                                                              · by_cases h55 : n < 32800
                                                                                                                · have hr : n - 32750 < 50 := by omega
                                                                                                                  have heq : n = (n - 32750) + 32750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact pos_w655 ⟨n - 32750, hr⟩
                                                                                                                · by_cases h56 : n < 32850
                                                                                                                  · have hr : n - 32800 < 50 := by omega
                                                                                                                    have heq : n = (n - 32800) + 32800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact pos_w656 ⟨n - 32800, hr⟩
                                                                                                                  · by_cases h57 : n < 32900
                                                                                                                    · have hr : n - 32850 < 50 := by omega
                                                                                                                      have heq : n = (n - 32850) + 32850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact pos_w657 ⟨n - 32850, hr⟩
                                                                                                                    · by_cases h58 : n < 32950
                                                                                                                      · have hr : n - 32900 < 50 := by omega
                                                                                                                        have heq : n = (n - 32900) + 32900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact pos_w658 ⟨n - 32900, hr⟩
                                                                                                                      · by_cases h59 : n < 33000
                                                                                                                        · have hr : n - 32950 < 50 := by omega
                                                                                                                          have heq : n = (n - 32950) + 32950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact pos_w659 ⟨n - 32950, hr⟩
                                                                                                                        · by_cases h60 : n < 33050
                                                                                                                          · have hr : n - 33000 < 50 := by omega
                                                                                                                            have heq : n = (n - 33000) + 33000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact pos_w660 ⟨n - 33000, hr⟩
                                                                                                                          · by_cases h61 : n < 33100
                                                                                                                            · have hr : n - 33050 < 50 := by omega
                                                                                                                              have heq : n = (n - 33050) + 33050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact pos_w661 ⟨n - 33050, hr⟩
                                                                                                                            · by_cases h62 : n < 33150
                                                                                                                              · have hr : n - 33100 < 50 := by omega
                                                                                                                                have heq : n = (n - 33100) + 33100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact pos_w662 ⟨n - 33100, hr⟩
                                                                                                                              · by_cases h63 : n < 33200
                                                                                                                                · have hr : n - 33150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 33150) + 33150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact pos_w663 ⟨n - 33150, hr⟩
                                                                                                                                · by_cases h64 : n < 33250
                                                                                                                                  · have hr : n - 33200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 33200) + 33200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact pos_w664 ⟨n - 33200, hr⟩
                                                                                                                                  · by_cases h65 : n < 33300
                                                                                                                                    · have hr : n - 33250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 33250) + 33250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact pos_w665 ⟨n - 33250, hr⟩
                                                                                                                                    · by_cases h66 : n < 33350
                                                                                                                                      · have hr : n - 33300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 33300) + 33300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact pos_w666 ⟨n - 33300, hr⟩
                                                                                                                                      · by_cases h67 : n < 33400
                                                                                                                                        · have hr : n - 33350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 33350) + 33350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact pos_w667 ⟨n - 33350, hr⟩
                                                                                                                                        · by_cases h68 : n < 33450
                                                                                                                                          · have hr : n - 33400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 33400) + 33400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact pos_w668 ⟨n - 33400, hr⟩
                                                                                                                                          · by_cases h69 : n < 33500
                                                                                                                                            · have hr : n - 33450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 33450) + 33450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact pos_w669 ⟨n - 33450, hr⟩
                                                                                                                                            · by_cases h70 : n < 33550
                                                                                                                                              · have hr : n - 33500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 33500) + 33500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact pos_w670 ⟨n - 33500, hr⟩
                                                                                                                                              · by_cases h71 : n < 33600
                                                                                                                                                · have hr : n - 33550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 33550) + 33550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact pos_w671 ⟨n - 33550, hr⟩
                                                                                                                                                · by_cases h72 : n < 33650
                                                                                                                                                  · have hr : n - 33600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 33600) + 33600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact pos_w672 ⟨n - 33600, hr⟩
                                                                                                                                                  · by_cases h73 : n < 33700
                                                                                                                                                    · have hr : n - 33650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 33650) + 33650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact pos_w673 ⟨n - 33650, hr⟩
                                                                                                                                                    · by_cases h74 : n < 33750
                                                                                                                                                      · have hr : n - 33700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 33700) + 33700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact pos_w674 ⟨n - 33700, hr⟩
                                                                                                                                                      · by_cases h75 : n < 33800
                                                                                                                                                        · have hr : n - 33750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 33750) + 33750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact pos_w675 ⟨n - 33750, hr⟩
                                                                                                                                                        · by_cases h76 : n < 33850
                                                                                                                                                          · have hr : n - 33800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 33800) + 33800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact pos_w676 ⟨n - 33800, hr⟩
                                                                                                                                                          · by_cases h77 : n < 33900
                                                                                                                                                            · have hr : n - 33850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 33850) + 33850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact pos_w677 ⟨n - 33850, hr⟩
                                                                                                                                                            · by_cases h78 : n < 33950
                                                                                                                                                              · have hr : n - 33900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 33900) + 33900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact pos_w678 ⟨n - 33900, hr⟩
                                                                                                                                                              · by_cases h79 : n < 34000
                                                                                                                                                                · have hr : n - 33950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 33950) + 33950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact pos_w679 ⟨n - 33950, hr⟩
                                                                                                                                                                · by_cases h80 : n < 34050
                                                                                                                                                                  · have hr : n - 34000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 34000) + 34000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact pos_w680 ⟨n - 34000, hr⟩
                                                                                                                                                                  · by_cases h81 : n < 34100
                                                                                                                                                                    · have hr : n - 34050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 34050) + 34050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact pos_w681 ⟨n - 34050, hr⟩
                                                                                                                                                                    · by_cases h82 : n < 34150
                                                                                                                                                                      · have hr : n - 34100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 34100) + 34100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact pos_w682 ⟨n - 34100, hr⟩
                                                                                                                                                                      · by_cases h83 : n < 34200
                                                                                                                                                                        · have hr : n - 34150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 34150) + 34150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact pos_w683 ⟨n - 34150, hr⟩
                                                                                                                                                                        · by_cases h84 : n < 34250
                                                                                                                                                                          · have hr : n - 34200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 34200) + 34200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact pos_w684 ⟨n - 34200, hr⟩
                                                                                                                                                                          · by_cases h85 : n < 34300
                                                                                                                                                                            · have hr : n - 34250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 34250) + 34250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact pos_w685 ⟨n - 34250, hr⟩
                                                                                                                                                                            · by_cases h86 : n < 34350
                                                                                                                                                                              · have hr : n - 34300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 34300) + 34300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact pos_w686 ⟨n - 34300, hr⟩
                                                                                                                                                                              · by_cases h87 : n < 34400
                                                                                                                                                                                · have hr : n - 34350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 34350) + 34350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact pos_w687 ⟨n - 34350, hr⟩
                                                                                                                                                                                · by_cases h88 : n < 34450
                                                                                                                                                                                  · have hr : n - 34400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 34400) + 34400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact pos_w688 ⟨n - 34400, hr⟩
                                                                                                                                                                                  · by_cases h89 : n < 34500
                                                                                                                                                                                    · have hr : n - 34450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 34450) + 34450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact pos_w689 ⟨n - 34450, hr⟩
                                                                                                                                                                                    · by_cases h90 : n < 34550
                                                                                                                                                                                      · have hr : n - 34500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 34500) + 34500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact pos_w690 ⟨n - 34500, hr⟩
                                                                                                                                                                                      · by_cases h91 : n < 34600
                                                                                                                                                                                        · have hr : n - 34550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 34550) + 34550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact pos_w691 ⟨n - 34550, hr⟩
                                                                                                                                                                                        · by_cases h92 : n < 34650
                                                                                                                                                                                          · have hr : n - 34600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 34600) + 34600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact pos_w692 ⟨n - 34600, hr⟩
                                                                                                                                                                                          · by_cases h93 : n < 34700
                                                                                                                                                                                            · have hr : n - 34650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 34650) + 34650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact pos_w693 ⟨n - 34650, hr⟩
                                                                                                                                                                                            · by_cases h94 : n < 34750
                                                                                                                                                                                              · have hr : n - 34700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 34700) + 34700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact pos_w694 ⟨n - 34700, hr⟩
                                                                                                                                                                                              · by_cases h95 : n < 34800
                                                                                                                                                                                                · have hr : n - 34750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 34750) + 34750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact pos_w695 ⟨n - 34750, hr⟩
                                                                                                                                                                                                · by_cases h96 : n < 34850
                                                                                                                                                                                                  · have hr : n - 34800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 34800) + 34800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact pos_w696 ⟨n - 34800, hr⟩
                                                                                                                                                                                                  · by_cases h97 : n < 34900
                                                                                                                                                                                                    · have hr : n - 34850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 34850) + 34850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact pos_w697 ⟨n - 34850, hr⟩
                                                                                                                                                                                                    · by_cases h98 : n < 34950
                                                                                                                                                                                                      · have hr : n - 34900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 34900) + 34900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact pos_w698 ⟨n - 34900, hr⟩
                                                                                                                                                                                                      · by_cases h99 : n < 35000
                                                                                                                                                                                                        · have hr : n - 34950 < 50 := by omega
                                                                                                                                                                                                          have heq : n = (n - 34950) + 34950 := by omega
                                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                                          exact pos_w699 ⟨n - 34950, hr⟩
                                                                                                                                                                                                        · omega

end IntMul.Kappa.R8.Bit.Oppbank.DimBound6


