-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound7
-- name    : IntMul_Kappa_R8_Data_BitOppbankDimBound7
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:02:34.6504+00:00
-- url     : https://prove2.me/theorems/24160fc9-78c9-4c49-b9ae-bb1b01d62bd6
-- title:
--   Densified dimF $\le 22$ pack 7 ($[35000,40000)$)
-- statement:
--   Pack 7 of the densified dimension-field bound.
--
--   For every densified node index $n$ with $35000\le n<40000$, the 5-bit field $\mathrm{dimF}(n)$ extracted from $\mathrm{DIMT}$ satisfies
--   $$1\le \mathrm{dimF}(n)\le 22.$$
--   Proved by `decide` on successive `Fin 50` windows (no `native_decide`).
-- source:
--   R8 BitNB densified DIMT field bound; Fin-window decide packs

-- DimBound pack 7: dimF bounds on n ∈ [35000, 40000)

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

namespace IntMul.Kappa.R8.Bit.Oppbank.DimBound7

private theorem le_w700 : ∀ n : Fin 50, dimF (n.val + 35000) ≤ 22 := by decide
private theorem pos_w700 : ∀ n : Fin 50, 0 < dimF (n.val + 35000) := by decide
private theorem le_w701 : ∀ n : Fin 50, dimF (n.val + 35050) ≤ 22 := by decide
private theorem pos_w701 : ∀ n : Fin 50, 0 < dimF (n.val + 35050) := by decide
private theorem le_w702 : ∀ n : Fin 50, dimF (n.val + 35100) ≤ 22 := by decide
private theorem pos_w702 : ∀ n : Fin 50, 0 < dimF (n.val + 35100) := by decide
private theorem le_w703 : ∀ n : Fin 50, dimF (n.val + 35150) ≤ 22 := by decide
private theorem pos_w703 : ∀ n : Fin 50, 0 < dimF (n.val + 35150) := by decide
private theorem le_w704 : ∀ n : Fin 50, dimF (n.val + 35200) ≤ 22 := by decide
private theorem pos_w704 : ∀ n : Fin 50, 0 < dimF (n.val + 35200) := by decide
private theorem le_w705 : ∀ n : Fin 50, dimF (n.val + 35250) ≤ 22 := by decide
private theorem pos_w705 : ∀ n : Fin 50, 0 < dimF (n.val + 35250) := by decide
private theorem le_w706 : ∀ n : Fin 50, dimF (n.val + 35300) ≤ 22 := by decide
private theorem pos_w706 : ∀ n : Fin 50, 0 < dimF (n.val + 35300) := by decide
private theorem le_w707 : ∀ n : Fin 50, dimF (n.val + 35350) ≤ 22 := by decide
private theorem pos_w707 : ∀ n : Fin 50, 0 < dimF (n.val + 35350) := by decide
private theorem le_w708 : ∀ n : Fin 50, dimF (n.val + 35400) ≤ 22 := by decide
private theorem pos_w708 : ∀ n : Fin 50, 0 < dimF (n.val + 35400) := by decide
private theorem le_w709 : ∀ n : Fin 50, dimF (n.val + 35450) ≤ 22 := by decide
private theorem pos_w709 : ∀ n : Fin 50, 0 < dimF (n.val + 35450) := by decide
private theorem le_w710 : ∀ n : Fin 50, dimF (n.val + 35500) ≤ 22 := by decide
private theorem pos_w710 : ∀ n : Fin 50, 0 < dimF (n.val + 35500) := by decide
private theorem le_w711 : ∀ n : Fin 50, dimF (n.val + 35550) ≤ 22 := by decide
private theorem pos_w711 : ∀ n : Fin 50, 0 < dimF (n.val + 35550) := by decide
private theorem le_w712 : ∀ n : Fin 50, dimF (n.val + 35600) ≤ 22 := by decide
private theorem pos_w712 : ∀ n : Fin 50, 0 < dimF (n.val + 35600) := by decide
private theorem le_w713 : ∀ n : Fin 50, dimF (n.val + 35650) ≤ 22 := by decide
private theorem pos_w713 : ∀ n : Fin 50, 0 < dimF (n.val + 35650) := by decide
private theorem le_w714 : ∀ n : Fin 50, dimF (n.val + 35700) ≤ 22 := by decide
private theorem pos_w714 : ∀ n : Fin 50, 0 < dimF (n.val + 35700) := by decide
private theorem le_w715 : ∀ n : Fin 50, dimF (n.val + 35750) ≤ 22 := by decide
private theorem pos_w715 : ∀ n : Fin 50, 0 < dimF (n.val + 35750) := by decide
private theorem le_w716 : ∀ n : Fin 50, dimF (n.val + 35800) ≤ 22 := by decide
private theorem pos_w716 : ∀ n : Fin 50, 0 < dimF (n.val + 35800) := by decide
private theorem le_w717 : ∀ n : Fin 50, dimF (n.val + 35850) ≤ 22 := by decide
private theorem pos_w717 : ∀ n : Fin 50, 0 < dimF (n.val + 35850) := by decide
private theorem le_w718 : ∀ n : Fin 50, dimF (n.val + 35900) ≤ 22 := by decide
private theorem pos_w718 : ∀ n : Fin 50, 0 < dimF (n.val + 35900) := by decide
private theorem le_w719 : ∀ n : Fin 50, dimF (n.val + 35950) ≤ 22 := by decide
private theorem pos_w719 : ∀ n : Fin 50, 0 < dimF (n.val + 35950) := by decide
private theorem le_w720 : ∀ n : Fin 50, dimF (n.val + 36000) ≤ 22 := by decide
private theorem pos_w720 : ∀ n : Fin 50, 0 < dimF (n.val + 36000) := by decide
private theorem le_w721 : ∀ n : Fin 50, dimF (n.val + 36050) ≤ 22 := by decide
private theorem pos_w721 : ∀ n : Fin 50, 0 < dimF (n.val + 36050) := by decide
private theorem le_w722 : ∀ n : Fin 50, dimF (n.val + 36100) ≤ 22 := by decide
private theorem pos_w722 : ∀ n : Fin 50, 0 < dimF (n.val + 36100) := by decide
private theorem le_w723 : ∀ n : Fin 50, dimF (n.val + 36150) ≤ 22 := by decide
private theorem pos_w723 : ∀ n : Fin 50, 0 < dimF (n.val + 36150) := by decide
private theorem le_w724 : ∀ n : Fin 50, dimF (n.val + 36200) ≤ 22 := by decide
private theorem pos_w724 : ∀ n : Fin 50, 0 < dimF (n.val + 36200) := by decide
private theorem le_w725 : ∀ n : Fin 50, dimF (n.val + 36250) ≤ 22 := by decide
private theorem pos_w725 : ∀ n : Fin 50, 0 < dimF (n.val + 36250) := by decide
private theorem le_w726 : ∀ n : Fin 50, dimF (n.val + 36300) ≤ 22 := by decide
private theorem pos_w726 : ∀ n : Fin 50, 0 < dimF (n.val + 36300) := by decide
private theorem le_w727 : ∀ n : Fin 50, dimF (n.val + 36350) ≤ 22 := by decide
private theorem pos_w727 : ∀ n : Fin 50, 0 < dimF (n.val + 36350) := by decide
private theorem le_w728 : ∀ n : Fin 50, dimF (n.val + 36400) ≤ 22 := by decide
private theorem pos_w728 : ∀ n : Fin 50, 0 < dimF (n.val + 36400) := by decide
private theorem le_w729 : ∀ n : Fin 50, dimF (n.val + 36450) ≤ 22 := by decide
private theorem pos_w729 : ∀ n : Fin 50, 0 < dimF (n.val + 36450) := by decide
private theorem le_w730 : ∀ n : Fin 50, dimF (n.val + 36500) ≤ 22 := by decide
private theorem pos_w730 : ∀ n : Fin 50, 0 < dimF (n.val + 36500) := by decide
private theorem le_w731 : ∀ n : Fin 50, dimF (n.val + 36550) ≤ 22 := by decide
private theorem pos_w731 : ∀ n : Fin 50, 0 < dimF (n.val + 36550) := by decide
private theorem le_w732 : ∀ n : Fin 50, dimF (n.val + 36600) ≤ 22 := by decide
private theorem pos_w732 : ∀ n : Fin 50, 0 < dimF (n.val + 36600) := by decide
private theorem le_w733 : ∀ n : Fin 50, dimF (n.val + 36650) ≤ 22 := by decide
private theorem pos_w733 : ∀ n : Fin 50, 0 < dimF (n.val + 36650) := by decide
private theorem le_w734 : ∀ n : Fin 50, dimF (n.val + 36700) ≤ 22 := by decide
private theorem pos_w734 : ∀ n : Fin 50, 0 < dimF (n.val + 36700) := by decide
private theorem le_w735 : ∀ n : Fin 50, dimF (n.val + 36750) ≤ 22 := by decide
private theorem pos_w735 : ∀ n : Fin 50, 0 < dimF (n.val + 36750) := by decide
private theorem le_w736 : ∀ n : Fin 50, dimF (n.val + 36800) ≤ 22 := by decide
private theorem pos_w736 : ∀ n : Fin 50, 0 < dimF (n.val + 36800) := by decide
private theorem le_w737 : ∀ n : Fin 50, dimF (n.val + 36850) ≤ 22 := by decide
private theorem pos_w737 : ∀ n : Fin 50, 0 < dimF (n.val + 36850) := by decide
private theorem le_w738 : ∀ n : Fin 50, dimF (n.val + 36900) ≤ 22 := by decide
private theorem pos_w738 : ∀ n : Fin 50, 0 < dimF (n.val + 36900) := by decide
private theorem le_w739 : ∀ n : Fin 50, dimF (n.val + 36950) ≤ 22 := by decide
private theorem pos_w739 : ∀ n : Fin 50, 0 < dimF (n.val + 36950) := by decide
private theorem le_w740 : ∀ n : Fin 50, dimF (n.val + 37000) ≤ 22 := by decide
private theorem pos_w740 : ∀ n : Fin 50, 0 < dimF (n.val + 37000) := by decide
private theorem le_w741 : ∀ n : Fin 50, dimF (n.val + 37050) ≤ 22 := by decide
private theorem pos_w741 : ∀ n : Fin 50, 0 < dimF (n.val + 37050) := by decide
private theorem le_w742 : ∀ n : Fin 50, dimF (n.val + 37100) ≤ 22 := by decide
private theorem pos_w742 : ∀ n : Fin 50, 0 < dimF (n.val + 37100) := by decide
private theorem le_w743 : ∀ n : Fin 50, dimF (n.val + 37150) ≤ 22 := by decide
private theorem pos_w743 : ∀ n : Fin 50, 0 < dimF (n.val + 37150) := by decide
private theorem le_w744 : ∀ n : Fin 50, dimF (n.val + 37200) ≤ 22 := by decide
private theorem pos_w744 : ∀ n : Fin 50, 0 < dimF (n.val + 37200) := by decide
private theorem le_w745 : ∀ n : Fin 50, dimF (n.val + 37250) ≤ 22 := by decide
private theorem pos_w745 : ∀ n : Fin 50, 0 < dimF (n.val + 37250) := by decide
private theorem le_w746 : ∀ n : Fin 50, dimF (n.val + 37300) ≤ 22 := by decide
private theorem pos_w746 : ∀ n : Fin 50, 0 < dimF (n.val + 37300) := by decide
private theorem le_w747 : ∀ n : Fin 50, dimF (n.val + 37350) ≤ 22 := by decide
private theorem pos_w747 : ∀ n : Fin 50, 0 < dimF (n.val + 37350) := by decide
private theorem le_w748 : ∀ n : Fin 50, dimF (n.val + 37400) ≤ 22 := by decide
private theorem pos_w748 : ∀ n : Fin 50, 0 < dimF (n.val + 37400) := by decide
private theorem le_w749 : ∀ n : Fin 50, dimF (n.val + 37450) ≤ 22 := by decide
private theorem pos_w749 : ∀ n : Fin 50, 0 < dimF (n.val + 37450) := by decide
private theorem le_w750 : ∀ n : Fin 50, dimF (n.val + 37500) ≤ 22 := by decide
private theorem pos_w750 : ∀ n : Fin 50, 0 < dimF (n.val + 37500) := by decide
private theorem le_w751 : ∀ n : Fin 50, dimF (n.val + 37550) ≤ 22 := by decide
private theorem pos_w751 : ∀ n : Fin 50, 0 < dimF (n.val + 37550) := by decide
private theorem le_w752 : ∀ n : Fin 50, dimF (n.val + 37600) ≤ 22 := by decide
private theorem pos_w752 : ∀ n : Fin 50, 0 < dimF (n.val + 37600) := by decide
private theorem le_w753 : ∀ n : Fin 50, dimF (n.val + 37650) ≤ 22 := by decide
private theorem pos_w753 : ∀ n : Fin 50, 0 < dimF (n.val + 37650) := by decide
private theorem le_w754 : ∀ n : Fin 50, dimF (n.val + 37700) ≤ 22 := by decide
private theorem pos_w754 : ∀ n : Fin 50, 0 < dimF (n.val + 37700) := by decide
private theorem le_w755 : ∀ n : Fin 50, dimF (n.val + 37750) ≤ 22 := by decide
private theorem pos_w755 : ∀ n : Fin 50, 0 < dimF (n.val + 37750) := by decide
private theorem le_w756 : ∀ n : Fin 50, dimF (n.val + 37800) ≤ 22 := by decide
private theorem pos_w756 : ∀ n : Fin 50, 0 < dimF (n.val + 37800) := by decide
private theorem le_w757 : ∀ n : Fin 50, dimF (n.val + 37850) ≤ 22 := by decide
private theorem pos_w757 : ∀ n : Fin 50, 0 < dimF (n.val + 37850) := by decide
private theorem le_w758 : ∀ n : Fin 50, dimF (n.val + 37900) ≤ 22 := by decide
private theorem pos_w758 : ∀ n : Fin 50, 0 < dimF (n.val + 37900) := by decide
private theorem le_w759 : ∀ n : Fin 50, dimF (n.val + 37950) ≤ 22 := by decide
private theorem pos_w759 : ∀ n : Fin 50, 0 < dimF (n.val + 37950) := by decide
private theorem le_w760 : ∀ n : Fin 50, dimF (n.val + 38000) ≤ 22 := by decide
private theorem pos_w760 : ∀ n : Fin 50, 0 < dimF (n.val + 38000) := by decide
private theorem le_w761 : ∀ n : Fin 50, dimF (n.val + 38050) ≤ 22 := by decide
private theorem pos_w761 : ∀ n : Fin 50, 0 < dimF (n.val + 38050) := by decide
private theorem le_w762 : ∀ n : Fin 50, dimF (n.val + 38100) ≤ 22 := by decide
private theorem pos_w762 : ∀ n : Fin 50, 0 < dimF (n.val + 38100) := by decide
private theorem le_w763 : ∀ n : Fin 50, dimF (n.val + 38150) ≤ 22 := by decide
private theorem pos_w763 : ∀ n : Fin 50, 0 < dimF (n.val + 38150) := by decide
private theorem le_w764 : ∀ n : Fin 50, dimF (n.val + 38200) ≤ 22 := by decide
private theorem pos_w764 : ∀ n : Fin 50, 0 < dimF (n.val + 38200) := by decide
private theorem le_w765 : ∀ n : Fin 50, dimF (n.val + 38250) ≤ 22 := by decide
private theorem pos_w765 : ∀ n : Fin 50, 0 < dimF (n.val + 38250) := by decide
private theorem le_w766 : ∀ n : Fin 50, dimF (n.val + 38300) ≤ 22 := by decide
private theorem pos_w766 : ∀ n : Fin 50, 0 < dimF (n.val + 38300) := by decide
private theorem le_w767 : ∀ n : Fin 50, dimF (n.val + 38350) ≤ 22 := by decide
private theorem pos_w767 : ∀ n : Fin 50, 0 < dimF (n.val + 38350) := by decide
private theorem le_w768 : ∀ n : Fin 50, dimF (n.val + 38400) ≤ 22 := by decide
private theorem pos_w768 : ∀ n : Fin 50, 0 < dimF (n.val + 38400) := by decide
private theorem le_w769 : ∀ n : Fin 50, dimF (n.val + 38450) ≤ 22 := by decide
private theorem pos_w769 : ∀ n : Fin 50, 0 < dimF (n.val + 38450) := by decide
private theorem le_w770 : ∀ n : Fin 50, dimF (n.val + 38500) ≤ 22 := by decide
private theorem pos_w770 : ∀ n : Fin 50, 0 < dimF (n.val + 38500) := by decide
private theorem le_w771 : ∀ n : Fin 50, dimF (n.val + 38550) ≤ 22 := by decide
private theorem pos_w771 : ∀ n : Fin 50, 0 < dimF (n.val + 38550) := by decide
private theorem le_w772 : ∀ n : Fin 50, dimF (n.val + 38600) ≤ 22 := by decide
private theorem pos_w772 : ∀ n : Fin 50, 0 < dimF (n.val + 38600) := by decide
private theorem le_w773 : ∀ n : Fin 50, dimF (n.val + 38650) ≤ 22 := by decide
private theorem pos_w773 : ∀ n : Fin 50, 0 < dimF (n.val + 38650) := by decide
private theorem le_w774 : ∀ n : Fin 50, dimF (n.val + 38700) ≤ 22 := by decide
private theorem pos_w774 : ∀ n : Fin 50, 0 < dimF (n.val + 38700) := by decide
private theorem le_w775 : ∀ n : Fin 50, dimF (n.val + 38750) ≤ 22 := by decide
private theorem pos_w775 : ∀ n : Fin 50, 0 < dimF (n.val + 38750) := by decide
private theorem le_w776 : ∀ n : Fin 50, dimF (n.val + 38800) ≤ 22 := by decide
private theorem pos_w776 : ∀ n : Fin 50, 0 < dimF (n.val + 38800) := by decide
private theorem le_w777 : ∀ n : Fin 50, dimF (n.val + 38850) ≤ 22 := by decide
private theorem pos_w777 : ∀ n : Fin 50, 0 < dimF (n.val + 38850) := by decide
private theorem le_w778 : ∀ n : Fin 50, dimF (n.val + 38900) ≤ 22 := by decide
private theorem pos_w778 : ∀ n : Fin 50, 0 < dimF (n.val + 38900) := by decide
private theorem le_w779 : ∀ n : Fin 50, dimF (n.val + 38950) ≤ 22 := by decide
private theorem pos_w779 : ∀ n : Fin 50, 0 < dimF (n.val + 38950) := by decide
private theorem le_w780 : ∀ n : Fin 50, dimF (n.val + 39000) ≤ 22 := by decide
private theorem pos_w780 : ∀ n : Fin 50, 0 < dimF (n.val + 39000) := by decide
private theorem le_w781 : ∀ n : Fin 50, dimF (n.val + 39050) ≤ 22 := by decide
private theorem pos_w781 : ∀ n : Fin 50, 0 < dimF (n.val + 39050) := by decide
private theorem le_w782 : ∀ n : Fin 50, dimF (n.val + 39100) ≤ 22 := by decide
private theorem pos_w782 : ∀ n : Fin 50, 0 < dimF (n.val + 39100) := by decide
private theorem le_w783 : ∀ n : Fin 50, dimF (n.val + 39150) ≤ 22 := by decide
private theorem pos_w783 : ∀ n : Fin 50, 0 < dimF (n.val + 39150) := by decide
private theorem le_w784 : ∀ n : Fin 50, dimF (n.val + 39200) ≤ 22 := by decide
private theorem pos_w784 : ∀ n : Fin 50, 0 < dimF (n.val + 39200) := by decide
private theorem le_w785 : ∀ n : Fin 50, dimF (n.val + 39250) ≤ 22 := by decide
private theorem pos_w785 : ∀ n : Fin 50, 0 < dimF (n.val + 39250) := by decide
private theorem le_w786 : ∀ n : Fin 50, dimF (n.val + 39300) ≤ 22 := by decide
private theorem pos_w786 : ∀ n : Fin 50, 0 < dimF (n.val + 39300) := by decide
private theorem le_w787 : ∀ n : Fin 50, dimF (n.val + 39350) ≤ 22 := by decide
private theorem pos_w787 : ∀ n : Fin 50, 0 < dimF (n.val + 39350) := by decide
private theorem le_w788 : ∀ n : Fin 50, dimF (n.val + 39400) ≤ 22 := by decide
private theorem pos_w788 : ∀ n : Fin 50, 0 < dimF (n.val + 39400) := by decide
private theorem le_w789 : ∀ n : Fin 50, dimF (n.val + 39450) ≤ 22 := by decide
private theorem pos_w789 : ∀ n : Fin 50, 0 < dimF (n.val + 39450) := by decide
private theorem le_w790 : ∀ n : Fin 50, dimF (n.val + 39500) ≤ 22 := by decide
private theorem pos_w790 : ∀ n : Fin 50, 0 < dimF (n.val + 39500) := by decide
private theorem le_w791 : ∀ n : Fin 50, dimF (n.val + 39550) ≤ 22 := by decide
private theorem pos_w791 : ∀ n : Fin 50, 0 < dimF (n.val + 39550) := by decide
private theorem le_w792 : ∀ n : Fin 50, dimF (n.val + 39600) ≤ 22 := by decide
private theorem pos_w792 : ∀ n : Fin 50, 0 < dimF (n.val + 39600) := by decide
private theorem le_w793 : ∀ n : Fin 50, dimF (n.val + 39650) ≤ 22 := by decide
private theorem pos_w793 : ∀ n : Fin 50, 0 < dimF (n.val + 39650) := by decide
private theorem le_w794 : ∀ n : Fin 50, dimF (n.val + 39700) ≤ 22 := by decide
private theorem pos_w794 : ∀ n : Fin 50, 0 < dimF (n.val + 39700) := by decide
private theorem le_w795 : ∀ n : Fin 50, dimF (n.val + 39750) ≤ 22 := by decide
private theorem pos_w795 : ∀ n : Fin 50, 0 < dimF (n.val + 39750) := by decide
private theorem le_w796 : ∀ n : Fin 50, dimF (n.val + 39800) ≤ 22 := by decide
private theorem pos_w796 : ∀ n : Fin 50, 0 < dimF (n.val + 39800) := by decide
private theorem le_w797 : ∀ n : Fin 50, dimF (n.val + 39850) ≤ 22 := by decide
private theorem pos_w797 : ∀ n : Fin 50, 0 < dimF (n.val + 39850) := by decide
private theorem le_w798 : ∀ n : Fin 50, dimF (n.val + 39900) ≤ 22 := by decide
private theorem pos_w798 : ∀ n : Fin 50, 0 < dimF (n.val + 39900) := by decide
private theorem le_w799 : ∀ n : Fin 50, dimF (n.val + 39950) ≤ 22 := by decide
private theorem pos_w799 : ∀ n : Fin 50, 0 < dimF (n.val + 39950) := by decide

theorem dimF_le_22_range : ∀ n, 35000 ≤ n → n < 40000 → dimF n ≤ 22 := by
  intro n hlo hhi
  by_cases h0 : n < 35050
  · have hr : n - 35000 < 50 := by omega
    have heq : n = (n - 35000) + 35000 := by omega
    rw [heq]
    exact le_w700 ⟨n - 35000, hr⟩
  · by_cases h1 : n < 35100
    · have hr : n - 35050 < 50 := by omega
      have heq : n = (n - 35050) + 35050 := by omega
      rw [heq]
      exact le_w701 ⟨n - 35050, hr⟩
    · by_cases h2 : n < 35150
      · have hr : n - 35100 < 50 := by omega
        have heq : n = (n - 35100) + 35100 := by omega
        rw [heq]
        exact le_w702 ⟨n - 35100, hr⟩
      · by_cases h3 : n < 35200
        · have hr : n - 35150 < 50 := by omega
          have heq : n = (n - 35150) + 35150 := by omega
          rw [heq]
          exact le_w703 ⟨n - 35150, hr⟩
        · by_cases h4 : n < 35250
          · have hr : n - 35200 < 50 := by omega
            have heq : n = (n - 35200) + 35200 := by omega
            rw [heq]
            exact le_w704 ⟨n - 35200, hr⟩
          · by_cases h5 : n < 35300
            · have hr : n - 35250 < 50 := by omega
              have heq : n = (n - 35250) + 35250 := by omega
              rw [heq]
              exact le_w705 ⟨n - 35250, hr⟩
            · by_cases h6 : n < 35350
              · have hr : n - 35300 < 50 := by omega
                have heq : n = (n - 35300) + 35300 := by omega
                rw [heq]
                exact le_w706 ⟨n - 35300, hr⟩
              · by_cases h7 : n < 35400
                · have hr : n - 35350 < 50 := by omega
                  have heq : n = (n - 35350) + 35350 := by omega
                  rw [heq]
                  exact le_w707 ⟨n - 35350, hr⟩
                · by_cases h8 : n < 35450
                  · have hr : n - 35400 < 50 := by omega
                    have heq : n = (n - 35400) + 35400 := by omega
                    rw [heq]
                    exact le_w708 ⟨n - 35400, hr⟩
                  · by_cases h9 : n < 35500
                    · have hr : n - 35450 < 50 := by omega
                      have heq : n = (n - 35450) + 35450 := by omega
                      rw [heq]
                      exact le_w709 ⟨n - 35450, hr⟩
                    · by_cases h10 : n < 35550
                      · have hr : n - 35500 < 50 := by omega
                        have heq : n = (n - 35500) + 35500 := by omega
                        rw [heq]
                        exact le_w710 ⟨n - 35500, hr⟩
                      · by_cases h11 : n < 35600
                        · have hr : n - 35550 < 50 := by omega
                          have heq : n = (n - 35550) + 35550 := by omega
                          rw [heq]
                          exact le_w711 ⟨n - 35550, hr⟩
                        · by_cases h12 : n < 35650
                          · have hr : n - 35600 < 50 := by omega
                            have heq : n = (n - 35600) + 35600 := by omega
                            rw [heq]
                            exact le_w712 ⟨n - 35600, hr⟩
                          · by_cases h13 : n < 35700
                            · have hr : n - 35650 < 50 := by omega
                              have heq : n = (n - 35650) + 35650 := by omega
                              rw [heq]
                              exact le_w713 ⟨n - 35650, hr⟩
                            · by_cases h14 : n < 35750
                              · have hr : n - 35700 < 50 := by omega
                                have heq : n = (n - 35700) + 35700 := by omega
                                rw [heq]
                                exact le_w714 ⟨n - 35700, hr⟩
                              · by_cases h15 : n < 35800
                                · have hr : n - 35750 < 50 := by omega
                                  have heq : n = (n - 35750) + 35750 := by omega
                                  rw [heq]
                                  exact le_w715 ⟨n - 35750, hr⟩
                                · by_cases h16 : n < 35850
                                  · have hr : n - 35800 < 50 := by omega
                                    have heq : n = (n - 35800) + 35800 := by omega
                                    rw [heq]
                                    exact le_w716 ⟨n - 35800, hr⟩
                                  · by_cases h17 : n < 35900
                                    · have hr : n - 35850 < 50 := by omega
                                      have heq : n = (n - 35850) + 35850 := by omega
                                      rw [heq]
                                      exact le_w717 ⟨n - 35850, hr⟩
                                    · by_cases h18 : n < 35950
                                      · have hr : n - 35900 < 50 := by omega
                                        have heq : n = (n - 35900) + 35900 := by omega
                                        rw [heq]
                                        exact le_w718 ⟨n - 35900, hr⟩
                                      · by_cases h19 : n < 36000
                                        · have hr : n - 35950 < 50 := by omega
                                          have heq : n = (n - 35950) + 35950 := by omega
                                          rw [heq]
                                          exact le_w719 ⟨n - 35950, hr⟩
                                        · by_cases h20 : n < 36050
                                          · have hr : n - 36000 < 50 := by omega
                                            have heq : n = (n - 36000) + 36000 := by omega
                                            rw [heq]
                                            exact le_w720 ⟨n - 36000, hr⟩
                                          · by_cases h21 : n < 36100
                                            · have hr : n - 36050 < 50 := by omega
                                              have heq : n = (n - 36050) + 36050 := by omega
                                              rw [heq]
                                              exact le_w721 ⟨n - 36050, hr⟩
                                            · by_cases h22 : n < 36150
                                              · have hr : n - 36100 < 50 := by omega
                                                have heq : n = (n - 36100) + 36100 := by omega
                                                rw [heq]
                                                exact le_w722 ⟨n - 36100, hr⟩
                                              · by_cases h23 : n < 36200
                                                · have hr : n - 36150 < 50 := by omega
                                                  have heq : n = (n - 36150) + 36150 := by omega
                                                  rw [heq]
                                                  exact le_w723 ⟨n - 36150, hr⟩
                                                · by_cases h24 : n < 36250
                                                  · have hr : n - 36200 < 50 := by omega
                                                    have heq : n = (n - 36200) + 36200 := by omega
                                                    rw [heq]
                                                    exact le_w724 ⟨n - 36200, hr⟩
                                                  · by_cases h25 : n < 36300
                                                    · have hr : n - 36250 < 50 := by omega
                                                      have heq : n = (n - 36250) + 36250 := by omega
                                                      rw [heq]
                                                      exact le_w725 ⟨n - 36250, hr⟩
                                                    · by_cases h26 : n < 36350
                                                      · have hr : n - 36300 < 50 := by omega
                                                        have heq : n = (n - 36300) + 36300 := by omega
                                                        rw [heq]
                                                        exact le_w726 ⟨n - 36300, hr⟩
                                                      · by_cases h27 : n < 36400
                                                        · have hr : n - 36350 < 50 := by omega
                                                          have heq : n = (n - 36350) + 36350 := by omega
                                                          rw [heq]
                                                          exact le_w727 ⟨n - 36350, hr⟩
                                                        · by_cases h28 : n < 36450
                                                          · have hr : n - 36400 < 50 := by omega
                                                            have heq : n = (n - 36400) + 36400 := by omega
                                                            rw [heq]
                                                            exact le_w728 ⟨n - 36400, hr⟩
                                                          · by_cases h29 : n < 36500
                                                            · have hr : n - 36450 < 50 := by omega
                                                              have heq : n = (n - 36450) + 36450 := by omega
                                                              rw [heq]
                                                              exact le_w729 ⟨n - 36450, hr⟩
                                                            · by_cases h30 : n < 36550
                                                              · have hr : n - 36500 < 50 := by omega
                                                                have heq : n = (n - 36500) + 36500 := by omega
                                                                rw [heq]
                                                                exact le_w730 ⟨n - 36500, hr⟩
                                                              · by_cases h31 : n < 36600
                                                                · have hr : n - 36550 < 50 := by omega
                                                                  have heq : n = (n - 36550) + 36550 := by omega
                                                                  rw [heq]
                                                                  exact le_w731 ⟨n - 36550, hr⟩
                                                                · by_cases h32 : n < 36650
                                                                  · have hr : n - 36600 < 50 := by omega
                                                                    have heq : n = (n - 36600) + 36600 := by omega
                                                                    rw [heq]
                                                                    exact le_w732 ⟨n - 36600, hr⟩
                                                                  · by_cases h33 : n < 36700
                                                                    · have hr : n - 36650 < 50 := by omega
                                                                      have heq : n = (n - 36650) + 36650 := by omega
                                                                      rw [heq]
                                                                      exact le_w733 ⟨n - 36650, hr⟩
                                                                    · by_cases h34 : n < 36750
                                                                      · have hr : n - 36700 < 50 := by omega
                                                                        have heq : n = (n - 36700) + 36700 := by omega
                                                                        rw [heq]
                                                                        exact le_w734 ⟨n - 36700, hr⟩
                                                                      · by_cases h35 : n < 36800
                                                                        · have hr : n - 36750 < 50 := by omega
                                                                          have heq : n = (n - 36750) + 36750 := by omega
                                                                          rw [heq]
                                                                          exact le_w735 ⟨n - 36750, hr⟩
                                                                        · by_cases h36 : n < 36850
                                                                          · have hr : n - 36800 < 50 := by omega
                                                                            have heq : n = (n - 36800) + 36800 := by omega
                                                                            rw [heq]
                                                                            exact le_w736 ⟨n - 36800, hr⟩
                                                                          · by_cases h37 : n < 36900
                                                                            · have hr : n - 36850 < 50 := by omega
                                                                              have heq : n = (n - 36850) + 36850 := by omega
                                                                              rw [heq]
                                                                              exact le_w737 ⟨n - 36850, hr⟩
                                                                            · by_cases h38 : n < 36950
                                                                              · have hr : n - 36900 < 50 := by omega
                                                                                have heq : n = (n - 36900) + 36900 := by omega
                                                                                rw [heq]
                                                                                exact le_w738 ⟨n - 36900, hr⟩
                                                                              · by_cases h39 : n < 37000
                                                                                · have hr : n - 36950 < 50 := by omega
                                                                                  have heq : n = (n - 36950) + 36950 := by omega
                                                                                  rw [heq]
                                                                                  exact le_w739 ⟨n - 36950, hr⟩
                                                                                · by_cases h40 : n < 37050
                                                                                  · have hr : n - 37000 < 50 := by omega
                                                                                    have heq : n = (n - 37000) + 37000 := by omega
                                                                                    rw [heq]
                                                                                    exact le_w740 ⟨n - 37000, hr⟩
                                                                                  · by_cases h41 : n < 37100
                                                                                    · have hr : n - 37050 < 50 := by omega
                                                                                      have heq : n = (n - 37050) + 37050 := by omega
                                                                                      rw [heq]
                                                                                      exact le_w741 ⟨n - 37050, hr⟩
                                                                                    · by_cases h42 : n < 37150
                                                                                      · have hr : n - 37100 < 50 := by omega
                                                                                        have heq : n = (n - 37100) + 37100 := by omega
                                                                                        rw [heq]
                                                                                        exact le_w742 ⟨n - 37100, hr⟩
                                                                                      · by_cases h43 : n < 37200
                                                                                        · have hr : n - 37150 < 50 := by omega
                                                                                          have heq : n = (n - 37150) + 37150 := by omega
                                                                                          rw [heq]
                                                                                          exact le_w743 ⟨n - 37150, hr⟩
                                                                                        · by_cases h44 : n < 37250
                                                                                          · have hr : n - 37200 < 50 := by omega
                                                                                            have heq : n = (n - 37200) + 37200 := by omega
                                                                                            rw [heq]
                                                                                            exact le_w744 ⟨n - 37200, hr⟩
                                                                                          · by_cases h45 : n < 37300
                                                                                            · have hr : n - 37250 < 50 := by omega
                                                                                              have heq : n = (n - 37250) + 37250 := by omega
                                                                                              rw [heq]
                                                                                              exact le_w745 ⟨n - 37250, hr⟩
                                                                                            · by_cases h46 : n < 37350
                                                                                              · have hr : n - 37300 < 50 := by omega
                                                                                                have heq : n = (n - 37300) + 37300 := by omega
                                                                                                rw [heq]
                                                                                                exact le_w746 ⟨n - 37300, hr⟩
                                                                                              · by_cases h47 : n < 37400
                                                                                                · have hr : n - 37350 < 50 := by omega
                                                                                                  have heq : n = (n - 37350) + 37350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact le_w747 ⟨n - 37350, hr⟩
                                                                                                · by_cases h48 : n < 37450
                                                                                                  · have hr : n - 37400 < 50 := by omega
                                                                                                    have heq : n = (n - 37400) + 37400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact le_w748 ⟨n - 37400, hr⟩
                                                                                                  · by_cases h49 : n < 37500
                                                                                                    · have hr : n - 37450 < 50 := by omega
                                                                                                      have heq : n = (n - 37450) + 37450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact le_w749 ⟨n - 37450, hr⟩
                                                                                                    · by_cases h50 : n < 37550
                                                                                                      · have hr : n - 37500 < 50 := by omega
                                                                                                        have heq : n = (n - 37500) + 37500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact le_w750 ⟨n - 37500, hr⟩
                                                                                                      · by_cases h51 : n < 37600
                                                                                                        · have hr : n - 37550 < 50 := by omega
                                                                                                          have heq : n = (n - 37550) + 37550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact le_w751 ⟨n - 37550, hr⟩
                                                                                                        · by_cases h52 : n < 37650
                                                                                                          · have hr : n - 37600 < 50 := by omega
                                                                                                            have heq : n = (n - 37600) + 37600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact le_w752 ⟨n - 37600, hr⟩
                                                                                                          · by_cases h53 : n < 37700
                                                                                                            · have hr : n - 37650 < 50 := by omega
                                                                                                              have heq : n = (n - 37650) + 37650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact le_w753 ⟨n - 37650, hr⟩
                                                                                                            · by_cases h54 : n < 37750
                                                                                                              · have hr : n - 37700 < 50 := by omega
                                                                                                                have heq : n = (n - 37700) + 37700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact le_w754 ⟨n - 37700, hr⟩
                                                                                                              · by_cases h55 : n < 37800
                                                                                                                · have hr : n - 37750 < 50 := by omega
                                                                                                                  have heq : n = (n - 37750) + 37750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact le_w755 ⟨n - 37750, hr⟩
                                                                                                                · by_cases h56 : n < 37850
                                                                                                                  · have hr : n - 37800 < 50 := by omega
                                                                                                                    have heq : n = (n - 37800) + 37800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact le_w756 ⟨n - 37800, hr⟩
                                                                                                                  · by_cases h57 : n < 37900
                                                                                                                    · have hr : n - 37850 < 50 := by omega
                                                                                                                      have heq : n = (n - 37850) + 37850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact le_w757 ⟨n - 37850, hr⟩
                                                                                                                    · by_cases h58 : n < 37950
                                                                                                                      · have hr : n - 37900 < 50 := by omega
                                                                                                                        have heq : n = (n - 37900) + 37900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact le_w758 ⟨n - 37900, hr⟩
                                                                                                                      · by_cases h59 : n < 38000
                                                                                                                        · have hr : n - 37950 < 50 := by omega
                                                                                                                          have heq : n = (n - 37950) + 37950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact le_w759 ⟨n - 37950, hr⟩
                                                                                                                        · by_cases h60 : n < 38050
                                                                                                                          · have hr : n - 38000 < 50 := by omega
                                                                                                                            have heq : n = (n - 38000) + 38000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact le_w760 ⟨n - 38000, hr⟩
                                                                                                                          · by_cases h61 : n < 38100
                                                                                                                            · have hr : n - 38050 < 50 := by omega
                                                                                                                              have heq : n = (n - 38050) + 38050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact le_w761 ⟨n - 38050, hr⟩
                                                                                                                            · by_cases h62 : n < 38150
                                                                                                                              · have hr : n - 38100 < 50 := by omega
                                                                                                                                have heq : n = (n - 38100) + 38100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact le_w762 ⟨n - 38100, hr⟩
                                                                                                                              · by_cases h63 : n < 38200
                                                                                                                                · have hr : n - 38150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 38150) + 38150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact le_w763 ⟨n - 38150, hr⟩
                                                                                                                                · by_cases h64 : n < 38250
                                                                                                                                  · have hr : n - 38200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 38200) + 38200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact le_w764 ⟨n - 38200, hr⟩
                                                                                                                                  · by_cases h65 : n < 38300
                                                                                                                                    · have hr : n - 38250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 38250) + 38250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact le_w765 ⟨n - 38250, hr⟩
                                                                                                                                    · by_cases h66 : n < 38350
                                                                                                                                      · have hr : n - 38300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 38300) + 38300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact le_w766 ⟨n - 38300, hr⟩
                                                                                                                                      · by_cases h67 : n < 38400
                                                                                                                                        · have hr : n - 38350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 38350) + 38350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact le_w767 ⟨n - 38350, hr⟩
                                                                                                                                        · by_cases h68 : n < 38450
                                                                                                                                          · have hr : n - 38400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 38400) + 38400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact le_w768 ⟨n - 38400, hr⟩
                                                                                                                                          · by_cases h69 : n < 38500
                                                                                                                                            · have hr : n - 38450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 38450) + 38450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact le_w769 ⟨n - 38450, hr⟩
                                                                                                                                            · by_cases h70 : n < 38550
                                                                                                                                              · have hr : n - 38500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 38500) + 38500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact le_w770 ⟨n - 38500, hr⟩
                                                                                                                                              · by_cases h71 : n < 38600
                                                                                                                                                · have hr : n - 38550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 38550) + 38550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact le_w771 ⟨n - 38550, hr⟩
                                                                                                                                                · by_cases h72 : n < 38650
                                                                                                                                                  · have hr : n - 38600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 38600) + 38600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact le_w772 ⟨n - 38600, hr⟩
                                                                                                                                                  · by_cases h73 : n < 38700
                                                                                                                                                    · have hr : n - 38650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 38650) + 38650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact le_w773 ⟨n - 38650, hr⟩
                                                                                                                                                    · by_cases h74 : n < 38750
                                                                                                                                                      · have hr : n - 38700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 38700) + 38700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact le_w774 ⟨n - 38700, hr⟩
                                                                                                                                                      · by_cases h75 : n < 38800
                                                                                                                                                        · have hr : n - 38750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 38750) + 38750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact le_w775 ⟨n - 38750, hr⟩
                                                                                                                                                        · by_cases h76 : n < 38850
                                                                                                                                                          · have hr : n - 38800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 38800) + 38800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact le_w776 ⟨n - 38800, hr⟩
                                                                                                                                                          · by_cases h77 : n < 38900
                                                                                                                                                            · have hr : n - 38850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 38850) + 38850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact le_w777 ⟨n - 38850, hr⟩
                                                                                                                                                            · by_cases h78 : n < 38950
                                                                                                                                                              · have hr : n - 38900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 38900) + 38900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact le_w778 ⟨n - 38900, hr⟩
                                                                                                                                                              · by_cases h79 : n < 39000
                                                                                                                                                                · have hr : n - 38950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 38950) + 38950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact le_w779 ⟨n - 38950, hr⟩
                                                                                                                                                                · by_cases h80 : n < 39050
                                                                                                                                                                  · have hr : n - 39000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 39000) + 39000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact le_w780 ⟨n - 39000, hr⟩
                                                                                                                                                                  · by_cases h81 : n < 39100
                                                                                                                                                                    · have hr : n - 39050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 39050) + 39050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact le_w781 ⟨n - 39050, hr⟩
                                                                                                                                                                    · by_cases h82 : n < 39150
                                                                                                                                                                      · have hr : n - 39100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 39100) + 39100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact le_w782 ⟨n - 39100, hr⟩
                                                                                                                                                                      · by_cases h83 : n < 39200
                                                                                                                                                                        · have hr : n - 39150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 39150) + 39150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact le_w783 ⟨n - 39150, hr⟩
                                                                                                                                                                        · by_cases h84 : n < 39250
                                                                                                                                                                          · have hr : n - 39200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 39200) + 39200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact le_w784 ⟨n - 39200, hr⟩
                                                                                                                                                                          · by_cases h85 : n < 39300
                                                                                                                                                                            · have hr : n - 39250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 39250) + 39250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact le_w785 ⟨n - 39250, hr⟩
                                                                                                                                                                            · by_cases h86 : n < 39350
                                                                                                                                                                              · have hr : n - 39300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 39300) + 39300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact le_w786 ⟨n - 39300, hr⟩
                                                                                                                                                                              · by_cases h87 : n < 39400
                                                                                                                                                                                · have hr : n - 39350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 39350) + 39350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact le_w787 ⟨n - 39350, hr⟩
                                                                                                                                                                                · by_cases h88 : n < 39450
                                                                                                                                                                                  · have hr : n - 39400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 39400) + 39400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact le_w788 ⟨n - 39400, hr⟩
                                                                                                                                                                                  · by_cases h89 : n < 39500
                                                                                                                                                                                    · have hr : n - 39450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 39450) + 39450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact le_w789 ⟨n - 39450, hr⟩
                                                                                                                                                                                    · by_cases h90 : n < 39550
                                                                                                                                                                                      · have hr : n - 39500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 39500) + 39500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact le_w790 ⟨n - 39500, hr⟩
                                                                                                                                                                                      · by_cases h91 : n < 39600
                                                                                                                                                                                        · have hr : n - 39550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 39550) + 39550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact le_w791 ⟨n - 39550, hr⟩
                                                                                                                                                                                        · by_cases h92 : n < 39650
                                                                                                                                                                                          · have hr : n - 39600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 39600) + 39600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact le_w792 ⟨n - 39600, hr⟩
                                                                                                                                                                                          · by_cases h93 : n < 39700
                                                                                                                                                                                            · have hr : n - 39650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 39650) + 39650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact le_w793 ⟨n - 39650, hr⟩
                                                                                                                                                                                            · by_cases h94 : n < 39750
                                                                                                                                                                                              · have hr : n - 39700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 39700) + 39700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact le_w794 ⟨n - 39700, hr⟩
                                                                                                                                                                                              · by_cases h95 : n < 39800
                                                                                                                                                                                                · have hr : n - 39750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 39750) + 39750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact le_w795 ⟨n - 39750, hr⟩
                                                                                                                                                                                                · by_cases h96 : n < 39850
                                                                                                                                                                                                  · have hr : n - 39800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 39800) + 39800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact le_w796 ⟨n - 39800, hr⟩
                                                                                                                                                                                                  · by_cases h97 : n < 39900
                                                                                                                                                                                                    · have hr : n - 39850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 39850) + 39850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact le_w797 ⟨n - 39850, hr⟩
                                                                                                                                                                                                    · by_cases h98 : n < 39950
                                                                                                                                                                                                      · have hr : n - 39900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 39900) + 39900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact le_w798 ⟨n - 39900, hr⟩
                                                                                                                                                                                                      · by_cases h99 : n < 40000
                                                                                                                                                                                                        · have hr : n - 39950 < 50 := by omega
                                                                                                                                                                                                          have heq : n = (n - 39950) + 39950 := by omega
                                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                                          exact le_w799 ⟨n - 39950, hr⟩
                                                                                                                                                                                                        · omega

theorem dimF_pos_range : ∀ n, 35000 ≤ n → n < 40000 → 0 < dimF n := by
  intro n hlo hhi
  by_cases h0 : n < 35050
  · have hr : n - 35000 < 50 := by omega
    have heq : n = (n - 35000) + 35000 := by omega
    rw [heq]
    exact pos_w700 ⟨n - 35000, hr⟩
  · by_cases h1 : n < 35100
    · have hr : n - 35050 < 50 := by omega
      have heq : n = (n - 35050) + 35050 := by omega
      rw [heq]
      exact pos_w701 ⟨n - 35050, hr⟩
    · by_cases h2 : n < 35150
      · have hr : n - 35100 < 50 := by omega
        have heq : n = (n - 35100) + 35100 := by omega
        rw [heq]
        exact pos_w702 ⟨n - 35100, hr⟩
      · by_cases h3 : n < 35200
        · have hr : n - 35150 < 50 := by omega
          have heq : n = (n - 35150) + 35150 := by omega
          rw [heq]
          exact pos_w703 ⟨n - 35150, hr⟩
        · by_cases h4 : n < 35250
          · have hr : n - 35200 < 50 := by omega
            have heq : n = (n - 35200) + 35200 := by omega
            rw [heq]
            exact pos_w704 ⟨n - 35200, hr⟩
          · by_cases h5 : n < 35300
            · have hr : n - 35250 < 50 := by omega
              have heq : n = (n - 35250) + 35250 := by omega
              rw [heq]
              exact pos_w705 ⟨n - 35250, hr⟩
            · by_cases h6 : n < 35350
              · have hr : n - 35300 < 50 := by omega
                have heq : n = (n - 35300) + 35300 := by omega
                rw [heq]
                exact pos_w706 ⟨n - 35300, hr⟩
              · by_cases h7 : n < 35400
                · have hr : n - 35350 < 50 := by omega
                  have heq : n = (n - 35350) + 35350 := by omega
                  rw [heq]
                  exact pos_w707 ⟨n - 35350, hr⟩
                · by_cases h8 : n < 35450
                  · have hr : n - 35400 < 50 := by omega
                    have heq : n = (n - 35400) + 35400 := by omega
                    rw [heq]
                    exact pos_w708 ⟨n - 35400, hr⟩
                  · by_cases h9 : n < 35500
                    · have hr : n - 35450 < 50 := by omega
                      have heq : n = (n - 35450) + 35450 := by omega
                      rw [heq]
                      exact pos_w709 ⟨n - 35450, hr⟩
                    · by_cases h10 : n < 35550
                      · have hr : n - 35500 < 50 := by omega
                        have heq : n = (n - 35500) + 35500 := by omega
                        rw [heq]
                        exact pos_w710 ⟨n - 35500, hr⟩
                      · by_cases h11 : n < 35600
                        · have hr : n - 35550 < 50 := by omega
                          have heq : n = (n - 35550) + 35550 := by omega
                          rw [heq]
                          exact pos_w711 ⟨n - 35550, hr⟩
                        · by_cases h12 : n < 35650
                          · have hr : n - 35600 < 50 := by omega
                            have heq : n = (n - 35600) + 35600 := by omega
                            rw [heq]
                            exact pos_w712 ⟨n - 35600, hr⟩
                          · by_cases h13 : n < 35700
                            · have hr : n - 35650 < 50 := by omega
                              have heq : n = (n - 35650) + 35650 := by omega
                              rw [heq]
                              exact pos_w713 ⟨n - 35650, hr⟩
                            · by_cases h14 : n < 35750
                              · have hr : n - 35700 < 50 := by omega
                                have heq : n = (n - 35700) + 35700 := by omega
                                rw [heq]
                                exact pos_w714 ⟨n - 35700, hr⟩
                              · by_cases h15 : n < 35800
                                · have hr : n - 35750 < 50 := by omega
                                  have heq : n = (n - 35750) + 35750 := by omega
                                  rw [heq]
                                  exact pos_w715 ⟨n - 35750, hr⟩
                                · by_cases h16 : n < 35850
                                  · have hr : n - 35800 < 50 := by omega
                                    have heq : n = (n - 35800) + 35800 := by omega
                                    rw [heq]
                                    exact pos_w716 ⟨n - 35800, hr⟩
                                  · by_cases h17 : n < 35900
                                    · have hr : n - 35850 < 50 := by omega
                                      have heq : n = (n - 35850) + 35850 := by omega
                                      rw [heq]
                                      exact pos_w717 ⟨n - 35850, hr⟩
                                    · by_cases h18 : n < 35950
                                      · have hr : n - 35900 < 50 := by omega
                                        have heq : n = (n - 35900) + 35900 := by omega
                                        rw [heq]
                                        exact pos_w718 ⟨n - 35900, hr⟩
                                      · by_cases h19 : n < 36000
                                        · have hr : n - 35950 < 50 := by omega
                                          have heq : n = (n - 35950) + 35950 := by omega
                                          rw [heq]
                                          exact pos_w719 ⟨n - 35950, hr⟩
                                        · by_cases h20 : n < 36050
                                          · have hr : n - 36000 < 50 := by omega
                                            have heq : n = (n - 36000) + 36000 := by omega
                                            rw [heq]
                                            exact pos_w720 ⟨n - 36000, hr⟩
                                          · by_cases h21 : n < 36100
                                            · have hr : n - 36050 < 50 := by omega
                                              have heq : n = (n - 36050) + 36050 := by omega
                                              rw [heq]
                                              exact pos_w721 ⟨n - 36050, hr⟩
                                            · by_cases h22 : n < 36150
                                              · have hr : n - 36100 < 50 := by omega
                                                have heq : n = (n - 36100) + 36100 := by omega
                                                rw [heq]
                                                exact pos_w722 ⟨n - 36100, hr⟩
                                              · by_cases h23 : n < 36200
                                                · have hr : n - 36150 < 50 := by omega
                                                  have heq : n = (n - 36150) + 36150 := by omega
                                                  rw [heq]
                                                  exact pos_w723 ⟨n - 36150, hr⟩
                                                · by_cases h24 : n < 36250
                                                  · have hr : n - 36200 < 50 := by omega
                                                    have heq : n = (n - 36200) + 36200 := by omega
                                                    rw [heq]
                                                    exact pos_w724 ⟨n - 36200, hr⟩
                                                  · by_cases h25 : n < 36300
                                                    · have hr : n - 36250 < 50 := by omega
                                                      have heq : n = (n - 36250) + 36250 := by omega
                                                      rw [heq]
                                                      exact pos_w725 ⟨n - 36250, hr⟩
                                                    · by_cases h26 : n < 36350
                                                      · have hr : n - 36300 < 50 := by omega
                                                        have heq : n = (n - 36300) + 36300 := by omega
                                                        rw [heq]
                                                        exact pos_w726 ⟨n - 36300, hr⟩
                                                      · by_cases h27 : n < 36400
                                                        · have hr : n - 36350 < 50 := by omega
                                                          have heq : n = (n - 36350) + 36350 := by omega
                                                          rw [heq]
                                                          exact pos_w727 ⟨n - 36350, hr⟩
                                                        · by_cases h28 : n < 36450
                                                          · have hr : n - 36400 < 50 := by omega
                                                            have heq : n = (n - 36400) + 36400 := by omega
                                                            rw [heq]
                                                            exact pos_w728 ⟨n - 36400, hr⟩
                                                          · by_cases h29 : n < 36500
                                                            · have hr : n - 36450 < 50 := by omega
                                                              have heq : n = (n - 36450) + 36450 := by omega
                                                              rw [heq]
                                                              exact pos_w729 ⟨n - 36450, hr⟩
                                                            · by_cases h30 : n < 36550
                                                              · have hr : n - 36500 < 50 := by omega
                                                                have heq : n = (n - 36500) + 36500 := by omega
                                                                rw [heq]
                                                                exact pos_w730 ⟨n - 36500, hr⟩
                                                              · by_cases h31 : n < 36600
                                                                · have hr : n - 36550 < 50 := by omega
                                                                  have heq : n = (n - 36550) + 36550 := by omega
                                                                  rw [heq]
                                                                  exact pos_w731 ⟨n - 36550, hr⟩
                                                                · by_cases h32 : n < 36650
                                                                  · have hr : n - 36600 < 50 := by omega
                                                                    have heq : n = (n - 36600) + 36600 := by omega
                                                                    rw [heq]
                                                                    exact pos_w732 ⟨n - 36600, hr⟩
                                                                  · by_cases h33 : n < 36700
                                                                    · have hr : n - 36650 < 50 := by omega
                                                                      have heq : n = (n - 36650) + 36650 := by omega
                                                                      rw [heq]
                                                                      exact pos_w733 ⟨n - 36650, hr⟩
                                                                    · by_cases h34 : n < 36750
                                                                      · have hr : n - 36700 < 50 := by omega
                                                                        have heq : n = (n - 36700) + 36700 := by omega
                                                                        rw [heq]
                                                                        exact pos_w734 ⟨n - 36700, hr⟩
                                                                      · by_cases h35 : n < 36800
                                                                        · have hr : n - 36750 < 50 := by omega
                                                                          have heq : n = (n - 36750) + 36750 := by omega
                                                                          rw [heq]
                                                                          exact pos_w735 ⟨n - 36750, hr⟩
                                                                        · by_cases h36 : n < 36850
                                                                          · have hr : n - 36800 < 50 := by omega
                                                                            have heq : n = (n - 36800) + 36800 := by omega
                                                                            rw [heq]
                                                                            exact pos_w736 ⟨n - 36800, hr⟩
                                                                          · by_cases h37 : n < 36900
                                                                            · have hr : n - 36850 < 50 := by omega
                                                                              have heq : n = (n - 36850) + 36850 := by omega
                                                                              rw [heq]
                                                                              exact pos_w737 ⟨n - 36850, hr⟩
                                                                            · by_cases h38 : n < 36950
                                                                              · have hr : n - 36900 < 50 := by omega
                                                                                have heq : n = (n - 36900) + 36900 := by omega
                                                                                rw [heq]
                                                                                exact pos_w738 ⟨n - 36900, hr⟩
                                                                              · by_cases h39 : n < 37000
                                                                                · have hr : n - 36950 < 50 := by omega
                                                                                  have heq : n = (n - 36950) + 36950 := by omega
                                                                                  rw [heq]
                                                                                  exact pos_w739 ⟨n - 36950, hr⟩
                                                                                · by_cases h40 : n < 37050
                                                                                  · have hr : n - 37000 < 50 := by omega
                                                                                    have heq : n = (n - 37000) + 37000 := by omega
                                                                                    rw [heq]
                                                                                    exact pos_w740 ⟨n - 37000, hr⟩
                                                                                  · by_cases h41 : n < 37100
                                                                                    · have hr : n - 37050 < 50 := by omega
                                                                                      have heq : n = (n - 37050) + 37050 := by omega
                                                                                      rw [heq]
                                                                                      exact pos_w741 ⟨n - 37050, hr⟩
                                                                                    · by_cases h42 : n < 37150
                                                                                      · have hr : n - 37100 < 50 := by omega
                                                                                        have heq : n = (n - 37100) + 37100 := by omega
                                                                                        rw [heq]
                                                                                        exact pos_w742 ⟨n - 37100, hr⟩
                                                                                      · by_cases h43 : n < 37200
                                                                                        · have hr : n - 37150 < 50 := by omega
                                                                                          have heq : n = (n - 37150) + 37150 := by omega
                                                                                          rw [heq]
                                                                                          exact pos_w743 ⟨n - 37150, hr⟩
                                                                                        · by_cases h44 : n < 37250
                                                                                          · have hr : n - 37200 < 50 := by omega
                                                                                            have heq : n = (n - 37200) + 37200 := by omega
                                                                                            rw [heq]
                                                                                            exact pos_w744 ⟨n - 37200, hr⟩
                                                                                          · by_cases h45 : n < 37300
                                                                                            · have hr : n - 37250 < 50 := by omega
                                                                                              have heq : n = (n - 37250) + 37250 := by omega
                                                                                              rw [heq]
                                                                                              exact pos_w745 ⟨n - 37250, hr⟩
                                                                                            · by_cases h46 : n < 37350
                                                                                              · have hr : n - 37300 < 50 := by omega
                                                                                                have heq : n = (n - 37300) + 37300 := by omega
                                                                                                rw [heq]
                                                                                                exact pos_w746 ⟨n - 37300, hr⟩
                                                                                              · by_cases h47 : n < 37400
                                                                                                · have hr : n - 37350 < 50 := by omega
                                                                                                  have heq : n = (n - 37350) + 37350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact pos_w747 ⟨n - 37350, hr⟩
                                                                                                · by_cases h48 : n < 37450
                                                                                                  · have hr : n - 37400 < 50 := by omega
                                                                                                    have heq : n = (n - 37400) + 37400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact pos_w748 ⟨n - 37400, hr⟩
                                                                                                  · by_cases h49 : n < 37500
                                                                                                    · have hr : n - 37450 < 50 := by omega
                                                                                                      have heq : n = (n - 37450) + 37450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact pos_w749 ⟨n - 37450, hr⟩
                                                                                                    · by_cases h50 : n < 37550
                                                                                                      · have hr : n - 37500 < 50 := by omega
                                                                                                        have heq : n = (n - 37500) + 37500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact pos_w750 ⟨n - 37500, hr⟩
                                                                                                      · by_cases h51 : n < 37600
                                                                                                        · have hr : n - 37550 < 50 := by omega
                                                                                                          have heq : n = (n - 37550) + 37550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact pos_w751 ⟨n - 37550, hr⟩
                                                                                                        · by_cases h52 : n < 37650
                                                                                                          · have hr : n - 37600 < 50 := by omega
                                                                                                            have heq : n = (n - 37600) + 37600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact pos_w752 ⟨n - 37600, hr⟩
                                                                                                          · by_cases h53 : n < 37700
                                                                                                            · have hr : n - 37650 < 50 := by omega
                                                                                                              have heq : n = (n - 37650) + 37650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact pos_w753 ⟨n - 37650, hr⟩
                                                                                                            · by_cases h54 : n < 37750
                                                                                                              · have hr : n - 37700 < 50 := by omega
                                                                                                                have heq : n = (n - 37700) + 37700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact pos_w754 ⟨n - 37700, hr⟩
                                                                                                              · by_cases h55 : n < 37800
                                                                                                                · have hr : n - 37750 < 50 := by omega
                                                                                                                  have heq : n = (n - 37750) + 37750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact pos_w755 ⟨n - 37750, hr⟩
                                                                                                                · by_cases h56 : n < 37850
                                                                                                                  · have hr : n - 37800 < 50 := by omega
                                                                                                                    have heq : n = (n - 37800) + 37800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact pos_w756 ⟨n - 37800, hr⟩
                                                                                                                  · by_cases h57 : n < 37900
                                                                                                                    · have hr : n - 37850 < 50 := by omega
                                                                                                                      have heq : n = (n - 37850) + 37850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact pos_w757 ⟨n - 37850, hr⟩
                                                                                                                    · by_cases h58 : n < 37950
                                                                                                                      · have hr : n - 37900 < 50 := by omega
                                                                                                                        have heq : n = (n - 37900) + 37900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact pos_w758 ⟨n - 37900, hr⟩
                                                                                                                      · by_cases h59 : n < 38000
                                                                                                                        · have hr : n - 37950 < 50 := by omega
                                                                                                                          have heq : n = (n - 37950) + 37950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact pos_w759 ⟨n - 37950, hr⟩
                                                                                                                        · by_cases h60 : n < 38050
                                                                                                                          · have hr : n - 38000 < 50 := by omega
                                                                                                                            have heq : n = (n - 38000) + 38000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact pos_w760 ⟨n - 38000, hr⟩
                                                                                                                          · by_cases h61 : n < 38100
                                                                                                                            · have hr : n - 38050 < 50 := by omega
                                                                                                                              have heq : n = (n - 38050) + 38050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact pos_w761 ⟨n - 38050, hr⟩
                                                                                                                            · by_cases h62 : n < 38150
                                                                                                                              · have hr : n - 38100 < 50 := by omega
                                                                                                                                have heq : n = (n - 38100) + 38100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact pos_w762 ⟨n - 38100, hr⟩
                                                                                                                              · by_cases h63 : n < 38200
                                                                                                                                · have hr : n - 38150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 38150) + 38150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact pos_w763 ⟨n - 38150, hr⟩
                                                                                                                                · by_cases h64 : n < 38250
                                                                                                                                  · have hr : n - 38200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 38200) + 38200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact pos_w764 ⟨n - 38200, hr⟩
                                                                                                                                  · by_cases h65 : n < 38300
                                                                                                                                    · have hr : n - 38250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 38250) + 38250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact pos_w765 ⟨n - 38250, hr⟩
                                                                                                                                    · by_cases h66 : n < 38350
                                                                                                                                      · have hr : n - 38300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 38300) + 38300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact pos_w766 ⟨n - 38300, hr⟩
                                                                                                                                      · by_cases h67 : n < 38400
                                                                                                                                        · have hr : n - 38350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 38350) + 38350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact pos_w767 ⟨n - 38350, hr⟩
                                                                                                                                        · by_cases h68 : n < 38450
                                                                                                                                          · have hr : n - 38400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 38400) + 38400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact pos_w768 ⟨n - 38400, hr⟩
                                                                                                                                          · by_cases h69 : n < 38500
                                                                                                                                            · have hr : n - 38450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 38450) + 38450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact pos_w769 ⟨n - 38450, hr⟩
                                                                                                                                            · by_cases h70 : n < 38550
                                                                                                                                              · have hr : n - 38500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 38500) + 38500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact pos_w770 ⟨n - 38500, hr⟩
                                                                                                                                              · by_cases h71 : n < 38600
                                                                                                                                                · have hr : n - 38550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 38550) + 38550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact pos_w771 ⟨n - 38550, hr⟩
                                                                                                                                                · by_cases h72 : n < 38650
                                                                                                                                                  · have hr : n - 38600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 38600) + 38600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact pos_w772 ⟨n - 38600, hr⟩
                                                                                                                                                  · by_cases h73 : n < 38700
                                                                                                                                                    · have hr : n - 38650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 38650) + 38650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact pos_w773 ⟨n - 38650, hr⟩
                                                                                                                                                    · by_cases h74 : n < 38750
                                                                                                                                                      · have hr : n - 38700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 38700) + 38700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact pos_w774 ⟨n - 38700, hr⟩
                                                                                                                                                      · by_cases h75 : n < 38800
                                                                                                                                                        · have hr : n - 38750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 38750) + 38750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact pos_w775 ⟨n - 38750, hr⟩
                                                                                                                                                        · by_cases h76 : n < 38850
                                                                                                                                                          · have hr : n - 38800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 38800) + 38800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact pos_w776 ⟨n - 38800, hr⟩
                                                                                                                                                          · by_cases h77 : n < 38900
                                                                                                                                                            · have hr : n - 38850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 38850) + 38850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact pos_w777 ⟨n - 38850, hr⟩
                                                                                                                                                            · by_cases h78 : n < 38950
                                                                                                                                                              · have hr : n - 38900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 38900) + 38900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact pos_w778 ⟨n - 38900, hr⟩
                                                                                                                                                              · by_cases h79 : n < 39000
                                                                                                                                                                · have hr : n - 38950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 38950) + 38950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact pos_w779 ⟨n - 38950, hr⟩
                                                                                                                                                                · by_cases h80 : n < 39050
                                                                                                                                                                  · have hr : n - 39000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 39000) + 39000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact pos_w780 ⟨n - 39000, hr⟩
                                                                                                                                                                  · by_cases h81 : n < 39100
                                                                                                                                                                    · have hr : n - 39050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 39050) + 39050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact pos_w781 ⟨n - 39050, hr⟩
                                                                                                                                                                    · by_cases h82 : n < 39150
                                                                                                                                                                      · have hr : n - 39100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 39100) + 39100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact pos_w782 ⟨n - 39100, hr⟩
                                                                                                                                                                      · by_cases h83 : n < 39200
                                                                                                                                                                        · have hr : n - 39150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 39150) + 39150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact pos_w783 ⟨n - 39150, hr⟩
                                                                                                                                                                        · by_cases h84 : n < 39250
                                                                                                                                                                          · have hr : n - 39200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 39200) + 39200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact pos_w784 ⟨n - 39200, hr⟩
                                                                                                                                                                          · by_cases h85 : n < 39300
                                                                                                                                                                            · have hr : n - 39250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 39250) + 39250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact pos_w785 ⟨n - 39250, hr⟩
                                                                                                                                                                            · by_cases h86 : n < 39350
                                                                                                                                                                              · have hr : n - 39300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 39300) + 39300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact pos_w786 ⟨n - 39300, hr⟩
                                                                                                                                                                              · by_cases h87 : n < 39400
                                                                                                                                                                                · have hr : n - 39350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 39350) + 39350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact pos_w787 ⟨n - 39350, hr⟩
                                                                                                                                                                                · by_cases h88 : n < 39450
                                                                                                                                                                                  · have hr : n - 39400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 39400) + 39400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact pos_w788 ⟨n - 39400, hr⟩
                                                                                                                                                                                  · by_cases h89 : n < 39500
                                                                                                                                                                                    · have hr : n - 39450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 39450) + 39450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact pos_w789 ⟨n - 39450, hr⟩
                                                                                                                                                                                    · by_cases h90 : n < 39550
                                                                                                                                                                                      · have hr : n - 39500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 39500) + 39500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact pos_w790 ⟨n - 39500, hr⟩
                                                                                                                                                                                      · by_cases h91 : n < 39600
                                                                                                                                                                                        · have hr : n - 39550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 39550) + 39550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact pos_w791 ⟨n - 39550, hr⟩
                                                                                                                                                                                        · by_cases h92 : n < 39650
                                                                                                                                                                                          · have hr : n - 39600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 39600) + 39600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact pos_w792 ⟨n - 39600, hr⟩
                                                                                                                                                                                          · by_cases h93 : n < 39700
                                                                                                                                                                                            · have hr : n - 39650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 39650) + 39650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact pos_w793 ⟨n - 39650, hr⟩
                                                                                                                                                                                            · by_cases h94 : n < 39750
                                                                                                                                                                                              · have hr : n - 39700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 39700) + 39700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact pos_w794 ⟨n - 39700, hr⟩
                                                                                                                                                                                              · by_cases h95 : n < 39800
                                                                                                                                                                                                · have hr : n - 39750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 39750) + 39750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact pos_w795 ⟨n - 39750, hr⟩
                                                                                                                                                                                                · by_cases h96 : n < 39850
                                                                                                                                                                                                  · have hr : n - 39800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 39800) + 39800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact pos_w796 ⟨n - 39800, hr⟩
                                                                                                                                                                                                  · by_cases h97 : n < 39900
                                                                                                                                                                                                    · have hr : n - 39850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 39850) + 39850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact pos_w797 ⟨n - 39850, hr⟩
                                                                                                                                                                                                    · by_cases h98 : n < 39950
                                                                                                                                                                                                      · have hr : n - 39900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 39900) + 39900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact pos_w798 ⟨n - 39900, hr⟩
                                                                                                                                                                                                      · by_cases h99 : n < 40000
                                                                                                                                                                                                        · have hr : n - 39950 < 50 := by omega
                                                                                                                                                                                                          have heq : n = (n - 39950) + 39950 := by omega
                                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                                          exact pos_w799 ⟨n - 39950, hr⟩
                                                                                                                                                                                                        · omega

end IntMul.Kappa.R8.Bit.Oppbank.DimBound7


