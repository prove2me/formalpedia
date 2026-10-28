-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound8
-- name    : IntMul_Kappa_R8_Data_BitOppbankDimBound8
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:04:13.447116+00:00
-- url     : https://prove2.me/theorems/a44f0f49-bfd0-4c32-84ef-3ad2ed4b99c5
-- title:
--   Densified dimF $\le 22$ pack 8 ($[40000,45000)$)
-- statement:
--   Pack 8 of the densified dimension-field bound.
--
--   For every densified node index $n$ with $40000\le n<45000$, the 5-bit field $\mathrm{dimF}(n)$ extracted from $\mathrm{DIMT}$ satisfies
--   $$1\le \mathrm{dimF}(n)\le 22.$$
--   Proved by `decide` on successive `Fin 50` windows (no `native_decide`).
-- source:
--   R8 BitNB densified DIMT field bound; Fin-window decide packs

-- DimBound pack 8: dimF bounds on n ∈ [40000, 45000)

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

namespace IntMul.Kappa.R8.Bit.Oppbank.DimBound8

private theorem le_w800 : ∀ n : Fin 50, dimF (n.val + 40000) ≤ 22 := by decide
private theorem pos_w800 : ∀ n : Fin 50, 0 < dimF (n.val + 40000) := by decide
private theorem le_w801 : ∀ n : Fin 50, dimF (n.val + 40050) ≤ 22 := by decide
private theorem pos_w801 : ∀ n : Fin 50, 0 < dimF (n.val + 40050) := by decide
private theorem le_w802 : ∀ n : Fin 50, dimF (n.val + 40100) ≤ 22 := by decide
private theorem pos_w802 : ∀ n : Fin 50, 0 < dimF (n.val + 40100) := by decide
private theorem le_w803 : ∀ n : Fin 50, dimF (n.val + 40150) ≤ 22 := by decide
private theorem pos_w803 : ∀ n : Fin 50, 0 < dimF (n.val + 40150) := by decide
private theorem le_w804 : ∀ n : Fin 50, dimF (n.val + 40200) ≤ 22 := by decide
private theorem pos_w804 : ∀ n : Fin 50, 0 < dimF (n.val + 40200) := by decide
private theorem le_w805 : ∀ n : Fin 50, dimF (n.val + 40250) ≤ 22 := by decide
private theorem pos_w805 : ∀ n : Fin 50, 0 < dimF (n.val + 40250) := by decide
private theorem le_w806 : ∀ n : Fin 50, dimF (n.val + 40300) ≤ 22 := by decide
private theorem pos_w806 : ∀ n : Fin 50, 0 < dimF (n.val + 40300) := by decide
private theorem le_w807 : ∀ n : Fin 50, dimF (n.val + 40350) ≤ 22 := by decide
private theorem pos_w807 : ∀ n : Fin 50, 0 < dimF (n.val + 40350) := by decide
private theorem le_w808 : ∀ n : Fin 50, dimF (n.val + 40400) ≤ 22 := by decide
private theorem pos_w808 : ∀ n : Fin 50, 0 < dimF (n.val + 40400) := by decide
private theorem le_w809 : ∀ n : Fin 50, dimF (n.val + 40450) ≤ 22 := by decide
private theorem pos_w809 : ∀ n : Fin 50, 0 < dimF (n.val + 40450) := by decide
private theorem le_w810 : ∀ n : Fin 50, dimF (n.val + 40500) ≤ 22 := by decide
private theorem pos_w810 : ∀ n : Fin 50, 0 < dimF (n.val + 40500) := by decide
private theorem le_w811 : ∀ n : Fin 50, dimF (n.val + 40550) ≤ 22 := by decide
private theorem pos_w811 : ∀ n : Fin 50, 0 < dimF (n.val + 40550) := by decide
private theorem le_w812 : ∀ n : Fin 50, dimF (n.val + 40600) ≤ 22 := by decide
private theorem pos_w812 : ∀ n : Fin 50, 0 < dimF (n.val + 40600) := by decide
private theorem le_w813 : ∀ n : Fin 50, dimF (n.val + 40650) ≤ 22 := by decide
private theorem pos_w813 : ∀ n : Fin 50, 0 < dimF (n.val + 40650) := by decide
private theorem le_w814 : ∀ n : Fin 50, dimF (n.val + 40700) ≤ 22 := by decide
private theorem pos_w814 : ∀ n : Fin 50, 0 < dimF (n.val + 40700) := by decide
private theorem le_w815 : ∀ n : Fin 50, dimF (n.val + 40750) ≤ 22 := by decide
private theorem pos_w815 : ∀ n : Fin 50, 0 < dimF (n.val + 40750) := by decide
private theorem le_w816 : ∀ n : Fin 50, dimF (n.val + 40800) ≤ 22 := by decide
private theorem pos_w816 : ∀ n : Fin 50, 0 < dimF (n.val + 40800) := by decide
private theorem le_w817 : ∀ n : Fin 50, dimF (n.val + 40850) ≤ 22 := by decide
private theorem pos_w817 : ∀ n : Fin 50, 0 < dimF (n.val + 40850) := by decide
private theorem le_w818 : ∀ n : Fin 50, dimF (n.val + 40900) ≤ 22 := by decide
private theorem pos_w818 : ∀ n : Fin 50, 0 < dimF (n.val + 40900) := by decide
private theorem le_w819 : ∀ n : Fin 50, dimF (n.val + 40950) ≤ 22 := by decide
private theorem pos_w819 : ∀ n : Fin 50, 0 < dimF (n.val + 40950) := by decide
private theorem le_w820 : ∀ n : Fin 50, dimF (n.val + 41000) ≤ 22 := by decide
private theorem pos_w820 : ∀ n : Fin 50, 0 < dimF (n.val + 41000) := by decide
private theorem le_w821 : ∀ n : Fin 50, dimF (n.val + 41050) ≤ 22 := by decide
private theorem pos_w821 : ∀ n : Fin 50, 0 < dimF (n.val + 41050) := by decide
private theorem le_w822 : ∀ n : Fin 50, dimF (n.val + 41100) ≤ 22 := by decide
private theorem pos_w822 : ∀ n : Fin 50, 0 < dimF (n.val + 41100) := by decide
private theorem le_w823 : ∀ n : Fin 50, dimF (n.val + 41150) ≤ 22 := by decide
private theorem pos_w823 : ∀ n : Fin 50, 0 < dimF (n.val + 41150) := by decide
private theorem le_w824 : ∀ n : Fin 50, dimF (n.val + 41200) ≤ 22 := by decide
private theorem pos_w824 : ∀ n : Fin 50, 0 < dimF (n.val + 41200) := by decide
private theorem le_w825 : ∀ n : Fin 50, dimF (n.val + 41250) ≤ 22 := by decide
private theorem pos_w825 : ∀ n : Fin 50, 0 < dimF (n.val + 41250) := by decide
private theorem le_w826 : ∀ n : Fin 50, dimF (n.val + 41300) ≤ 22 := by decide
private theorem pos_w826 : ∀ n : Fin 50, 0 < dimF (n.val + 41300) := by decide
private theorem le_w827 : ∀ n : Fin 50, dimF (n.val + 41350) ≤ 22 := by decide
private theorem pos_w827 : ∀ n : Fin 50, 0 < dimF (n.val + 41350) := by decide
private theorem le_w828 : ∀ n : Fin 50, dimF (n.val + 41400) ≤ 22 := by decide
private theorem pos_w828 : ∀ n : Fin 50, 0 < dimF (n.val + 41400) := by decide
private theorem le_w829 : ∀ n : Fin 50, dimF (n.val + 41450) ≤ 22 := by decide
private theorem pos_w829 : ∀ n : Fin 50, 0 < dimF (n.val + 41450) := by decide
private theorem le_w830 : ∀ n : Fin 50, dimF (n.val + 41500) ≤ 22 := by decide
private theorem pos_w830 : ∀ n : Fin 50, 0 < dimF (n.val + 41500) := by decide
private theorem le_w831 : ∀ n : Fin 50, dimF (n.val + 41550) ≤ 22 := by decide
private theorem pos_w831 : ∀ n : Fin 50, 0 < dimF (n.val + 41550) := by decide
private theorem le_w832 : ∀ n : Fin 50, dimF (n.val + 41600) ≤ 22 := by decide
private theorem pos_w832 : ∀ n : Fin 50, 0 < dimF (n.val + 41600) := by decide
private theorem le_w833 : ∀ n : Fin 50, dimF (n.val + 41650) ≤ 22 := by decide
private theorem pos_w833 : ∀ n : Fin 50, 0 < dimF (n.val + 41650) := by decide
private theorem le_w834 : ∀ n : Fin 50, dimF (n.val + 41700) ≤ 22 := by decide
private theorem pos_w834 : ∀ n : Fin 50, 0 < dimF (n.val + 41700) := by decide
private theorem le_w835 : ∀ n : Fin 50, dimF (n.val + 41750) ≤ 22 := by decide
private theorem pos_w835 : ∀ n : Fin 50, 0 < dimF (n.val + 41750) := by decide
private theorem le_w836 : ∀ n : Fin 50, dimF (n.val + 41800) ≤ 22 := by decide
private theorem pos_w836 : ∀ n : Fin 50, 0 < dimF (n.val + 41800) := by decide
private theorem le_w837 : ∀ n : Fin 50, dimF (n.val + 41850) ≤ 22 := by decide
private theorem pos_w837 : ∀ n : Fin 50, 0 < dimF (n.val + 41850) := by decide
private theorem le_w838 : ∀ n : Fin 50, dimF (n.val + 41900) ≤ 22 := by decide
private theorem pos_w838 : ∀ n : Fin 50, 0 < dimF (n.val + 41900) := by decide
private theorem le_w839 : ∀ n : Fin 50, dimF (n.val + 41950) ≤ 22 := by decide
private theorem pos_w839 : ∀ n : Fin 50, 0 < dimF (n.val + 41950) := by decide
private theorem le_w840 : ∀ n : Fin 50, dimF (n.val + 42000) ≤ 22 := by decide
private theorem pos_w840 : ∀ n : Fin 50, 0 < dimF (n.val + 42000) := by decide
private theorem le_w841 : ∀ n : Fin 50, dimF (n.val + 42050) ≤ 22 := by decide
private theorem pos_w841 : ∀ n : Fin 50, 0 < dimF (n.val + 42050) := by decide
private theorem le_w842 : ∀ n : Fin 50, dimF (n.val + 42100) ≤ 22 := by decide
private theorem pos_w842 : ∀ n : Fin 50, 0 < dimF (n.val + 42100) := by decide
private theorem le_w843 : ∀ n : Fin 50, dimF (n.val + 42150) ≤ 22 := by decide
private theorem pos_w843 : ∀ n : Fin 50, 0 < dimF (n.val + 42150) := by decide
private theorem le_w844 : ∀ n : Fin 50, dimF (n.val + 42200) ≤ 22 := by decide
private theorem pos_w844 : ∀ n : Fin 50, 0 < dimF (n.val + 42200) := by decide
private theorem le_w845 : ∀ n : Fin 50, dimF (n.val + 42250) ≤ 22 := by decide
private theorem pos_w845 : ∀ n : Fin 50, 0 < dimF (n.val + 42250) := by decide
private theorem le_w846 : ∀ n : Fin 50, dimF (n.val + 42300) ≤ 22 := by decide
private theorem pos_w846 : ∀ n : Fin 50, 0 < dimF (n.val + 42300) := by decide
private theorem le_w847 : ∀ n : Fin 50, dimF (n.val + 42350) ≤ 22 := by decide
private theorem pos_w847 : ∀ n : Fin 50, 0 < dimF (n.val + 42350) := by decide
private theorem le_w848 : ∀ n : Fin 50, dimF (n.val + 42400) ≤ 22 := by decide
private theorem pos_w848 : ∀ n : Fin 50, 0 < dimF (n.val + 42400) := by decide
private theorem le_w849 : ∀ n : Fin 50, dimF (n.val + 42450) ≤ 22 := by decide
private theorem pos_w849 : ∀ n : Fin 50, 0 < dimF (n.val + 42450) := by decide
private theorem le_w850 : ∀ n : Fin 50, dimF (n.val + 42500) ≤ 22 := by decide
private theorem pos_w850 : ∀ n : Fin 50, 0 < dimF (n.val + 42500) := by decide
private theorem le_w851 : ∀ n : Fin 50, dimF (n.val + 42550) ≤ 22 := by decide
private theorem pos_w851 : ∀ n : Fin 50, 0 < dimF (n.val + 42550) := by decide
private theorem le_w852 : ∀ n : Fin 50, dimF (n.val + 42600) ≤ 22 := by decide
private theorem pos_w852 : ∀ n : Fin 50, 0 < dimF (n.val + 42600) := by decide
private theorem le_w853 : ∀ n : Fin 50, dimF (n.val + 42650) ≤ 22 := by decide
private theorem pos_w853 : ∀ n : Fin 50, 0 < dimF (n.val + 42650) := by decide
private theorem le_w854 : ∀ n : Fin 50, dimF (n.val + 42700) ≤ 22 := by decide
private theorem pos_w854 : ∀ n : Fin 50, 0 < dimF (n.val + 42700) := by decide
private theorem le_w855 : ∀ n : Fin 50, dimF (n.val + 42750) ≤ 22 := by decide
private theorem pos_w855 : ∀ n : Fin 50, 0 < dimF (n.val + 42750) := by decide
private theorem le_w856 : ∀ n : Fin 50, dimF (n.val + 42800) ≤ 22 := by decide
private theorem pos_w856 : ∀ n : Fin 50, 0 < dimF (n.val + 42800) := by decide
private theorem le_w857 : ∀ n : Fin 50, dimF (n.val + 42850) ≤ 22 := by decide
private theorem pos_w857 : ∀ n : Fin 50, 0 < dimF (n.val + 42850) := by decide
private theorem le_w858 : ∀ n : Fin 50, dimF (n.val + 42900) ≤ 22 := by decide
private theorem pos_w858 : ∀ n : Fin 50, 0 < dimF (n.val + 42900) := by decide
private theorem le_w859 : ∀ n : Fin 50, dimF (n.val + 42950) ≤ 22 := by decide
private theorem pos_w859 : ∀ n : Fin 50, 0 < dimF (n.val + 42950) := by decide
private theorem le_w860 : ∀ n : Fin 50, dimF (n.val + 43000) ≤ 22 := by decide
private theorem pos_w860 : ∀ n : Fin 50, 0 < dimF (n.val + 43000) := by decide
private theorem le_w861 : ∀ n : Fin 50, dimF (n.val + 43050) ≤ 22 := by decide
private theorem pos_w861 : ∀ n : Fin 50, 0 < dimF (n.val + 43050) := by decide
private theorem le_w862 : ∀ n : Fin 50, dimF (n.val + 43100) ≤ 22 := by decide
private theorem pos_w862 : ∀ n : Fin 50, 0 < dimF (n.val + 43100) := by decide
private theorem le_w863 : ∀ n : Fin 50, dimF (n.val + 43150) ≤ 22 := by decide
private theorem pos_w863 : ∀ n : Fin 50, 0 < dimF (n.val + 43150) := by decide
private theorem le_w864 : ∀ n : Fin 50, dimF (n.val + 43200) ≤ 22 := by decide
private theorem pos_w864 : ∀ n : Fin 50, 0 < dimF (n.val + 43200) := by decide
private theorem le_w865 : ∀ n : Fin 50, dimF (n.val + 43250) ≤ 22 := by decide
private theorem pos_w865 : ∀ n : Fin 50, 0 < dimF (n.val + 43250) := by decide
private theorem le_w866 : ∀ n : Fin 50, dimF (n.val + 43300) ≤ 22 := by decide
private theorem pos_w866 : ∀ n : Fin 50, 0 < dimF (n.val + 43300) := by decide
private theorem le_w867 : ∀ n : Fin 50, dimF (n.val + 43350) ≤ 22 := by decide
private theorem pos_w867 : ∀ n : Fin 50, 0 < dimF (n.val + 43350) := by decide
private theorem le_w868 : ∀ n : Fin 50, dimF (n.val + 43400) ≤ 22 := by decide
private theorem pos_w868 : ∀ n : Fin 50, 0 < dimF (n.val + 43400) := by decide
private theorem le_w869 : ∀ n : Fin 50, dimF (n.val + 43450) ≤ 22 := by decide
private theorem pos_w869 : ∀ n : Fin 50, 0 < dimF (n.val + 43450) := by decide
private theorem le_w870 : ∀ n : Fin 50, dimF (n.val + 43500) ≤ 22 := by decide
private theorem pos_w870 : ∀ n : Fin 50, 0 < dimF (n.val + 43500) := by decide
private theorem le_w871 : ∀ n : Fin 50, dimF (n.val + 43550) ≤ 22 := by decide
private theorem pos_w871 : ∀ n : Fin 50, 0 < dimF (n.val + 43550) := by decide
private theorem le_w872 : ∀ n : Fin 50, dimF (n.val + 43600) ≤ 22 := by decide
private theorem pos_w872 : ∀ n : Fin 50, 0 < dimF (n.val + 43600) := by decide
private theorem le_w873 : ∀ n : Fin 50, dimF (n.val + 43650) ≤ 22 := by decide
private theorem pos_w873 : ∀ n : Fin 50, 0 < dimF (n.val + 43650) := by decide
private theorem le_w874 : ∀ n : Fin 50, dimF (n.val + 43700) ≤ 22 := by decide
private theorem pos_w874 : ∀ n : Fin 50, 0 < dimF (n.val + 43700) := by decide
private theorem le_w875 : ∀ n : Fin 50, dimF (n.val + 43750) ≤ 22 := by decide
private theorem pos_w875 : ∀ n : Fin 50, 0 < dimF (n.val + 43750) := by decide
private theorem le_w876 : ∀ n : Fin 50, dimF (n.val + 43800) ≤ 22 := by decide
private theorem pos_w876 : ∀ n : Fin 50, 0 < dimF (n.val + 43800) := by decide
private theorem le_w877 : ∀ n : Fin 50, dimF (n.val + 43850) ≤ 22 := by decide
private theorem pos_w877 : ∀ n : Fin 50, 0 < dimF (n.val + 43850) := by decide
private theorem le_w878 : ∀ n : Fin 50, dimF (n.val + 43900) ≤ 22 := by decide
private theorem pos_w878 : ∀ n : Fin 50, 0 < dimF (n.val + 43900) := by decide
private theorem le_w879 : ∀ n : Fin 50, dimF (n.val + 43950) ≤ 22 := by decide
private theorem pos_w879 : ∀ n : Fin 50, 0 < dimF (n.val + 43950) := by decide
private theorem le_w880 : ∀ n : Fin 50, dimF (n.val + 44000) ≤ 22 := by decide
private theorem pos_w880 : ∀ n : Fin 50, 0 < dimF (n.val + 44000) := by decide
private theorem le_w881 : ∀ n : Fin 50, dimF (n.val + 44050) ≤ 22 := by decide
private theorem pos_w881 : ∀ n : Fin 50, 0 < dimF (n.val + 44050) := by decide
private theorem le_w882 : ∀ n : Fin 50, dimF (n.val + 44100) ≤ 22 := by decide
private theorem pos_w882 : ∀ n : Fin 50, 0 < dimF (n.val + 44100) := by decide
private theorem le_w883 : ∀ n : Fin 50, dimF (n.val + 44150) ≤ 22 := by decide
private theorem pos_w883 : ∀ n : Fin 50, 0 < dimF (n.val + 44150) := by decide
private theorem le_w884 : ∀ n : Fin 50, dimF (n.val + 44200) ≤ 22 := by decide
private theorem pos_w884 : ∀ n : Fin 50, 0 < dimF (n.val + 44200) := by decide
private theorem le_w885 : ∀ n : Fin 50, dimF (n.val + 44250) ≤ 22 := by decide
private theorem pos_w885 : ∀ n : Fin 50, 0 < dimF (n.val + 44250) := by decide
private theorem le_w886 : ∀ n : Fin 50, dimF (n.val + 44300) ≤ 22 := by decide
private theorem pos_w886 : ∀ n : Fin 50, 0 < dimF (n.val + 44300) := by decide
private theorem le_w887 : ∀ n : Fin 50, dimF (n.val + 44350) ≤ 22 := by decide
private theorem pos_w887 : ∀ n : Fin 50, 0 < dimF (n.val + 44350) := by decide
private theorem le_w888 : ∀ n : Fin 50, dimF (n.val + 44400) ≤ 22 := by decide
private theorem pos_w888 : ∀ n : Fin 50, 0 < dimF (n.val + 44400) := by decide
private theorem le_w889 : ∀ n : Fin 50, dimF (n.val + 44450) ≤ 22 := by decide
private theorem pos_w889 : ∀ n : Fin 50, 0 < dimF (n.val + 44450) := by decide
private theorem le_w890 : ∀ n : Fin 50, dimF (n.val + 44500) ≤ 22 := by decide
private theorem pos_w890 : ∀ n : Fin 50, 0 < dimF (n.val + 44500) := by decide
private theorem le_w891 : ∀ n : Fin 50, dimF (n.val + 44550) ≤ 22 := by decide
private theorem pos_w891 : ∀ n : Fin 50, 0 < dimF (n.val + 44550) := by decide
private theorem le_w892 : ∀ n : Fin 50, dimF (n.val + 44600) ≤ 22 := by decide
private theorem pos_w892 : ∀ n : Fin 50, 0 < dimF (n.val + 44600) := by decide
private theorem le_w893 : ∀ n : Fin 50, dimF (n.val + 44650) ≤ 22 := by decide
private theorem pos_w893 : ∀ n : Fin 50, 0 < dimF (n.val + 44650) := by decide
private theorem le_w894 : ∀ n : Fin 50, dimF (n.val + 44700) ≤ 22 := by decide
private theorem pos_w894 : ∀ n : Fin 50, 0 < dimF (n.val + 44700) := by decide
private theorem le_w895 : ∀ n : Fin 50, dimF (n.val + 44750) ≤ 22 := by decide
private theorem pos_w895 : ∀ n : Fin 50, 0 < dimF (n.val + 44750) := by decide
private theorem le_w896 : ∀ n : Fin 50, dimF (n.val + 44800) ≤ 22 := by decide
private theorem pos_w896 : ∀ n : Fin 50, 0 < dimF (n.val + 44800) := by decide
private theorem le_w897 : ∀ n : Fin 50, dimF (n.val + 44850) ≤ 22 := by decide
private theorem pos_w897 : ∀ n : Fin 50, 0 < dimF (n.val + 44850) := by decide
private theorem le_w898 : ∀ n : Fin 50, dimF (n.val + 44900) ≤ 22 := by decide
private theorem pos_w898 : ∀ n : Fin 50, 0 < dimF (n.val + 44900) := by decide
private theorem le_w899 : ∀ n : Fin 50, dimF (n.val + 44950) ≤ 22 := by decide
private theorem pos_w899 : ∀ n : Fin 50, 0 < dimF (n.val + 44950) := by decide

theorem dimF_le_22_range : ∀ n, 40000 ≤ n → n < 45000 → dimF n ≤ 22 := by
  intro n hlo hhi
  by_cases h0 : n < 40050
  · have hr : n - 40000 < 50 := by omega
    have heq : n = (n - 40000) + 40000 := by omega
    rw [heq]
    exact le_w800 ⟨n - 40000, hr⟩
  · by_cases h1 : n < 40100
    · have hr : n - 40050 < 50 := by omega
      have heq : n = (n - 40050) + 40050 := by omega
      rw [heq]
      exact le_w801 ⟨n - 40050, hr⟩
    · by_cases h2 : n < 40150
      · have hr : n - 40100 < 50 := by omega
        have heq : n = (n - 40100) + 40100 := by omega
        rw [heq]
        exact le_w802 ⟨n - 40100, hr⟩
      · by_cases h3 : n < 40200
        · have hr : n - 40150 < 50 := by omega
          have heq : n = (n - 40150) + 40150 := by omega
          rw [heq]
          exact le_w803 ⟨n - 40150, hr⟩
        · by_cases h4 : n < 40250
          · have hr : n - 40200 < 50 := by omega
            have heq : n = (n - 40200) + 40200 := by omega
            rw [heq]
            exact le_w804 ⟨n - 40200, hr⟩
          · by_cases h5 : n < 40300
            · have hr : n - 40250 < 50 := by omega
              have heq : n = (n - 40250) + 40250 := by omega
              rw [heq]
              exact le_w805 ⟨n - 40250, hr⟩
            · by_cases h6 : n < 40350
              · have hr : n - 40300 < 50 := by omega
                have heq : n = (n - 40300) + 40300 := by omega
                rw [heq]
                exact le_w806 ⟨n - 40300, hr⟩
              · by_cases h7 : n < 40400
                · have hr : n - 40350 < 50 := by omega
                  have heq : n = (n - 40350) + 40350 := by omega
                  rw [heq]
                  exact le_w807 ⟨n - 40350, hr⟩
                · by_cases h8 : n < 40450
                  · have hr : n - 40400 < 50 := by omega
                    have heq : n = (n - 40400) + 40400 := by omega
                    rw [heq]
                    exact le_w808 ⟨n - 40400, hr⟩
                  · by_cases h9 : n < 40500
                    · have hr : n - 40450 < 50 := by omega
                      have heq : n = (n - 40450) + 40450 := by omega
                      rw [heq]
                      exact le_w809 ⟨n - 40450, hr⟩
                    · by_cases h10 : n < 40550
                      · have hr : n - 40500 < 50 := by omega
                        have heq : n = (n - 40500) + 40500 := by omega
                        rw [heq]
                        exact le_w810 ⟨n - 40500, hr⟩
                      · by_cases h11 : n < 40600
                        · have hr : n - 40550 < 50 := by omega
                          have heq : n = (n - 40550) + 40550 := by omega
                          rw [heq]
                          exact le_w811 ⟨n - 40550, hr⟩
                        · by_cases h12 : n < 40650
                          · have hr : n - 40600 < 50 := by omega
                            have heq : n = (n - 40600) + 40600 := by omega
                            rw [heq]
                            exact le_w812 ⟨n - 40600, hr⟩
                          · by_cases h13 : n < 40700
                            · have hr : n - 40650 < 50 := by omega
                              have heq : n = (n - 40650) + 40650 := by omega
                              rw [heq]
                              exact le_w813 ⟨n - 40650, hr⟩
                            · by_cases h14 : n < 40750
                              · have hr : n - 40700 < 50 := by omega
                                have heq : n = (n - 40700) + 40700 := by omega
                                rw [heq]
                                exact le_w814 ⟨n - 40700, hr⟩
                              · by_cases h15 : n < 40800
                                · have hr : n - 40750 < 50 := by omega
                                  have heq : n = (n - 40750) + 40750 := by omega
                                  rw [heq]
                                  exact le_w815 ⟨n - 40750, hr⟩
                                · by_cases h16 : n < 40850
                                  · have hr : n - 40800 < 50 := by omega
                                    have heq : n = (n - 40800) + 40800 := by omega
                                    rw [heq]
                                    exact le_w816 ⟨n - 40800, hr⟩
                                  · by_cases h17 : n < 40900
                                    · have hr : n - 40850 < 50 := by omega
                                      have heq : n = (n - 40850) + 40850 := by omega
                                      rw [heq]
                                      exact le_w817 ⟨n - 40850, hr⟩
                                    · by_cases h18 : n < 40950
                                      · have hr : n - 40900 < 50 := by omega
                                        have heq : n = (n - 40900) + 40900 := by omega
                                        rw [heq]
                                        exact le_w818 ⟨n - 40900, hr⟩
                                      · by_cases h19 : n < 41000
                                        · have hr : n - 40950 < 50 := by omega
                                          have heq : n = (n - 40950) + 40950 := by omega
                                          rw [heq]
                                          exact le_w819 ⟨n - 40950, hr⟩
                                        · by_cases h20 : n < 41050
                                          · have hr : n - 41000 < 50 := by omega
                                            have heq : n = (n - 41000) + 41000 := by omega
                                            rw [heq]
                                            exact le_w820 ⟨n - 41000, hr⟩
                                          · by_cases h21 : n < 41100
                                            · have hr : n - 41050 < 50 := by omega
                                              have heq : n = (n - 41050) + 41050 := by omega
                                              rw [heq]
                                              exact le_w821 ⟨n - 41050, hr⟩
                                            · by_cases h22 : n < 41150
                                              · have hr : n - 41100 < 50 := by omega
                                                have heq : n = (n - 41100) + 41100 := by omega
                                                rw [heq]
                                                exact le_w822 ⟨n - 41100, hr⟩
                                              · by_cases h23 : n < 41200
                                                · have hr : n - 41150 < 50 := by omega
                                                  have heq : n = (n - 41150) + 41150 := by omega
                                                  rw [heq]
                                                  exact le_w823 ⟨n - 41150, hr⟩
                                                · by_cases h24 : n < 41250
                                                  · have hr : n - 41200 < 50 := by omega
                                                    have heq : n = (n - 41200) + 41200 := by omega
                                                    rw [heq]
                                                    exact le_w824 ⟨n - 41200, hr⟩
                                                  · by_cases h25 : n < 41300
                                                    · have hr : n - 41250 < 50 := by omega
                                                      have heq : n = (n - 41250) + 41250 := by omega
                                                      rw [heq]
                                                      exact le_w825 ⟨n - 41250, hr⟩
                                                    · by_cases h26 : n < 41350
                                                      · have hr : n - 41300 < 50 := by omega
                                                        have heq : n = (n - 41300) + 41300 := by omega
                                                        rw [heq]
                                                        exact le_w826 ⟨n - 41300, hr⟩
                                                      · by_cases h27 : n < 41400
                                                        · have hr : n - 41350 < 50 := by omega
                                                          have heq : n = (n - 41350) + 41350 := by omega
                                                          rw [heq]
                                                          exact le_w827 ⟨n - 41350, hr⟩
                                                        · by_cases h28 : n < 41450
                                                          · have hr : n - 41400 < 50 := by omega
                                                            have heq : n = (n - 41400) + 41400 := by omega
                                                            rw [heq]
                                                            exact le_w828 ⟨n - 41400, hr⟩
                                                          · by_cases h29 : n < 41500
                                                            · have hr : n - 41450 < 50 := by omega
                                                              have heq : n = (n - 41450) + 41450 := by omega
                                                              rw [heq]
                                                              exact le_w829 ⟨n - 41450, hr⟩
                                                            · by_cases h30 : n < 41550
                                                              · have hr : n - 41500 < 50 := by omega
                                                                have heq : n = (n - 41500) + 41500 := by omega
                                                                rw [heq]
                                                                exact le_w830 ⟨n - 41500, hr⟩
                                                              · by_cases h31 : n < 41600
                                                                · have hr : n - 41550 < 50 := by omega
                                                                  have heq : n = (n - 41550) + 41550 := by omega
                                                                  rw [heq]
                                                                  exact le_w831 ⟨n - 41550, hr⟩
                                                                · by_cases h32 : n < 41650
                                                                  · have hr : n - 41600 < 50 := by omega
                                                                    have heq : n = (n - 41600) + 41600 := by omega
                                                                    rw [heq]
                                                                    exact le_w832 ⟨n - 41600, hr⟩
                                                                  · by_cases h33 : n < 41700
                                                                    · have hr : n - 41650 < 50 := by omega
                                                                      have heq : n = (n - 41650) + 41650 := by omega
                                                                      rw [heq]
                                                                      exact le_w833 ⟨n - 41650, hr⟩
                                                                    · by_cases h34 : n < 41750
                                                                      · have hr : n - 41700 < 50 := by omega
                                                                        have heq : n = (n - 41700) + 41700 := by omega
                                                                        rw [heq]
                                                                        exact le_w834 ⟨n - 41700, hr⟩
                                                                      · by_cases h35 : n < 41800
                                                                        · have hr : n - 41750 < 50 := by omega
                                                                          have heq : n = (n - 41750) + 41750 := by omega
                                                                          rw [heq]
                                                                          exact le_w835 ⟨n - 41750, hr⟩
                                                                        · by_cases h36 : n < 41850
                                                                          · have hr : n - 41800 < 50 := by omega
                                                                            have heq : n = (n - 41800) + 41800 := by omega
                                                                            rw [heq]
                                                                            exact le_w836 ⟨n - 41800, hr⟩
                                                                          · by_cases h37 : n < 41900
                                                                            · have hr : n - 41850 < 50 := by omega
                                                                              have heq : n = (n - 41850) + 41850 := by omega
                                                                              rw [heq]
                                                                              exact le_w837 ⟨n - 41850, hr⟩
                                                                            · by_cases h38 : n < 41950
                                                                              · have hr : n - 41900 < 50 := by omega
                                                                                have heq : n = (n - 41900) + 41900 := by omega
                                                                                rw [heq]
                                                                                exact le_w838 ⟨n - 41900, hr⟩
                                                                              · by_cases h39 : n < 42000
                                                                                · have hr : n - 41950 < 50 := by omega
                                                                                  have heq : n = (n - 41950) + 41950 := by omega
                                                                                  rw [heq]
                                                                                  exact le_w839 ⟨n - 41950, hr⟩
                                                                                · by_cases h40 : n < 42050
                                                                                  · have hr : n - 42000 < 50 := by omega
                                                                                    have heq : n = (n - 42000) + 42000 := by omega
                                                                                    rw [heq]
                                                                                    exact le_w840 ⟨n - 42000, hr⟩
                                                                                  · by_cases h41 : n < 42100
                                                                                    · have hr : n - 42050 < 50 := by omega
                                                                                      have heq : n = (n - 42050) + 42050 := by omega
                                                                                      rw [heq]
                                                                                      exact le_w841 ⟨n - 42050, hr⟩
                                                                                    · by_cases h42 : n < 42150
                                                                                      · have hr : n - 42100 < 50 := by omega
                                                                                        have heq : n = (n - 42100) + 42100 := by omega
                                                                                        rw [heq]
                                                                                        exact le_w842 ⟨n - 42100, hr⟩
                                                                                      · by_cases h43 : n < 42200
                                                                                        · have hr : n - 42150 < 50 := by omega
                                                                                          have heq : n = (n - 42150) + 42150 := by omega
                                                                                          rw [heq]
                                                                                          exact le_w843 ⟨n - 42150, hr⟩
                                                                                        · by_cases h44 : n < 42250
                                                                                          · have hr : n - 42200 < 50 := by omega
                                                                                            have heq : n = (n - 42200) + 42200 := by omega
                                                                                            rw [heq]
                                                                                            exact le_w844 ⟨n - 42200, hr⟩
                                                                                          · by_cases h45 : n < 42300
                                                                                            · have hr : n - 42250 < 50 := by omega
                                                                                              have heq : n = (n - 42250) + 42250 := by omega
                                                                                              rw [heq]
                                                                                              exact le_w845 ⟨n - 42250, hr⟩
                                                                                            · by_cases h46 : n < 42350
                                                                                              · have hr : n - 42300 < 50 := by omega
                                                                                                have heq : n = (n - 42300) + 42300 := by omega
                                                                                                rw [heq]
                                                                                                exact le_w846 ⟨n - 42300, hr⟩
                                                                                              · by_cases h47 : n < 42400
                                                                                                · have hr : n - 42350 < 50 := by omega
                                                                                                  have heq : n = (n - 42350) + 42350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact le_w847 ⟨n - 42350, hr⟩
                                                                                                · by_cases h48 : n < 42450
                                                                                                  · have hr : n - 42400 < 50 := by omega
                                                                                                    have heq : n = (n - 42400) + 42400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact le_w848 ⟨n - 42400, hr⟩
                                                                                                  · by_cases h49 : n < 42500
                                                                                                    · have hr : n - 42450 < 50 := by omega
                                                                                                      have heq : n = (n - 42450) + 42450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact le_w849 ⟨n - 42450, hr⟩
                                                                                                    · by_cases h50 : n < 42550
                                                                                                      · have hr : n - 42500 < 50 := by omega
                                                                                                        have heq : n = (n - 42500) + 42500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact le_w850 ⟨n - 42500, hr⟩
                                                                                                      · by_cases h51 : n < 42600
                                                                                                        · have hr : n - 42550 < 50 := by omega
                                                                                                          have heq : n = (n - 42550) + 42550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact le_w851 ⟨n - 42550, hr⟩
                                                                                                        · by_cases h52 : n < 42650
                                                                                                          · have hr : n - 42600 < 50 := by omega
                                                                                                            have heq : n = (n - 42600) + 42600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact le_w852 ⟨n - 42600, hr⟩
                                                                                                          · by_cases h53 : n < 42700
                                                                                                            · have hr : n - 42650 < 50 := by omega
                                                                                                              have heq : n = (n - 42650) + 42650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact le_w853 ⟨n - 42650, hr⟩
                                                                                                            · by_cases h54 : n < 42750
                                                                                                              · have hr : n - 42700 < 50 := by omega
                                                                                                                have heq : n = (n - 42700) + 42700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact le_w854 ⟨n - 42700, hr⟩
                                                                                                              · by_cases h55 : n < 42800
                                                                                                                · have hr : n - 42750 < 50 := by omega
                                                                                                                  have heq : n = (n - 42750) + 42750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact le_w855 ⟨n - 42750, hr⟩
                                                                                                                · by_cases h56 : n < 42850
                                                                                                                  · have hr : n - 42800 < 50 := by omega
                                                                                                                    have heq : n = (n - 42800) + 42800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact le_w856 ⟨n - 42800, hr⟩
                                                                                                                  · by_cases h57 : n < 42900
                                                                                                                    · have hr : n - 42850 < 50 := by omega
                                                                                                                      have heq : n = (n - 42850) + 42850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact le_w857 ⟨n - 42850, hr⟩
                                                                                                                    · by_cases h58 : n < 42950
                                                                                                                      · have hr : n - 42900 < 50 := by omega
                                                                                                                        have heq : n = (n - 42900) + 42900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact le_w858 ⟨n - 42900, hr⟩
                                                                                                                      · by_cases h59 : n < 43000
                                                                                                                        · have hr : n - 42950 < 50 := by omega
                                                                                                                          have heq : n = (n - 42950) + 42950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact le_w859 ⟨n - 42950, hr⟩
                                                                                                                        · by_cases h60 : n < 43050
                                                                                                                          · have hr : n - 43000 < 50 := by omega
                                                                                                                            have heq : n = (n - 43000) + 43000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact le_w860 ⟨n - 43000, hr⟩
                                                                                                                          · by_cases h61 : n < 43100
                                                                                                                            · have hr : n - 43050 < 50 := by omega
                                                                                                                              have heq : n = (n - 43050) + 43050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact le_w861 ⟨n - 43050, hr⟩
                                                                                                                            · by_cases h62 : n < 43150
                                                                                                                              · have hr : n - 43100 < 50 := by omega
                                                                                                                                have heq : n = (n - 43100) + 43100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact le_w862 ⟨n - 43100, hr⟩
                                                                                                                              · by_cases h63 : n < 43200
                                                                                                                                · have hr : n - 43150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 43150) + 43150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact le_w863 ⟨n - 43150, hr⟩
                                                                                                                                · by_cases h64 : n < 43250
                                                                                                                                  · have hr : n - 43200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 43200) + 43200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact le_w864 ⟨n - 43200, hr⟩
                                                                                                                                  · by_cases h65 : n < 43300
                                                                                                                                    · have hr : n - 43250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 43250) + 43250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact le_w865 ⟨n - 43250, hr⟩
                                                                                                                                    · by_cases h66 : n < 43350
                                                                                                                                      · have hr : n - 43300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 43300) + 43300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact le_w866 ⟨n - 43300, hr⟩
                                                                                                                                      · by_cases h67 : n < 43400
                                                                                                                                        · have hr : n - 43350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 43350) + 43350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact le_w867 ⟨n - 43350, hr⟩
                                                                                                                                        · by_cases h68 : n < 43450
                                                                                                                                          · have hr : n - 43400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 43400) + 43400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact le_w868 ⟨n - 43400, hr⟩
                                                                                                                                          · by_cases h69 : n < 43500
                                                                                                                                            · have hr : n - 43450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 43450) + 43450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact le_w869 ⟨n - 43450, hr⟩
                                                                                                                                            · by_cases h70 : n < 43550
                                                                                                                                              · have hr : n - 43500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 43500) + 43500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact le_w870 ⟨n - 43500, hr⟩
                                                                                                                                              · by_cases h71 : n < 43600
                                                                                                                                                · have hr : n - 43550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 43550) + 43550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact le_w871 ⟨n - 43550, hr⟩
                                                                                                                                                · by_cases h72 : n < 43650
                                                                                                                                                  · have hr : n - 43600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 43600) + 43600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact le_w872 ⟨n - 43600, hr⟩
                                                                                                                                                  · by_cases h73 : n < 43700
                                                                                                                                                    · have hr : n - 43650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 43650) + 43650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact le_w873 ⟨n - 43650, hr⟩
                                                                                                                                                    · by_cases h74 : n < 43750
                                                                                                                                                      · have hr : n - 43700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 43700) + 43700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact le_w874 ⟨n - 43700, hr⟩
                                                                                                                                                      · by_cases h75 : n < 43800
                                                                                                                                                        · have hr : n - 43750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 43750) + 43750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact le_w875 ⟨n - 43750, hr⟩
                                                                                                                                                        · by_cases h76 : n < 43850
                                                                                                                                                          · have hr : n - 43800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 43800) + 43800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact le_w876 ⟨n - 43800, hr⟩
                                                                                                                                                          · by_cases h77 : n < 43900
                                                                                                                                                            · have hr : n - 43850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 43850) + 43850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact le_w877 ⟨n - 43850, hr⟩
                                                                                                                                                            · by_cases h78 : n < 43950
                                                                                                                                                              · have hr : n - 43900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 43900) + 43900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact le_w878 ⟨n - 43900, hr⟩
                                                                                                                                                              · by_cases h79 : n < 44000
                                                                                                                                                                · have hr : n - 43950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 43950) + 43950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact le_w879 ⟨n - 43950, hr⟩
                                                                                                                                                                · by_cases h80 : n < 44050
                                                                                                                                                                  · have hr : n - 44000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 44000) + 44000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact le_w880 ⟨n - 44000, hr⟩
                                                                                                                                                                  · by_cases h81 : n < 44100
                                                                                                                                                                    · have hr : n - 44050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 44050) + 44050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact le_w881 ⟨n - 44050, hr⟩
                                                                                                                                                                    · by_cases h82 : n < 44150
                                                                                                                                                                      · have hr : n - 44100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 44100) + 44100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact le_w882 ⟨n - 44100, hr⟩
                                                                                                                                                                      · by_cases h83 : n < 44200
                                                                                                                                                                        · have hr : n - 44150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 44150) + 44150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact le_w883 ⟨n - 44150, hr⟩
                                                                                                                                                                        · by_cases h84 : n < 44250
                                                                                                                                                                          · have hr : n - 44200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 44200) + 44200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact le_w884 ⟨n - 44200, hr⟩
                                                                                                                                                                          · by_cases h85 : n < 44300
                                                                                                                                                                            · have hr : n - 44250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 44250) + 44250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact le_w885 ⟨n - 44250, hr⟩
                                                                                                                                                                            · by_cases h86 : n < 44350
                                                                                                                                                                              · have hr : n - 44300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 44300) + 44300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact le_w886 ⟨n - 44300, hr⟩
                                                                                                                                                                              · by_cases h87 : n < 44400
                                                                                                                                                                                · have hr : n - 44350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 44350) + 44350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact le_w887 ⟨n - 44350, hr⟩
                                                                                                                                                                                · by_cases h88 : n < 44450
                                                                                                                                                                                  · have hr : n - 44400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 44400) + 44400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact le_w888 ⟨n - 44400, hr⟩
                                                                                                                                                                                  · by_cases h89 : n < 44500
                                                                                                                                                                                    · have hr : n - 44450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 44450) + 44450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact le_w889 ⟨n - 44450, hr⟩
                                                                                                                                                                                    · by_cases h90 : n < 44550
                                                                                                                                                                                      · have hr : n - 44500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 44500) + 44500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact le_w890 ⟨n - 44500, hr⟩
                                                                                                                                                                                      · by_cases h91 : n < 44600
                                                                                                                                                                                        · have hr : n - 44550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 44550) + 44550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact le_w891 ⟨n - 44550, hr⟩
                                                                                                                                                                                        · by_cases h92 : n < 44650
                                                                                                                                                                                          · have hr : n - 44600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 44600) + 44600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact le_w892 ⟨n - 44600, hr⟩
                                                                                                                                                                                          · by_cases h93 : n < 44700
                                                                                                                                                                                            · have hr : n - 44650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 44650) + 44650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact le_w893 ⟨n - 44650, hr⟩
                                                                                                                                                                                            · by_cases h94 : n < 44750
                                                                                                                                                                                              · have hr : n - 44700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 44700) + 44700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact le_w894 ⟨n - 44700, hr⟩
                                                                                                                                                                                              · by_cases h95 : n < 44800
                                                                                                                                                                                                · have hr : n - 44750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 44750) + 44750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact le_w895 ⟨n - 44750, hr⟩
                                                                                                                                                                                                · by_cases h96 : n < 44850
                                                                                                                                                                                                  · have hr : n - 44800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 44800) + 44800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact le_w896 ⟨n - 44800, hr⟩
                                                                                                                                                                                                  · by_cases h97 : n < 44900
                                                                                                                                                                                                    · have hr : n - 44850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 44850) + 44850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact le_w897 ⟨n - 44850, hr⟩
                                                                                                                                                                                                    · by_cases h98 : n < 44950
                                                                                                                                                                                                      · have hr : n - 44900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 44900) + 44900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact le_w898 ⟨n - 44900, hr⟩
                                                                                                                                                                                                      · by_cases h99 : n < 45000
                                                                                                                                                                                                        · have hr : n - 44950 < 50 := by omega
                                                                                                                                                                                                          have heq : n = (n - 44950) + 44950 := by omega
                                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                                          exact le_w899 ⟨n - 44950, hr⟩
                                                                                                                                                                                                        · omega

theorem dimF_pos_range : ∀ n, 40000 ≤ n → n < 45000 → 0 < dimF n := by
  intro n hlo hhi
  by_cases h0 : n < 40050
  · have hr : n - 40000 < 50 := by omega
    have heq : n = (n - 40000) + 40000 := by omega
    rw [heq]
    exact pos_w800 ⟨n - 40000, hr⟩
  · by_cases h1 : n < 40100
    · have hr : n - 40050 < 50 := by omega
      have heq : n = (n - 40050) + 40050 := by omega
      rw [heq]
      exact pos_w801 ⟨n - 40050, hr⟩
    · by_cases h2 : n < 40150
      · have hr : n - 40100 < 50 := by omega
        have heq : n = (n - 40100) + 40100 := by omega
        rw [heq]
        exact pos_w802 ⟨n - 40100, hr⟩
      · by_cases h3 : n < 40200
        · have hr : n - 40150 < 50 := by omega
          have heq : n = (n - 40150) + 40150 := by omega
          rw [heq]
          exact pos_w803 ⟨n - 40150, hr⟩
        · by_cases h4 : n < 40250
          · have hr : n - 40200 < 50 := by omega
            have heq : n = (n - 40200) + 40200 := by omega
            rw [heq]
            exact pos_w804 ⟨n - 40200, hr⟩
          · by_cases h5 : n < 40300
            · have hr : n - 40250 < 50 := by omega
              have heq : n = (n - 40250) + 40250 := by omega
              rw [heq]
              exact pos_w805 ⟨n - 40250, hr⟩
            · by_cases h6 : n < 40350
              · have hr : n - 40300 < 50 := by omega
                have heq : n = (n - 40300) + 40300 := by omega
                rw [heq]
                exact pos_w806 ⟨n - 40300, hr⟩
              · by_cases h7 : n < 40400
                · have hr : n - 40350 < 50 := by omega
                  have heq : n = (n - 40350) + 40350 := by omega
                  rw [heq]
                  exact pos_w807 ⟨n - 40350, hr⟩
                · by_cases h8 : n < 40450
                  · have hr : n - 40400 < 50 := by omega
                    have heq : n = (n - 40400) + 40400 := by omega
                    rw [heq]
                    exact pos_w808 ⟨n - 40400, hr⟩
                  · by_cases h9 : n < 40500
                    · have hr : n - 40450 < 50 := by omega
                      have heq : n = (n - 40450) + 40450 := by omega
                      rw [heq]
                      exact pos_w809 ⟨n - 40450, hr⟩
                    · by_cases h10 : n < 40550
                      · have hr : n - 40500 < 50 := by omega
                        have heq : n = (n - 40500) + 40500 := by omega
                        rw [heq]
                        exact pos_w810 ⟨n - 40500, hr⟩
                      · by_cases h11 : n < 40600
                        · have hr : n - 40550 < 50 := by omega
                          have heq : n = (n - 40550) + 40550 := by omega
                          rw [heq]
                          exact pos_w811 ⟨n - 40550, hr⟩
                        · by_cases h12 : n < 40650
                          · have hr : n - 40600 < 50 := by omega
                            have heq : n = (n - 40600) + 40600 := by omega
                            rw [heq]
                            exact pos_w812 ⟨n - 40600, hr⟩
                          · by_cases h13 : n < 40700
                            · have hr : n - 40650 < 50 := by omega
                              have heq : n = (n - 40650) + 40650 := by omega
                              rw [heq]
                              exact pos_w813 ⟨n - 40650, hr⟩
                            · by_cases h14 : n < 40750
                              · have hr : n - 40700 < 50 := by omega
                                have heq : n = (n - 40700) + 40700 := by omega
                                rw [heq]
                                exact pos_w814 ⟨n - 40700, hr⟩
                              · by_cases h15 : n < 40800
                                · have hr : n - 40750 < 50 := by omega
                                  have heq : n = (n - 40750) + 40750 := by omega
                                  rw [heq]
                                  exact pos_w815 ⟨n - 40750, hr⟩
                                · by_cases h16 : n < 40850
                                  · have hr : n - 40800 < 50 := by omega
                                    have heq : n = (n - 40800) + 40800 := by omega
                                    rw [heq]
                                    exact pos_w816 ⟨n - 40800, hr⟩
                                  · by_cases h17 : n < 40900
                                    · have hr : n - 40850 < 50 := by omega
                                      have heq : n = (n - 40850) + 40850 := by omega
                                      rw [heq]
                                      exact pos_w817 ⟨n - 40850, hr⟩
                                    · by_cases h18 : n < 40950
                                      · have hr : n - 40900 < 50 := by omega
                                        have heq : n = (n - 40900) + 40900 := by omega
                                        rw [heq]
                                        exact pos_w818 ⟨n - 40900, hr⟩
                                      · by_cases h19 : n < 41000
                                        · have hr : n - 40950 < 50 := by omega
                                          have heq : n = (n - 40950) + 40950 := by omega
                                          rw [heq]
                                          exact pos_w819 ⟨n - 40950, hr⟩
                                        · by_cases h20 : n < 41050
                                          · have hr : n - 41000 < 50 := by omega
                                            have heq : n = (n - 41000) + 41000 := by omega
                                            rw [heq]
                                            exact pos_w820 ⟨n - 41000, hr⟩
                                          · by_cases h21 : n < 41100
                                            · have hr : n - 41050 < 50 := by omega
                                              have heq : n = (n - 41050) + 41050 := by omega
                                              rw [heq]
                                              exact pos_w821 ⟨n - 41050, hr⟩
                                            · by_cases h22 : n < 41150
                                              · have hr : n - 41100 < 50 := by omega
                                                have heq : n = (n - 41100) + 41100 := by omega
                                                rw [heq]
                                                exact pos_w822 ⟨n - 41100, hr⟩
                                              · by_cases h23 : n < 41200
                                                · have hr : n - 41150 < 50 := by omega
                                                  have heq : n = (n - 41150) + 41150 := by omega
                                                  rw [heq]
                                                  exact pos_w823 ⟨n - 41150, hr⟩
                                                · by_cases h24 : n < 41250
                                                  · have hr : n - 41200 < 50 := by omega
                                                    have heq : n = (n - 41200) + 41200 := by omega
                                                    rw [heq]
                                                    exact pos_w824 ⟨n - 41200, hr⟩
                                                  · by_cases h25 : n < 41300
                                                    · have hr : n - 41250 < 50 := by omega
                                                      have heq : n = (n - 41250) + 41250 := by omega
                                                      rw [heq]
                                                      exact pos_w825 ⟨n - 41250, hr⟩
                                                    · by_cases h26 : n < 41350
                                                      · have hr : n - 41300 < 50 := by omega
                                                        have heq : n = (n - 41300) + 41300 := by omega
                                                        rw [heq]
                                                        exact pos_w826 ⟨n - 41300, hr⟩
                                                      · by_cases h27 : n < 41400
                                                        · have hr : n - 41350 < 50 := by omega
                                                          have heq : n = (n - 41350) + 41350 := by omega
                                                          rw [heq]
                                                          exact pos_w827 ⟨n - 41350, hr⟩
                                                        · by_cases h28 : n < 41450
                                                          · have hr : n - 41400 < 50 := by omega
                                                            have heq : n = (n - 41400) + 41400 := by omega
                                                            rw [heq]
                                                            exact pos_w828 ⟨n - 41400, hr⟩
                                                          · by_cases h29 : n < 41500
                                                            · have hr : n - 41450 < 50 := by omega
                                                              have heq : n = (n - 41450) + 41450 := by omega
                                                              rw [heq]
                                                              exact pos_w829 ⟨n - 41450, hr⟩
                                                            · by_cases h30 : n < 41550
                                                              · have hr : n - 41500 < 50 := by omega
                                                                have heq : n = (n - 41500) + 41500 := by omega
                                                                rw [heq]
                                                                exact pos_w830 ⟨n - 41500, hr⟩
                                                              · by_cases h31 : n < 41600
                                                                · have hr : n - 41550 < 50 := by omega
                                                                  have heq : n = (n - 41550) + 41550 := by omega
                                                                  rw [heq]
                                                                  exact pos_w831 ⟨n - 41550, hr⟩
                                                                · by_cases h32 : n < 41650
                                                                  · have hr : n - 41600 < 50 := by omega
                                                                    have heq : n = (n - 41600) + 41600 := by omega
                                                                    rw [heq]
                                                                    exact pos_w832 ⟨n - 41600, hr⟩
                                                                  · by_cases h33 : n < 41700
                                                                    · have hr : n - 41650 < 50 := by omega
                                                                      have heq : n = (n - 41650) + 41650 := by omega
                                                                      rw [heq]
                                                                      exact pos_w833 ⟨n - 41650, hr⟩
                                                                    · by_cases h34 : n < 41750
                                                                      · have hr : n - 41700 < 50 := by omega
                                                                        have heq : n = (n - 41700) + 41700 := by omega
                                                                        rw [heq]
                                                                        exact pos_w834 ⟨n - 41700, hr⟩
                                                                      · by_cases h35 : n < 41800
                                                                        · have hr : n - 41750 < 50 := by omega
                                                                          have heq : n = (n - 41750) + 41750 := by omega
                                                                          rw [heq]
                                                                          exact pos_w835 ⟨n - 41750, hr⟩
                                                                        · by_cases h36 : n < 41850
                                                                          · have hr : n - 41800 < 50 := by omega
                                                                            have heq : n = (n - 41800) + 41800 := by omega
                                                                            rw [heq]
                                                                            exact pos_w836 ⟨n - 41800, hr⟩
                                                                          · by_cases h37 : n < 41900
                                                                            · have hr : n - 41850 < 50 := by omega
                                                                              have heq : n = (n - 41850) + 41850 := by omega
                                                                              rw [heq]
                                                                              exact pos_w837 ⟨n - 41850, hr⟩
                                                                            · by_cases h38 : n < 41950
                                                                              · have hr : n - 41900 < 50 := by omega
                                                                                have heq : n = (n - 41900) + 41900 := by omega
                                                                                rw [heq]
                                                                                exact pos_w838 ⟨n - 41900, hr⟩
                                                                              · by_cases h39 : n < 42000
                                                                                · have hr : n - 41950 < 50 := by omega
                                                                                  have heq : n = (n - 41950) + 41950 := by omega
                                                                                  rw [heq]
                                                                                  exact pos_w839 ⟨n - 41950, hr⟩
                                                                                · by_cases h40 : n < 42050
                                                                                  · have hr : n - 42000 < 50 := by omega
                                                                                    have heq : n = (n - 42000) + 42000 := by omega
                                                                                    rw [heq]
                                                                                    exact pos_w840 ⟨n - 42000, hr⟩
                                                                                  · by_cases h41 : n < 42100
                                                                                    · have hr : n - 42050 < 50 := by omega
                                                                                      have heq : n = (n - 42050) + 42050 := by omega
                                                                                      rw [heq]
                                                                                      exact pos_w841 ⟨n - 42050, hr⟩
                                                                                    · by_cases h42 : n < 42150
                                                                                      · have hr : n - 42100 < 50 := by omega
                                                                                        have heq : n = (n - 42100) + 42100 := by omega
                                                                                        rw [heq]
                                                                                        exact pos_w842 ⟨n - 42100, hr⟩
                                                                                      · by_cases h43 : n < 42200
                                                                                        · have hr : n - 42150 < 50 := by omega
                                                                                          have heq : n = (n - 42150) + 42150 := by omega
                                                                                          rw [heq]
                                                                                          exact pos_w843 ⟨n - 42150, hr⟩
                                                                                        · by_cases h44 : n < 42250
                                                                                          · have hr : n - 42200 < 50 := by omega
                                                                                            have heq : n = (n - 42200) + 42200 := by omega
                                                                                            rw [heq]
                                                                                            exact pos_w844 ⟨n - 42200, hr⟩
                                                                                          · by_cases h45 : n < 42300
                                                                                            · have hr : n - 42250 < 50 := by omega
                                                                                              have heq : n = (n - 42250) + 42250 := by omega
                                                                                              rw [heq]
                                                                                              exact pos_w845 ⟨n - 42250, hr⟩
                                                                                            · by_cases h46 : n < 42350
                                                                                              · have hr : n - 42300 < 50 := by omega
                                                                                                have heq : n = (n - 42300) + 42300 := by omega
                                                                                                rw [heq]
                                                                                                exact pos_w846 ⟨n - 42300, hr⟩
                                                                                              · by_cases h47 : n < 42400
                                                                                                · have hr : n - 42350 < 50 := by omega
                                                                                                  have heq : n = (n - 42350) + 42350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact pos_w847 ⟨n - 42350, hr⟩
                                                                                                · by_cases h48 : n < 42450
                                                                                                  · have hr : n - 42400 < 50 := by omega
                                                                                                    have heq : n = (n - 42400) + 42400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact pos_w848 ⟨n - 42400, hr⟩
                                                                                                  · by_cases h49 : n < 42500
                                                                                                    · have hr : n - 42450 < 50 := by omega
                                                                                                      have heq : n = (n - 42450) + 42450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact pos_w849 ⟨n - 42450, hr⟩
                                                                                                    · by_cases h50 : n < 42550
                                                                                                      · have hr : n - 42500 < 50 := by omega
                                                                                                        have heq : n = (n - 42500) + 42500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact pos_w850 ⟨n - 42500, hr⟩
                                                                                                      · by_cases h51 : n < 42600
                                                                                                        · have hr : n - 42550 < 50 := by omega
                                                                                                          have heq : n = (n - 42550) + 42550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact pos_w851 ⟨n - 42550, hr⟩
                                                                                                        · by_cases h52 : n < 42650
                                                                                                          · have hr : n - 42600 < 50 := by omega
                                                                                                            have heq : n = (n - 42600) + 42600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact pos_w852 ⟨n - 42600, hr⟩
                                                                                                          · by_cases h53 : n < 42700
                                                                                                            · have hr : n - 42650 < 50 := by omega
                                                                                                              have heq : n = (n - 42650) + 42650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact pos_w853 ⟨n - 42650, hr⟩
                                                                                                            · by_cases h54 : n < 42750
                                                                                                              · have hr : n - 42700 < 50 := by omega
                                                                                                                have heq : n = (n - 42700) + 42700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact pos_w854 ⟨n - 42700, hr⟩
                                                                                                              · by_cases h55 : n < 42800
                                                                                                                · have hr : n - 42750 < 50 := by omega
                                                                                                                  have heq : n = (n - 42750) + 42750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact pos_w855 ⟨n - 42750, hr⟩
                                                                                                                · by_cases h56 : n < 42850
                                                                                                                  · have hr : n - 42800 < 50 := by omega
                                                                                                                    have heq : n = (n - 42800) + 42800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact pos_w856 ⟨n - 42800, hr⟩
                                                                                                                  · by_cases h57 : n < 42900
                                                                                                                    · have hr : n - 42850 < 50 := by omega
                                                                                                                      have heq : n = (n - 42850) + 42850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact pos_w857 ⟨n - 42850, hr⟩
                                                                                                                    · by_cases h58 : n < 42950
                                                                                                                      · have hr : n - 42900 < 50 := by omega
                                                                                                                        have heq : n = (n - 42900) + 42900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact pos_w858 ⟨n - 42900, hr⟩
                                                                                                                      · by_cases h59 : n < 43000
                                                                                                                        · have hr : n - 42950 < 50 := by omega
                                                                                                                          have heq : n = (n - 42950) + 42950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact pos_w859 ⟨n - 42950, hr⟩
                                                                                                                        · by_cases h60 : n < 43050
                                                                                                                          · have hr : n - 43000 < 50 := by omega
                                                                                                                            have heq : n = (n - 43000) + 43000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact pos_w860 ⟨n - 43000, hr⟩
                                                                                                                          · by_cases h61 : n < 43100
                                                                                                                            · have hr : n - 43050 < 50 := by omega
                                                                                                                              have heq : n = (n - 43050) + 43050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact pos_w861 ⟨n - 43050, hr⟩
                                                                                                                            · by_cases h62 : n < 43150
                                                                                                                              · have hr : n - 43100 < 50 := by omega
                                                                                                                                have heq : n = (n - 43100) + 43100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact pos_w862 ⟨n - 43100, hr⟩
                                                                                                                              · by_cases h63 : n < 43200
                                                                                                                                · have hr : n - 43150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 43150) + 43150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact pos_w863 ⟨n - 43150, hr⟩
                                                                                                                                · by_cases h64 : n < 43250
                                                                                                                                  · have hr : n - 43200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 43200) + 43200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact pos_w864 ⟨n - 43200, hr⟩
                                                                                                                                  · by_cases h65 : n < 43300
                                                                                                                                    · have hr : n - 43250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 43250) + 43250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact pos_w865 ⟨n - 43250, hr⟩
                                                                                                                                    · by_cases h66 : n < 43350
                                                                                                                                      · have hr : n - 43300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 43300) + 43300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact pos_w866 ⟨n - 43300, hr⟩
                                                                                                                                      · by_cases h67 : n < 43400
                                                                                                                                        · have hr : n - 43350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 43350) + 43350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact pos_w867 ⟨n - 43350, hr⟩
                                                                                                                                        · by_cases h68 : n < 43450
                                                                                                                                          · have hr : n - 43400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 43400) + 43400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact pos_w868 ⟨n - 43400, hr⟩
                                                                                                                                          · by_cases h69 : n < 43500
                                                                                                                                            · have hr : n - 43450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 43450) + 43450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact pos_w869 ⟨n - 43450, hr⟩
                                                                                                                                            · by_cases h70 : n < 43550
                                                                                                                                              · have hr : n - 43500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 43500) + 43500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact pos_w870 ⟨n - 43500, hr⟩
                                                                                                                                              · by_cases h71 : n < 43600
                                                                                                                                                · have hr : n - 43550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 43550) + 43550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact pos_w871 ⟨n - 43550, hr⟩
                                                                                                                                                · by_cases h72 : n < 43650
                                                                                                                                                  · have hr : n - 43600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 43600) + 43600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact pos_w872 ⟨n - 43600, hr⟩
                                                                                                                                                  · by_cases h73 : n < 43700
                                                                                                                                                    · have hr : n - 43650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 43650) + 43650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact pos_w873 ⟨n - 43650, hr⟩
                                                                                                                                                    · by_cases h74 : n < 43750
                                                                                                                                                      · have hr : n - 43700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 43700) + 43700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact pos_w874 ⟨n - 43700, hr⟩
                                                                                                                                                      · by_cases h75 : n < 43800
                                                                                                                                                        · have hr : n - 43750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 43750) + 43750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact pos_w875 ⟨n - 43750, hr⟩
                                                                                                                                                        · by_cases h76 : n < 43850
                                                                                                                                                          · have hr : n - 43800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 43800) + 43800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact pos_w876 ⟨n - 43800, hr⟩
                                                                                                                                                          · by_cases h77 : n < 43900
                                                                                                                                                            · have hr : n - 43850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 43850) + 43850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact pos_w877 ⟨n - 43850, hr⟩
                                                                                                                                                            · by_cases h78 : n < 43950
                                                                                                                                                              · have hr : n - 43900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 43900) + 43900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact pos_w878 ⟨n - 43900, hr⟩
                                                                                                                                                              · by_cases h79 : n < 44000
                                                                                                                                                                · have hr : n - 43950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 43950) + 43950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact pos_w879 ⟨n - 43950, hr⟩
                                                                                                                                                                · by_cases h80 : n < 44050
                                                                                                                                                                  · have hr : n - 44000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 44000) + 44000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact pos_w880 ⟨n - 44000, hr⟩
                                                                                                                                                                  · by_cases h81 : n < 44100
                                                                                                                                                                    · have hr : n - 44050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 44050) + 44050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact pos_w881 ⟨n - 44050, hr⟩
                                                                                                                                                                    · by_cases h82 : n < 44150
                                                                                                                                                                      · have hr : n - 44100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 44100) + 44100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact pos_w882 ⟨n - 44100, hr⟩
                                                                                                                                                                      · by_cases h83 : n < 44200
                                                                                                                                                                        · have hr : n - 44150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 44150) + 44150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact pos_w883 ⟨n - 44150, hr⟩
                                                                                                                                                                        · by_cases h84 : n < 44250
                                                                                                                                                                          · have hr : n - 44200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 44200) + 44200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact pos_w884 ⟨n - 44200, hr⟩
                                                                                                                                                                          · by_cases h85 : n < 44300
                                                                                                                                                                            · have hr : n - 44250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 44250) + 44250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact pos_w885 ⟨n - 44250, hr⟩
                                                                                                                                                                            · by_cases h86 : n < 44350
                                                                                                                                                                              · have hr : n - 44300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 44300) + 44300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact pos_w886 ⟨n - 44300, hr⟩
                                                                                                                                                                              · by_cases h87 : n < 44400
                                                                                                                                                                                · have hr : n - 44350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 44350) + 44350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact pos_w887 ⟨n - 44350, hr⟩
                                                                                                                                                                                · by_cases h88 : n < 44450
                                                                                                                                                                                  · have hr : n - 44400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 44400) + 44400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact pos_w888 ⟨n - 44400, hr⟩
                                                                                                                                                                                  · by_cases h89 : n < 44500
                                                                                                                                                                                    · have hr : n - 44450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 44450) + 44450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact pos_w889 ⟨n - 44450, hr⟩
                                                                                                                                                                                    · by_cases h90 : n < 44550
                                                                                                                                                                                      · have hr : n - 44500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 44500) + 44500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact pos_w890 ⟨n - 44500, hr⟩
                                                                                                                                                                                      · by_cases h91 : n < 44600
                                                                                                                                                                                        · have hr : n - 44550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 44550) + 44550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact pos_w891 ⟨n - 44550, hr⟩
                                                                                                                                                                                        · by_cases h92 : n < 44650
                                                                                                                                                                                          · have hr : n - 44600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 44600) + 44600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact pos_w892 ⟨n - 44600, hr⟩
                                                                                                                                                                                          · by_cases h93 : n < 44700
                                                                                                                                                                                            · have hr : n - 44650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 44650) + 44650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact pos_w893 ⟨n - 44650, hr⟩
                                                                                                                                                                                            · by_cases h94 : n < 44750
                                                                                                                                                                                              · have hr : n - 44700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 44700) + 44700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact pos_w894 ⟨n - 44700, hr⟩
                                                                                                                                                                                              · by_cases h95 : n < 44800
                                                                                                                                                                                                · have hr : n - 44750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 44750) + 44750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact pos_w895 ⟨n - 44750, hr⟩
                                                                                                                                                                                                · by_cases h96 : n < 44850
                                                                                                                                                                                                  · have hr : n - 44800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 44800) + 44800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact pos_w896 ⟨n - 44800, hr⟩
                                                                                                                                                                                                  · by_cases h97 : n < 44900
                                                                                                                                                                                                    · have hr : n - 44850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 44850) + 44850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact pos_w897 ⟨n - 44850, hr⟩
                                                                                                                                                                                                    · by_cases h98 : n < 44950
                                                                                                                                                                                                      · have hr : n - 44900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 44900) + 44900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact pos_w898 ⟨n - 44900, hr⟩
                                                                                                                                                                                                      · by_cases h99 : n < 45000
                                                                                                                                                                                                        · have hr : n - 44950 < 50 := by omega
                                                                                                                                                                                                          have heq : n = (n - 44950) + 44950 := by omega
                                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                                          exact pos_w899 ⟨n - 44950, hr⟩
                                                                                                                                                                                                        · omega

end IntMul.Kappa.R8.Bit.Oppbank.DimBound8


