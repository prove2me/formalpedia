-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound10
-- name    : IntMul_Kappa_R8_Data_BitOppbankDimBound10
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:03:01.428929+00:00
-- url     : https://prove2.me/theorems/18f4f154-6b19-485d-8097-d10ac1649de8
-- title:
--   Densified dimF $\le 22$ pack 10 ($[50000,55000)$)
-- statement:
--   Pack 10 of the densified dimension-field bound.
--
--   For every densified node index $n$ with $50000\le n<55000$, the 5-bit field $\mathrm{dimF}(n)$ extracted from $\mathrm{DIMT}$ satisfies
--   $$1\le \mathrm{dimF}(n)\le 22.$$
--   Proved by `decide` on successive `Fin 50` windows (no `native_decide`).
-- source:
--   R8 BitNB densified DIMT field bound; Fin-window decide packs

-- DimBound pack 10: dimF bounds on n ∈ [50000, 55000)

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

namespace IntMul.Kappa.R8.Bit.Oppbank.DimBound10

private theorem le_w1000 : ∀ n : Fin 50, dimF (n.val + 50000) ≤ 22 := by decide
private theorem pos_w1000 : ∀ n : Fin 50, 0 < dimF (n.val + 50000) := by decide
private theorem le_w1001 : ∀ n : Fin 50, dimF (n.val + 50050) ≤ 22 := by decide
private theorem pos_w1001 : ∀ n : Fin 50, 0 < dimF (n.val + 50050) := by decide
private theorem le_w1002 : ∀ n : Fin 50, dimF (n.val + 50100) ≤ 22 := by decide
private theorem pos_w1002 : ∀ n : Fin 50, 0 < dimF (n.val + 50100) := by decide
private theorem le_w1003 : ∀ n : Fin 50, dimF (n.val + 50150) ≤ 22 := by decide
private theorem pos_w1003 : ∀ n : Fin 50, 0 < dimF (n.val + 50150) := by decide
private theorem le_w1004 : ∀ n : Fin 50, dimF (n.val + 50200) ≤ 22 := by decide
private theorem pos_w1004 : ∀ n : Fin 50, 0 < dimF (n.val + 50200) := by decide
private theorem le_w1005 : ∀ n : Fin 50, dimF (n.val + 50250) ≤ 22 := by decide
private theorem pos_w1005 : ∀ n : Fin 50, 0 < dimF (n.val + 50250) := by decide
private theorem le_w1006 : ∀ n : Fin 50, dimF (n.val + 50300) ≤ 22 := by decide
private theorem pos_w1006 : ∀ n : Fin 50, 0 < dimF (n.val + 50300) := by decide
private theorem le_w1007 : ∀ n : Fin 50, dimF (n.val + 50350) ≤ 22 := by decide
private theorem pos_w1007 : ∀ n : Fin 50, 0 < dimF (n.val + 50350) := by decide
private theorem le_w1008 : ∀ n : Fin 50, dimF (n.val + 50400) ≤ 22 := by decide
private theorem pos_w1008 : ∀ n : Fin 50, 0 < dimF (n.val + 50400) := by decide
private theorem le_w1009 : ∀ n : Fin 50, dimF (n.val + 50450) ≤ 22 := by decide
private theorem pos_w1009 : ∀ n : Fin 50, 0 < dimF (n.val + 50450) := by decide
private theorem le_w1010 : ∀ n : Fin 50, dimF (n.val + 50500) ≤ 22 := by decide
private theorem pos_w1010 : ∀ n : Fin 50, 0 < dimF (n.val + 50500) := by decide
private theorem le_w1011 : ∀ n : Fin 50, dimF (n.val + 50550) ≤ 22 := by decide
private theorem pos_w1011 : ∀ n : Fin 50, 0 < dimF (n.val + 50550) := by decide
private theorem le_w1012 : ∀ n : Fin 50, dimF (n.val + 50600) ≤ 22 := by decide
private theorem pos_w1012 : ∀ n : Fin 50, 0 < dimF (n.val + 50600) := by decide
private theorem le_w1013 : ∀ n : Fin 50, dimF (n.val + 50650) ≤ 22 := by decide
private theorem pos_w1013 : ∀ n : Fin 50, 0 < dimF (n.val + 50650) := by decide
private theorem le_w1014 : ∀ n : Fin 50, dimF (n.val + 50700) ≤ 22 := by decide
private theorem pos_w1014 : ∀ n : Fin 50, 0 < dimF (n.val + 50700) := by decide
private theorem le_w1015 : ∀ n : Fin 50, dimF (n.val + 50750) ≤ 22 := by decide
private theorem pos_w1015 : ∀ n : Fin 50, 0 < dimF (n.val + 50750) := by decide
private theorem le_w1016 : ∀ n : Fin 50, dimF (n.val + 50800) ≤ 22 := by decide
private theorem pos_w1016 : ∀ n : Fin 50, 0 < dimF (n.val + 50800) := by decide
private theorem le_w1017 : ∀ n : Fin 50, dimF (n.val + 50850) ≤ 22 := by decide
private theorem pos_w1017 : ∀ n : Fin 50, 0 < dimF (n.val + 50850) := by decide
private theorem le_w1018 : ∀ n : Fin 50, dimF (n.val + 50900) ≤ 22 := by decide
private theorem pos_w1018 : ∀ n : Fin 50, 0 < dimF (n.val + 50900) := by decide
private theorem le_w1019 : ∀ n : Fin 50, dimF (n.val + 50950) ≤ 22 := by decide
private theorem pos_w1019 : ∀ n : Fin 50, 0 < dimF (n.val + 50950) := by decide
private theorem le_w1020 : ∀ n : Fin 50, dimF (n.val + 51000) ≤ 22 := by decide
private theorem pos_w1020 : ∀ n : Fin 50, 0 < dimF (n.val + 51000) := by decide
private theorem le_w1021 : ∀ n : Fin 50, dimF (n.val + 51050) ≤ 22 := by decide
private theorem pos_w1021 : ∀ n : Fin 50, 0 < dimF (n.val + 51050) := by decide
private theorem le_w1022 : ∀ n : Fin 50, dimF (n.val + 51100) ≤ 22 := by decide
private theorem pos_w1022 : ∀ n : Fin 50, 0 < dimF (n.val + 51100) := by decide
private theorem le_w1023 : ∀ n : Fin 50, dimF (n.val + 51150) ≤ 22 := by decide
private theorem pos_w1023 : ∀ n : Fin 50, 0 < dimF (n.val + 51150) := by decide
private theorem le_w1024 : ∀ n : Fin 50, dimF (n.val + 51200) ≤ 22 := by decide
private theorem pos_w1024 : ∀ n : Fin 50, 0 < dimF (n.val + 51200) := by decide
private theorem le_w1025 : ∀ n : Fin 50, dimF (n.val + 51250) ≤ 22 := by decide
private theorem pos_w1025 : ∀ n : Fin 50, 0 < dimF (n.val + 51250) := by decide
private theorem le_w1026 : ∀ n : Fin 50, dimF (n.val + 51300) ≤ 22 := by decide
private theorem pos_w1026 : ∀ n : Fin 50, 0 < dimF (n.val + 51300) := by decide
private theorem le_w1027 : ∀ n : Fin 50, dimF (n.val + 51350) ≤ 22 := by decide
private theorem pos_w1027 : ∀ n : Fin 50, 0 < dimF (n.val + 51350) := by decide
private theorem le_w1028 : ∀ n : Fin 50, dimF (n.val + 51400) ≤ 22 := by decide
private theorem pos_w1028 : ∀ n : Fin 50, 0 < dimF (n.val + 51400) := by decide
private theorem le_w1029 : ∀ n : Fin 50, dimF (n.val + 51450) ≤ 22 := by decide
private theorem pos_w1029 : ∀ n : Fin 50, 0 < dimF (n.val + 51450) := by decide
private theorem le_w1030 : ∀ n : Fin 50, dimF (n.val + 51500) ≤ 22 := by decide
private theorem pos_w1030 : ∀ n : Fin 50, 0 < dimF (n.val + 51500) := by decide
private theorem le_w1031 : ∀ n : Fin 50, dimF (n.val + 51550) ≤ 22 := by decide
private theorem pos_w1031 : ∀ n : Fin 50, 0 < dimF (n.val + 51550) := by decide
private theorem le_w1032 : ∀ n : Fin 50, dimF (n.val + 51600) ≤ 22 := by decide
private theorem pos_w1032 : ∀ n : Fin 50, 0 < dimF (n.val + 51600) := by decide
private theorem le_w1033 : ∀ n : Fin 50, dimF (n.val + 51650) ≤ 22 := by decide
private theorem pos_w1033 : ∀ n : Fin 50, 0 < dimF (n.val + 51650) := by decide
private theorem le_w1034 : ∀ n : Fin 50, dimF (n.val + 51700) ≤ 22 := by decide
private theorem pos_w1034 : ∀ n : Fin 50, 0 < dimF (n.val + 51700) := by decide
private theorem le_w1035 : ∀ n : Fin 50, dimF (n.val + 51750) ≤ 22 := by decide
private theorem pos_w1035 : ∀ n : Fin 50, 0 < dimF (n.val + 51750) := by decide
private theorem le_w1036 : ∀ n : Fin 50, dimF (n.val + 51800) ≤ 22 := by decide
private theorem pos_w1036 : ∀ n : Fin 50, 0 < dimF (n.val + 51800) := by decide
private theorem le_w1037 : ∀ n : Fin 50, dimF (n.val + 51850) ≤ 22 := by decide
private theorem pos_w1037 : ∀ n : Fin 50, 0 < dimF (n.val + 51850) := by decide
private theorem le_w1038 : ∀ n : Fin 50, dimF (n.val + 51900) ≤ 22 := by decide
private theorem pos_w1038 : ∀ n : Fin 50, 0 < dimF (n.val + 51900) := by decide
private theorem le_w1039 : ∀ n : Fin 50, dimF (n.val + 51950) ≤ 22 := by decide
private theorem pos_w1039 : ∀ n : Fin 50, 0 < dimF (n.val + 51950) := by decide
private theorem le_w1040 : ∀ n : Fin 50, dimF (n.val + 52000) ≤ 22 := by decide
private theorem pos_w1040 : ∀ n : Fin 50, 0 < dimF (n.val + 52000) := by decide
private theorem le_w1041 : ∀ n : Fin 50, dimF (n.val + 52050) ≤ 22 := by decide
private theorem pos_w1041 : ∀ n : Fin 50, 0 < dimF (n.val + 52050) := by decide
private theorem le_w1042 : ∀ n : Fin 50, dimF (n.val + 52100) ≤ 22 := by decide
private theorem pos_w1042 : ∀ n : Fin 50, 0 < dimF (n.val + 52100) := by decide
private theorem le_w1043 : ∀ n : Fin 50, dimF (n.val + 52150) ≤ 22 := by decide
private theorem pos_w1043 : ∀ n : Fin 50, 0 < dimF (n.val + 52150) := by decide
private theorem le_w1044 : ∀ n : Fin 50, dimF (n.val + 52200) ≤ 22 := by decide
private theorem pos_w1044 : ∀ n : Fin 50, 0 < dimF (n.val + 52200) := by decide
private theorem le_w1045 : ∀ n : Fin 50, dimF (n.val + 52250) ≤ 22 := by decide
private theorem pos_w1045 : ∀ n : Fin 50, 0 < dimF (n.val + 52250) := by decide
private theorem le_w1046 : ∀ n : Fin 50, dimF (n.val + 52300) ≤ 22 := by decide
private theorem pos_w1046 : ∀ n : Fin 50, 0 < dimF (n.val + 52300) := by decide
private theorem le_w1047 : ∀ n : Fin 50, dimF (n.val + 52350) ≤ 22 := by decide
private theorem pos_w1047 : ∀ n : Fin 50, 0 < dimF (n.val + 52350) := by decide
private theorem le_w1048 : ∀ n : Fin 50, dimF (n.val + 52400) ≤ 22 := by decide
private theorem pos_w1048 : ∀ n : Fin 50, 0 < dimF (n.val + 52400) := by decide
private theorem le_w1049 : ∀ n : Fin 50, dimF (n.val + 52450) ≤ 22 := by decide
private theorem pos_w1049 : ∀ n : Fin 50, 0 < dimF (n.val + 52450) := by decide
private theorem le_w1050 : ∀ n : Fin 50, dimF (n.val + 52500) ≤ 22 := by decide
private theorem pos_w1050 : ∀ n : Fin 50, 0 < dimF (n.val + 52500) := by decide
private theorem le_w1051 : ∀ n : Fin 50, dimF (n.val + 52550) ≤ 22 := by decide
private theorem pos_w1051 : ∀ n : Fin 50, 0 < dimF (n.val + 52550) := by decide
private theorem le_w1052 : ∀ n : Fin 50, dimF (n.val + 52600) ≤ 22 := by decide
private theorem pos_w1052 : ∀ n : Fin 50, 0 < dimF (n.val + 52600) := by decide
private theorem le_w1053 : ∀ n : Fin 50, dimF (n.val + 52650) ≤ 22 := by decide
private theorem pos_w1053 : ∀ n : Fin 50, 0 < dimF (n.val + 52650) := by decide
private theorem le_w1054 : ∀ n : Fin 50, dimF (n.val + 52700) ≤ 22 := by decide
private theorem pos_w1054 : ∀ n : Fin 50, 0 < dimF (n.val + 52700) := by decide
private theorem le_w1055 : ∀ n : Fin 50, dimF (n.val + 52750) ≤ 22 := by decide
private theorem pos_w1055 : ∀ n : Fin 50, 0 < dimF (n.val + 52750) := by decide
private theorem le_w1056 : ∀ n : Fin 50, dimF (n.val + 52800) ≤ 22 := by decide
private theorem pos_w1056 : ∀ n : Fin 50, 0 < dimF (n.val + 52800) := by decide
private theorem le_w1057 : ∀ n : Fin 50, dimF (n.val + 52850) ≤ 22 := by decide
private theorem pos_w1057 : ∀ n : Fin 50, 0 < dimF (n.val + 52850) := by decide
private theorem le_w1058 : ∀ n : Fin 50, dimF (n.val + 52900) ≤ 22 := by decide
private theorem pos_w1058 : ∀ n : Fin 50, 0 < dimF (n.val + 52900) := by decide
private theorem le_w1059 : ∀ n : Fin 50, dimF (n.val + 52950) ≤ 22 := by decide
private theorem pos_w1059 : ∀ n : Fin 50, 0 < dimF (n.val + 52950) := by decide
private theorem le_w1060 : ∀ n : Fin 50, dimF (n.val + 53000) ≤ 22 := by decide
private theorem pos_w1060 : ∀ n : Fin 50, 0 < dimF (n.val + 53000) := by decide
private theorem le_w1061 : ∀ n : Fin 50, dimF (n.val + 53050) ≤ 22 := by decide
private theorem pos_w1061 : ∀ n : Fin 50, 0 < dimF (n.val + 53050) := by decide
private theorem le_w1062 : ∀ n : Fin 50, dimF (n.val + 53100) ≤ 22 := by decide
private theorem pos_w1062 : ∀ n : Fin 50, 0 < dimF (n.val + 53100) := by decide
private theorem le_w1063 : ∀ n : Fin 50, dimF (n.val + 53150) ≤ 22 := by decide
private theorem pos_w1063 : ∀ n : Fin 50, 0 < dimF (n.val + 53150) := by decide
private theorem le_w1064 : ∀ n : Fin 50, dimF (n.val + 53200) ≤ 22 := by decide
private theorem pos_w1064 : ∀ n : Fin 50, 0 < dimF (n.val + 53200) := by decide
private theorem le_w1065 : ∀ n : Fin 50, dimF (n.val + 53250) ≤ 22 := by decide
private theorem pos_w1065 : ∀ n : Fin 50, 0 < dimF (n.val + 53250) := by decide
private theorem le_w1066 : ∀ n : Fin 50, dimF (n.val + 53300) ≤ 22 := by decide
private theorem pos_w1066 : ∀ n : Fin 50, 0 < dimF (n.val + 53300) := by decide
private theorem le_w1067 : ∀ n : Fin 50, dimF (n.val + 53350) ≤ 22 := by decide
private theorem pos_w1067 : ∀ n : Fin 50, 0 < dimF (n.val + 53350) := by decide
private theorem le_w1068 : ∀ n : Fin 50, dimF (n.val + 53400) ≤ 22 := by decide
private theorem pos_w1068 : ∀ n : Fin 50, 0 < dimF (n.val + 53400) := by decide
private theorem le_w1069 : ∀ n : Fin 50, dimF (n.val + 53450) ≤ 22 := by decide
private theorem pos_w1069 : ∀ n : Fin 50, 0 < dimF (n.val + 53450) := by decide
private theorem le_w1070 : ∀ n : Fin 50, dimF (n.val + 53500) ≤ 22 := by decide
private theorem pos_w1070 : ∀ n : Fin 50, 0 < dimF (n.val + 53500) := by decide
private theorem le_w1071 : ∀ n : Fin 50, dimF (n.val + 53550) ≤ 22 := by decide
private theorem pos_w1071 : ∀ n : Fin 50, 0 < dimF (n.val + 53550) := by decide
private theorem le_w1072 : ∀ n : Fin 50, dimF (n.val + 53600) ≤ 22 := by decide
private theorem pos_w1072 : ∀ n : Fin 50, 0 < dimF (n.val + 53600) := by decide
private theorem le_w1073 : ∀ n : Fin 50, dimF (n.val + 53650) ≤ 22 := by decide
private theorem pos_w1073 : ∀ n : Fin 50, 0 < dimF (n.val + 53650) := by decide
private theorem le_w1074 : ∀ n : Fin 50, dimF (n.val + 53700) ≤ 22 := by decide
private theorem pos_w1074 : ∀ n : Fin 50, 0 < dimF (n.val + 53700) := by decide
private theorem le_w1075 : ∀ n : Fin 50, dimF (n.val + 53750) ≤ 22 := by decide
private theorem pos_w1075 : ∀ n : Fin 50, 0 < dimF (n.val + 53750) := by decide
private theorem le_w1076 : ∀ n : Fin 50, dimF (n.val + 53800) ≤ 22 := by decide
private theorem pos_w1076 : ∀ n : Fin 50, 0 < dimF (n.val + 53800) := by decide
private theorem le_w1077 : ∀ n : Fin 50, dimF (n.val + 53850) ≤ 22 := by decide
private theorem pos_w1077 : ∀ n : Fin 50, 0 < dimF (n.val + 53850) := by decide
private theorem le_w1078 : ∀ n : Fin 50, dimF (n.val + 53900) ≤ 22 := by decide
private theorem pos_w1078 : ∀ n : Fin 50, 0 < dimF (n.val + 53900) := by decide
private theorem le_w1079 : ∀ n : Fin 50, dimF (n.val + 53950) ≤ 22 := by decide
private theorem pos_w1079 : ∀ n : Fin 50, 0 < dimF (n.val + 53950) := by decide
private theorem le_w1080 : ∀ n : Fin 50, dimF (n.val + 54000) ≤ 22 := by decide
private theorem pos_w1080 : ∀ n : Fin 50, 0 < dimF (n.val + 54000) := by decide
private theorem le_w1081 : ∀ n : Fin 50, dimF (n.val + 54050) ≤ 22 := by decide
private theorem pos_w1081 : ∀ n : Fin 50, 0 < dimF (n.val + 54050) := by decide
private theorem le_w1082 : ∀ n : Fin 50, dimF (n.val + 54100) ≤ 22 := by decide
private theorem pos_w1082 : ∀ n : Fin 50, 0 < dimF (n.val + 54100) := by decide
private theorem le_w1083 : ∀ n : Fin 50, dimF (n.val + 54150) ≤ 22 := by decide
private theorem pos_w1083 : ∀ n : Fin 50, 0 < dimF (n.val + 54150) := by decide
private theorem le_w1084 : ∀ n : Fin 50, dimF (n.val + 54200) ≤ 22 := by decide
private theorem pos_w1084 : ∀ n : Fin 50, 0 < dimF (n.val + 54200) := by decide
private theorem le_w1085 : ∀ n : Fin 50, dimF (n.val + 54250) ≤ 22 := by decide
private theorem pos_w1085 : ∀ n : Fin 50, 0 < dimF (n.val + 54250) := by decide
private theorem le_w1086 : ∀ n : Fin 50, dimF (n.val + 54300) ≤ 22 := by decide
private theorem pos_w1086 : ∀ n : Fin 50, 0 < dimF (n.val + 54300) := by decide
private theorem le_w1087 : ∀ n : Fin 50, dimF (n.val + 54350) ≤ 22 := by decide
private theorem pos_w1087 : ∀ n : Fin 50, 0 < dimF (n.val + 54350) := by decide
private theorem le_w1088 : ∀ n : Fin 50, dimF (n.val + 54400) ≤ 22 := by decide
private theorem pos_w1088 : ∀ n : Fin 50, 0 < dimF (n.val + 54400) := by decide
private theorem le_w1089 : ∀ n : Fin 50, dimF (n.val + 54450) ≤ 22 := by decide
private theorem pos_w1089 : ∀ n : Fin 50, 0 < dimF (n.val + 54450) := by decide
private theorem le_w1090 : ∀ n : Fin 50, dimF (n.val + 54500) ≤ 22 := by decide
private theorem pos_w1090 : ∀ n : Fin 50, 0 < dimF (n.val + 54500) := by decide
private theorem le_w1091 : ∀ n : Fin 50, dimF (n.val + 54550) ≤ 22 := by decide
private theorem pos_w1091 : ∀ n : Fin 50, 0 < dimF (n.val + 54550) := by decide
private theorem le_w1092 : ∀ n : Fin 50, dimF (n.val + 54600) ≤ 22 := by decide
private theorem pos_w1092 : ∀ n : Fin 50, 0 < dimF (n.val + 54600) := by decide
private theorem le_w1093 : ∀ n : Fin 50, dimF (n.val + 54650) ≤ 22 := by decide
private theorem pos_w1093 : ∀ n : Fin 50, 0 < dimF (n.val + 54650) := by decide
private theorem le_w1094 : ∀ n : Fin 50, dimF (n.val + 54700) ≤ 22 := by decide
private theorem pos_w1094 : ∀ n : Fin 50, 0 < dimF (n.val + 54700) := by decide
private theorem le_w1095 : ∀ n : Fin 50, dimF (n.val + 54750) ≤ 22 := by decide
private theorem pos_w1095 : ∀ n : Fin 50, 0 < dimF (n.val + 54750) := by decide
private theorem le_w1096 : ∀ n : Fin 50, dimF (n.val + 54800) ≤ 22 := by decide
private theorem pos_w1096 : ∀ n : Fin 50, 0 < dimF (n.val + 54800) := by decide
private theorem le_w1097 : ∀ n : Fin 50, dimF (n.val + 54850) ≤ 22 := by decide
private theorem pos_w1097 : ∀ n : Fin 50, 0 < dimF (n.val + 54850) := by decide
private theorem le_w1098 : ∀ n : Fin 50, dimF (n.val + 54900) ≤ 22 := by decide
private theorem pos_w1098 : ∀ n : Fin 50, 0 < dimF (n.val + 54900) := by decide
private theorem le_w1099 : ∀ n : Fin 50, dimF (n.val + 54950) ≤ 22 := by decide
private theorem pos_w1099 : ∀ n : Fin 50, 0 < dimF (n.val + 54950) := by decide

theorem dimF_le_22_range : ∀ n, 50000 ≤ n → n < 55000 → dimF n ≤ 22 := by
  intro n hlo hhi
  by_cases h0 : n < 50050
  · have hr : n - 50000 < 50 := by omega
    have heq : n = (n - 50000) + 50000 := by omega
    rw [heq]
    exact le_w1000 ⟨n - 50000, hr⟩
  · by_cases h1 : n < 50100
    · have hr : n - 50050 < 50 := by omega
      have heq : n = (n - 50050) + 50050 := by omega
      rw [heq]
      exact le_w1001 ⟨n - 50050, hr⟩
    · by_cases h2 : n < 50150
      · have hr : n - 50100 < 50 := by omega
        have heq : n = (n - 50100) + 50100 := by omega
        rw [heq]
        exact le_w1002 ⟨n - 50100, hr⟩
      · by_cases h3 : n < 50200
        · have hr : n - 50150 < 50 := by omega
          have heq : n = (n - 50150) + 50150 := by omega
          rw [heq]
          exact le_w1003 ⟨n - 50150, hr⟩
        · by_cases h4 : n < 50250
          · have hr : n - 50200 < 50 := by omega
            have heq : n = (n - 50200) + 50200 := by omega
            rw [heq]
            exact le_w1004 ⟨n - 50200, hr⟩
          · by_cases h5 : n < 50300
            · have hr : n - 50250 < 50 := by omega
              have heq : n = (n - 50250) + 50250 := by omega
              rw [heq]
              exact le_w1005 ⟨n - 50250, hr⟩
            · by_cases h6 : n < 50350
              · have hr : n - 50300 < 50 := by omega
                have heq : n = (n - 50300) + 50300 := by omega
                rw [heq]
                exact le_w1006 ⟨n - 50300, hr⟩
              · by_cases h7 : n < 50400
                · have hr : n - 50350 < 50 := by omega
                  have heq : n = (n - 50350) + 50350 := by omega
                  rw [heq]
                  exact le_w1007 ⟨n - 50350, hr⟩
                · by_cases h8 : n < 50450
                  · have hr : n - 50400 < 50 := by omega
                    have heq : n = (n - 50400) + 50400 := by omega
                    rw [heq]
                    exact le_w1008 ⟨n - 50400, hr⟩
                  · by_cases h9 : n < 50500
                    · have hr : n - 50450 < 50 := by omega
                      have heq : n = (n - 50450) + 50450 := by omega
                      rw [heq]
                      exact le_w1009 ⟨n - 50450, hr⟩
                    · by_cases h10 : n < 50550
                      · have hr : n - 50500 < 50 := by omega
                        have heq : n = (n - 50500) + 50500 := by omega
                        rw [heq]
                        exact le_w1010 ⟨n - 50500, hr⟩
                      · by_cases h11 : n < 50600
                        · have hr : n - 50550 < 50 := by omega
                          have heq : n = (n - 50550) + 50550 := by omega
                          rw [heq]
                          exact le_w1011 ⟨n - 50550, hr⟩
                        · by_cases h12 : n < 50650
                          · have hr : n - 50600 < 50 := by omega
                            have heq : n = (n - 50600) + 50600 := by omega
                            rw [heq]
                            exact le_w1012 ⟨n - 50600, hr⟩
                          · by_cases h13 : n < 50700
                            · have hr : n - 50650 < 50 := by omega
                              have heq : n = (n - 50650) + 50650 := by omega
                              rw [heq]
                              exact le_w1013 ⟨n - 50650, hr⟩
                            · by_cases h14 : n < 50750
                              · have hr : n - 50700 < 50 := by omega
                                have heq : n = (n - 50700) + 50700 := by omega
                                rw [heq]
                                exact le_w1014 ⟨n - 50700, hr⟩
                              · by_cases h15 : n < 50800
                                · have hr : n - 50750 < 50 := by omega
                                  have heq : n = (n - 50750) + 50750 := by omega
                                  rw [heq]
                                  exact le_w1015 ⟨n - 50750, hr⟩
                                · by_cases h16 : n < 50850
                                  · have hr : n - 50800 < 50 := by omega
                                    have heq : n = (n - 50800) + 50800 := by omega
                                    rw [heq]
                                    exact le_w1016 ⟨n - 50800, hr⟩
                                  · by_cases h17 : n < 50900
                                    · have hr : n - 50850 < 50 := by omega
                                      have heq : n = (n - 50850) + 50850 := by omega
                                      rw [heq]
                                      exact le_w1017 ⟨n - 50850, hr⟩
                                    · by_cases h18 : n < 50950
                                      · have hr : n - 50900 < 50 := by omega
                                        have heq : n = (n - 50900) + 50900 := by omega
                                        rw [heq]
                                        exact le_w1018 ⟨n - 50900, hr⟩
                                      · by_cases h19 : n < 51000
                                        · have hr : n - 50950 < 50 := by omega
                                          have heq : n = (n - 50950) + 50950 := by omega
                                          rw [heq]
                                          exact le_w1019 ⟨n - 50950, hr⟩
                                        · by_cases h20 : n < 51050
                                          · have hr : n - 51000 < 50 := by omega
                                            have heq : n = (n - 51000) + 51000 := by omega
                                            rw [heq]
                                            exact le_w1020 ⟨n - 51000, hr⟩
                                          · by_cases h21 : n < 51100
                                            · have hr : n - 51050 < 50 := by omega
                                              have heq : n = (n - 51050) + 51050 := by omega
                                              rw [heq]
                                              exact le_w1021 ⟨n - 51050, hr⟩
                                            · by_cases h22 : n < 51150
                                              · have hr : n - 51100 < 50 := by omega
                                                have heq : n = (n - 51100) + 51100 := by omega
                                                rw [heq]
                                                exact le_w1022 ⟨n - 51100, hr⟩
                                              · by_cases h23 : n < 51200
                                                · have hr : n - 51150 < 50 := by omega
                                                  have heq : n = (n - 51150) + 51150 := by omega
                                                  rw [heq]
                                                  exact le_w1023 ⟨n - 51150, hr⟩
                                                · by_cases h24 : n < 51250
                                                  · have hr : n - 51200 < 50 := by omega
                                                    have heq : n = (n - 51200) + 51200 := by omega
                                                    rw [heq]
                                                    exact le_w1024 ⟨n - 51200, hr⟩
                                                  · by_cases h25 : n < 51300
                                                    · have hr : n - 51250 < 50 := by omega
                                                      have heq : n = (n - 51250) + 51250 := by omega
                                                      rw [heq]
                                                      exact le_w1025 ⟨n - 51250, hr⟩
                                                    · by_cases h26 : n < 51350
                                                      · have hr : n - 51300 < 50 := by omega
                                                        have heq : n = (n - 51300) + 51300 := by omega
                                                        rw [heq]
                                                        exact le_w1026 ⟨n - 51300, hr⟩
                                                      · by_cases h27 : n < 51400
                                                        · have hr : n - 51350 < 50 := by omega
                                                          have heq : n = (n - 51350) + 51350 := by omega
                                                          rw [heq]
                                                          exact le_w1027 ⟨n - 51350, hr⟩
                                                        · by_cases h28 : n < 51450
                                                          · have hr : n - 51400 < 50 := by omega
                                                            have heq : n = (n - 51400) + 51400 := by omega
                                                            rw [heq]
                                                            exact le_w1028 ⟨n - 51400, hr⟩
                                                          · by_cases h29 : n < 51500
                                                            · have hr : n - 51450 < 50 := by omega
                                                              have heq : n = (n - 51450) + 51450 := by omega
                                                              rw [heq]
                                                              exact le_w1029 ⟨n - 51450, hr⟩
                                                            · by_cases h30 : n < 51550
                                                              · have hr : n - 51500 < 50 := by omega
                                                                have heq : n = (n - 51500) + 51500 := by omega
                                                                rw [heq]
                                                                exact le_w1030 ⟨n - 51500, hr⟩
                                                              · by_cases h31 : n < 51600
                                                                · have hr : n - 51550 < 50 := by omega
                                                                  have heq : n = (n - 51550) + 51550 := by omega
                                                                  rw [heq]
                                                                  exact le_w1031 ⟨n - 51550, hr⟩
                                                                · by_cases h32 : n < 51650
                                                                  · have hr : n - 51600 < 50 := by omega
                                                                    have heq : n = (n - 51600) + 51600 := by omega
                                                                    rw [heq]
                                                                    exact le_w1032 ⟨n - 51600, hr⟩
                                                                  · by_cases h33 : n < 51700
                                                                    · have hr : n - 51650 < 50 := by omega
                                                                      have heq : n = (n - 51650) + 51650 := by omega
                                                                      rw [heq]
                                                                      exact le_w1033 ⟨n - 51650, hr⟩
                                                                    · by_cases h34 : n < 51750
                                                                      · have hr : n - 51700 < 50 := by omega
                                                                        have heq : n = (n - 51700) + 51700 := by omega
                                                                        rw [heq]
                                                                        exact le_w1034 ⟨n - 51700, hr⟩
                                                                      · by_cases h35 : n < 51800
                                                                        · have hr : n - 51750 < 50 := by omega
                                                                          have heq : n = (n - 51750) + 51750 := by omega
                                                                          rw [heq]
                                                                          exact le_w1035 ⟨n - 51750, hr⟩
                                                                        · by_cases h36 : n < 51850
                                                                          · have hr : n - 51800 < 50 := by omega
                                                                            have heq : n = (n - 51800) + 51800 := by omega
                                                                            rw [heq]
                                                                            exact le_w1036 ⟨n - 51800, hr⟩
                                                                          · by_cases h37 : n < 51900
                                                                            · have hr : n - 51850 < 50 := by omega
                                                                              have heq : n = (n - 51850) + 51850 := by omega
                                                                              rw [heq]
                                                                              exact le_w1037 ⟨n - 51850, hr⟩
                                                                            · by_cases h38 : n < 51950
                                                                              · have hr : n - 51900 < 50 := by omega
                                                                                have heq : n = (n - 51900) + 51900 := by omega
                                                                                rw [heq]
                                                                                exact le_w1038 ⟨n - 51900, hr⟩
                                                                              · by_cases h39 : n < 52000
                                                                                · have hr : n - 51950 < 50 := by omega
                                                                                  have heq : n = (n - 51950) + 51950 := by omega
                                                                                  rw [heq]
                                                                                  exact le_w1039 ⟨n - 51950, hr⟩
                                                                                · by_cases h40 : n < 52050
                                                                                  · have hr : n - 52000 < 50 := by omega
                                                                                    have heq : n = (n - 52000) + 52000 := by omega
                                                                                    rw [heq]
                                                                                    exact le_w1040 ⟨n - 52000, hr⟩
                                                                                  · by_cases h41 : n < 52100
                                                                                    · have hr : n - 52050 < 50 := by omega
                                                                                      have heq : n = (n - 52050) + 52050 := by omega
                                                                                      rw [heq]
                                                                                      exact le_w1041 ⟨n - 52050, hr⟩
                                                                                    · by_cases h42 : n < 52150
                                                                                      · have hr : n - 52100 < 50 := by omega
                                                                                        have heq : n = (n - 52100) + 52100 := by omega
                                                                                        rw [heq]
                                                                                        exact le_w1042 ⟨n - 52100, hr⟩
                                                                                      · by_cases h43 : n < 52200
                                                                                        · have hr : n - 52150 < 50 := by omega
                                                                                          have heq : n = (n - 52150) + 52150 := by omega
                                                                                          rw [heq]
                                                                                          exact le_w1043 ⟨n - 52150, hr⟩
                                                                                        · by_cases h44 : n < 52250
                                                                                          · have hr : n - 52200 < 50 := by omega
                                                                                            have heq : n = (n - 52200) + 52200 := by omega
                                                                                            rw [heq]
                                                                                            exact le_w1044 ⟨n - 52200, hr⟩
                                                                                          · by_cases h45 : n < 52300
                                                                                            · have hr : n - 52250 < 50 := by omega
                                                                                              have heq : n = (n - 52250) + 52250 := by omega
                                                                                              rw [heq]
                                                                                              exact le_w1045 ⟨n - 52250, hr⟩
                                                                                            · by_cases h46 : n < 52350
                                                                                              · have hr : n - 52300 < 50 := by omega
                                                                                                have heq : n = (n - 52300) + 52300 := by omega
                                                                                                rw [heq]
                                                                                                exact le_w1046 ⟨n - 52300, hr⟩
                                                                                              · by_cases h47 : n < 52400
                                                                                                · have hr : n - 52350 < 50 := by omega
                                                                                                  have heq : n = (n - 52350) + 52350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact le_w1047 ⟨n - 52350, hr⟩
                                                                                                · by_cases h48 : n < 52450
                                                                                                  · have hr : n - 52400 < 50 := by omega
                                                                                                    have heq : n = (n - 52400) + 52400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact le_w1048 ⟨n - 52400, hr⟩
                                                                                                  · by_cases h49 : n < 52500
                                                                                                    · have hr : n - 52450 < 50 := by omega
                                                                                                      have heq : n = (n - 52450) + 52450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact le_w1049 ⟨n - 52450, hr⟩
                                                                                                    · by_cases h50 : n < 52550
                                                                                                      · have hr : n - 52500 < 50 := by omega
                                                                                                        have heq : n = (n - 52500) + 52500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact le_w1050 ⟨n - 52500, hr⟩
                                                                                                      · by_cases h51 : n < 52600
                                                                                                        · have hr : n - 52550 < 50 := by omega
                                                                                                          have heq : n = (n - 52550) + 52550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact le_w1051 ⟨n - 52550, hr⟩
                                                                                                        · by_cases h52 : n < 52650
                                                                                                          · have hr : n - 52600 < 50 := by omega
                                                                                                            have heq : n = (n - 52600) + 52600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact le_w1052 ⟨n - 52600, hr⟩
                                                                                                          · by_cases h53 : n < 52700
                                                                                                            · have hr : n - 52650 < 50 := by omega
                                                                                                              have heq : n = (n - 52650) + 52650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact le_w1053 ⟨n - 52650, hr⟩
                                                                                                            · by_cases h54 : n < 52750
                                                                                                              · have hr : n - 52700 < 50 := by omega
                                                                                                                have heq : n = (n - 52700) + 52700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact le_w1054 ⟨n - 52700, hr⟩
                                                                                                              · by_cases h55 : n < 52800
                                                                                                                · have hr : n - 52750 < 50 := by omega
                                                                                                                  have heq : n = (n - 52750) + 52750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact le_w1055 ⟨n - 52750, hr⟩
                                                                                                                · by_cases h56 : n < 52850
                                                                                                                  · have hr : n - 52800 < 50 := by omega
                                                                                                                    have heq : n = (n - 52800) + 52800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact le_w1056 ⟨n - 52800, hr⟩
                                                                                                                  · by_cases h57 : n < 52900
                                                                                                                    · have hr : n - 52850 < 50 := by omega
                                                                                                                      have heq : n = (n - 52850) + 52850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact le_w1057 ⟨n - 52850, hr⟩
                                                                                                                    · by_cases h58 : n < 52950
                                                                                                                      · have hr : n - 52900 < 50 := by omega
                                                                                                                        have heq : n = (n - 52900) + 52900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact le_w1058 ⟨n - 52900, hr⟩
                                                                                                                      · by_cases h59 : n < 53000
                                                                                                                        · have hr : n - 52950 < 50 := by omega
                                                                                                                          have heq : n = (n - 52950) + 52950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact le_w1059 ⟨n - 52950, hr⟩
                                                                                                                        · by_cases h60 : n < 53050
                                                                                                                          · have hr : n - 53000 < 50 := by omega
                                                                                                                            have heq : n = (n - 53000) + 53000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact le_w1060 ⟨n - 53000, hr⟩
                                                                                                                          · by_cases h61 : n < 53100
                                                                                                                            · have hr : n - 53050 < 50 := by omega
                                                                                                                              have heq : n = (n - 53050) + 53050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact le_w1061 ⟨n - 53050, hr⟩
                                                                                                                            · by_cases h62 : n < 53150
                                                                                                                              · have hr : n - 53100 < 50 := by omega
                                                                                                                                have heq : n = (n - 53100) + 53100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact le_w1062 ⟨n - 53100, hr⟩
                                                                                                                              · by_cases h63 : n < 53200
                                                                                                                                · have hr : n - 53150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 53150) + 53150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact le_w1063 ⟨n - 53150, hr⟩
                                                                                                                                · by_cases h64 : n < 53250
                                                                                                                                  · have hr : n - 53200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 53200) + 53200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact le_w1064 ⟨n - 53200, hr⟩
                                                                                                                                  · by_cases h65 : n < 53300
                                                                                                                                    · have hr : n - 53250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 53250) + 53250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact le_w1065 ⟨n - 53250, hr⟩
                                                                                                                                    · by_cases h66 : n < 53350
                                                                                                                                      · have hr : n - 53300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 53300) + 53300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact le_w1066 ⟨n - 53300, hr⟩
                                                                                                                                      · by_cases h67 : n < 53400
                                                                                                                                        · have hr : n - 53350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 53350) + 53350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact le_w1067 ⟨n - 53350, hr⟩
                                                                                                                                        · by_cases h68 : n < 53450
                                                                                                                                          · have hr : n - 53400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 53400) + 53400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact le_w1068 ⟨n - 53400, hr⟩
                                                                                                                                          · by_cases h69 : n < 53500
                                                                                                                                            · have hr : n - 53450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 53450) + 53450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact le_w1069 ⟨n - 53450, hr⟩
                                                                                                                                            · by_cases h70 : n < 53550
                                                                                                                                              · have hr : n - 53500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 53500) + 53500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact le_w1070 ⟨n - 53500, hr⟩
                                                                                                                                              · by_cases h71 : n < 53600
                                                                                                                                                · have hr : n - 53550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 53550) + 53550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact le_w1071 ⟨n - 53550, hr⟩
                                                                                                                                                · by_cases h72 : n < 53650
                                                                                                                                                  · have hr : n - 53600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 53600) + 53600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact le_w1072 ⟨n - 53600, hr⟩
                                                                                                                                                  · by_cases h73 : n < 53700
                                                                                                                                                    · have hr : n - 53650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 53650) + 53650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact le_w1073 ⟨n - 53650, hr⟩
                                                                                                                                                    · by_cases h74 : n < 53750
                                                                                                                                                      · have hr : n - 53700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 53700) + 53700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact le_w1074 ⟨n - 53700, hr⟩
                                                                                                                                                      · by_cases h75 : n < 53800
                                                                                                                                                        · have hr : n - 53750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 53750) + 53750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact le_w1075 ⟨n - 53750, hr⟩
                                                                                                                                                        · by_cases h76 : n < 53850
                                                                                                                                                          · have hr : n - 53800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 53800) + 53800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact le_w1076 ⟨n - 53800, hr⟩
                                                                                                                                                          · by_cases h77 : n < 53900
                                                                                                                                                            · have hr : n - 53850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 53850) + 53850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact le_w1077 ⟨n - 53850, hr⟩
                                                                                                                                                            · by_cases h78 : n < 53950
                                                                                                                                                              · have hr : n - 53900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 53900) + 53900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact le_w1078 ⟨n - 53900, hr⟩
                                                                                                                                                              · by_cases h79 : n < 54000
                                                                                                                                                                · have hr : n - 53950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 53950) + 53950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact le_w1079 ⟨n - 53950, hr⟩
                                                                                                                                                                · by_cases h80 : n < 54050
                                                                                                                                                                  · have hr : n - 54000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 54000) + 54000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact le_w1080 ⟨n - 54000, hr⟩
                                                                                                                                                                  · by_cases h81 : n < 54100
                                                                                                                                                                    · have hr : n - 54050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 54050) + 54050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact le_w1081 ⟨n - 54050, hr⟩
                                                                                                                                                                    · by_cases h82 : n < 54150
                                                                                                                                                                      · have hr : n - 54100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 54100) + 54100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact le_w1082 ⟨n - 54100, hr⟩
                                                                                                                                                                      · by_cases h83 : n < 54200
                                                                                                                                                                        · have hr : n - 54150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 54150) + 54150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact le_w1083 ⟨n - 54150, hr⟩
                                                                                                                                                                        · by_cases h84 : n < 54250
                                                                                                                                                                          · have hr : n - 54200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 54200) + 54200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact le_w1084 ⟨n - 54200, hr⟩
                                                                                                                                                                          · by_cases h85 : n < 54300
                                                                                                                                                                            · have hr : n - 54250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 54250) + 54250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact le_w1085 ⟨n - 54250, hr⟩
                                                                                                                                                                            · by_cases h86 : n < 54350
                                                                                                                                                                              · have hr : n - 54300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 54300) + 54300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact le_w1086 ⟨n - 54300, hr⟩
                                                                                                                                                                              · by_cases h87 : n < 54400
                                                                                                                                                                                · have hr : n - 54350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 54350) + 54350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact le_w1087 ⟨n - 54350, hr⟩
                                                                                                                                                                                · by_cases h88 : n < 54450
                                                                                                                                                                                  · have hr : n - 54400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 54400) + 54400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact le_w1088 ⟨n - 54400, hr⟩
                                                                                                                                                                                  · by_cases h89 : n < 54500
                                                                                                                                                                                    · have hr : n - 54450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 54450) + 54450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact le_w1089 ⟨n - 54450, hr⟩
                                                                                                                                                                                    · by_cases h90 : n < 54550
                                                                                                                                                                                      · have hr : n - 54500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 54500) + 54500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact le_w1090 ⟨n - 54500, hr⟩
                                                                                                                                                                                      · by_cases h91 : n < 54600
                                                                                                                                                                                        · have hr : n - 54550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 54550) + 54550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact le_w1091 ⟨n - 54550, hr⟩
                                                                                                                                                                                        · by_cases h92 : n < 54650
                                                                                                                                                                                          · have hr : n - 54600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 54600) + 54600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact le_w1092 ⟨n - 54600, hr⟩
                                                                                                                                                                                          · by_cases h93 : n < 54700
                                                                                                                                                                                            · have hr : n - 54650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 54650) + 54650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact le_w1093 ⟨n - 54650, hr⟩
                                                                                                                                                                                            · by_cases h94 : n < 54750
                                                                                                                                                                                              · have hr : n - 54700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 54700) + 54700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact le_w1094 ⟨n - 54700, hr⟩
                                                                                                                                                                                              · by_cases h95 : n < 54800
                                                                                                                                                                                                · have hr : n - 54750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 54750) + 54750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact le_w1095 ⟨n - 54750, hr⟩
                                                                                                                                                                                                · by_cases h96 : n < 54850
                                                                                                                                                                                                  · have hr : n - 54800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 54800) + 54800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact le_w1096 ⟨n - 54800, hr⟩
                                                                                                                                                                                                  · by_cases h97 : n < 54900
                                                                                                                                                                                                    · have hr : n - 54850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 54850) + 54850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact le_w1097 ⟨n - 54850, hr⟩
                                                                                                                                                                                                    · by_cases h98 : n < 54950
                                                                                                                                                                                                      · have hr : n - 54900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 54900) + 54900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact le_w1098 ⟨n - 54900, hr⟩
                                                                                                                                                                                                      · by_cases h99 : n < 55000
                                                                                                                                                                                                        · have hr : n - 54950 < 50 := by omega
                                                                                                                                                                                                          have heq : n = (n - 54950) + 54950 := by omega
                                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                                          exact le_w1099 ⟨n - 54950, hr⟩
                                                                                                                                                                                                        · omega

theorem dimF_pos_range : ∀ n, 50000 ≤ n → n < 55000 → 0 < dimF n := by
  intro n hlo hhi
  by_cases h0 : n < 50050
  · have hr : n - 50000 < 50 := by omega
    have heq : n = (n - 50000) + 50000 := by omega
    rw [heq]
    exact pos_w1000 ⟨n - 50000, hr⟩
  · by_cases h1 : n < 50100
    · have hr : n - 50050 < 50 := by omega
      have heq : n = (n - 50050) + 50050 := by omega
      rw [heq]
      exact pos_w1001 ⟨n - 50050, hr⟩
    · by_cases h2 : n < 50150
      · have hr : n - 50100 < 50 := by omega
        have heq : n = (n - 50100) + 50100 := by omega
        rw [heq]
        exact pos_w1002 ⟨n - 50100, hr⟩
      · by_cases h3 : n < 50200
        · have hr : n - 50150 < 50 := by omega
          have heq : n = (n - 50150) + 50150 := by omega
          rw [heq]
          exact pos_w1003 ⟨n - 50150, hr⟩
        · by_cases h4 : n < 50250
          · have hr : n - 50200 < 50 := by omega
            have heq : n = (n - 50200) + 50200 := by omega
            rw [heq]
            exact pos_w1004 ⟨n - 50200, hr⟩
          · by_cases h5 : n < 50300
            · have hr : n - 50250 < 50 := by omega
              have heq : n = (n - 50250) + 50250 := by omega
              rw [heq]
              exact pos_w1005 ⟨n - 50250, hr⟩
            · by_cases h6 : n < 50350
              · have hr : n - 50300 < 50 := by omega
                have heq : n = (n - 50300) + 50300 := by omega
                rw [heq]
                exact pos_w1006 ⟨n - 50300, hr⟩
              · by_cases h7 : n < 50400
                · have hr : n - 50350 < 50 := by omega
                  have heq : n = (n - 50350) + 50350 := by omega
                  rw [heq]
                  exact pos_w1007 ⟨n - 50350, hr⟩
                · by_cases h8 : n < 50450
                  · have hr : n - 50400 < 50 := by omega
                    have heq : n = (n - 50400) + 50400 := by omega
                    rw [heq]
                    exact pos_w1008 ⟨n - 50400, hr⟩
                  · by_cases h9 : n < 50500
                    · have hr : n - 50450 < 50 := by omega
                      have heq : n = (n - 50450) + 50450 := by omega
                      rw [heq]
                      exact pos_w1009 ⟨n - 50450, hr⟩
                    · by_cases h10 : n < 50550
                      · have hr : n - 50500 < 50 := by omega
                        have heq : n = (n - 50500) + 50500 := by omega
                        rw [heq]
                        exact pos_w1010 ⟨n - 50500, hr⟩
                      · by_cases h11 : n < 50600
                        · have hr : n - 50550 < 50 := by omega
                          have heq : n = (n - 50550) + 50550 := by omega
                          rw [heq]
                          exact pos_w1011 ⟨n - 50550, hr⟩
                        · by_cases h12 : n < 50650
                          · have hr : n - 50600 < 50 := by omega
                            have heq : n = (n - 50600) + 50600 := by omega
                            rw [heq]
                            exact pos_w1012 ⟨n - 50600, hr⟩
                          · by_cases h13 : n < 50700
                            · have hr : n - 50650 < 50 := by omega
                              have heq : n = (n - 50650) + 50650 := by omega
                              rw [heq]
                              exact pos_w1013 ⟨n - 50650, hr⟩
                            · by_cases h14 : n < 50750
                              · have hr : n - 50700 < 50 := by omega
                                have heq : n = (n - 50700) + 50700 := by omega
                                rw [heq]
                                exact pos_w1014 ⟨n - 50700, hr⟩
                              · by_cases h15 : n < 50800
                                · have hr : n - 50750 < 50 := by omega
                                  have heq : n = (n - 50750) + 50750 := by omega
                                  rw [heq]
                                  exact pos_w1015 ⟨n - 50750, hr⟩
                                · by_cases h16 : n < 50850
                                  · have hr : n - 50800 < 50 := by omega
                                    have heq : n = (n - 50800) + 50800 := by omega
                                    rw [heq]
                                    exact pos_w1016 ⟨n - 50800, hr⟩
                                  · by_cases h17 : n < 50900
                                    · have hr : n - 50850 < 50 := by omega
                                      have heq : n = (n - 50850) + 50850 := by omega
                                      rw [heq]
                                      exact pos_w1017 ⟨n - 50850, hr⟩
                                    · by_cases h18 : n < 50950
                                      · have hr : n - 50900 < 50 := by omega
                                        have heq : n = (n - 50900) + 50900 := by omega
                                        rw [heq]
                                        exact pos_w1018 ⟨n - 50900, hr⟩
                                      · by_cases h19 : n < 51000
                                        · have hr : n - 50950 < 50 := by omega
                                          have heq : n = (n - 50950) + 50950 := by omega
                                          rw [heq]
                                          exact pos_w1019 ⟨n - 50950, hr⟩
                                        · by_cases h20 : n < 51050
                                          · have hr : n - 51000 < 50 := by omega
                                            have heq : n = (n - 51000) + 51000 := by omega
                                            rw [heq]
                                            exact pos_w1020 ⟨n - 51000, hr⟩
                                          · by_cases h21 : n < 51100
                                            · have hr : n - 51050 < 50 := by omega
                                              have heq : n = (n - 51050) + 51050 := by omega
                                              rw [heq]
                                              exact pos_w1021 ⟨n - 51050, hr⟩
                                            · by_cases h22 : n < 51150
                                              · have hr : n - 51100 < 50 := by omega
                                                have heq : n = (n - 51100) + 51100 := by omega
                                                rw [heq]
                                                exact pos_w1022 ⟨n - 51100, hr⟩
                                              · by_cases h23 : n < 51200
                                                · have hr : n - 51150 < 50 := by omega
                                                  have heq : n = (n - 51150) + 51150 := by omega
                                                  rw [heq]
                                                  exact pos_w1023 ⟨n - 51150, hr⟩
                                                · by_cases h24 : n < 51250
                                                  · have hr : n - 51200 < 50 := by omega
                                                    have heq : n = (n - 51200) + 51200 := by omega
                                                    rw [heq]
                                                    exact pos_w1024 ⟨n - 51200, hr⟩
                                                  · by_cases h25 : n < 51300
                                                    · have hr : n - 51250 < 50 := by omega
                                                      have heq : n = (n - 51250) + 51250 := by omega
                                                      rw [heq]
                                                      exact pos_w1025 ⟨n - 51250, hr⟩
                                                    · by_cases h26 : n < 51350
                                                      · have hr : n - 51300 < 50 := by omega
                                                        have heq : n = (n - 51300) + 51300 := by omega
                                                        rw [heq]
                                                        exact pos_w1026 ⟨n - 51300, hr⟩
                                                      · by_cases h27 : n < 51400
                                                        · have hr : n - 51350 < 50 := by omega
                                                          have heq : n = (n - 51350) + 51350 := by omega
                                                          rw [heq]
                                                          exact pos_w1027 ⟨n - 51350, hr⟩
                                                        · by_cases h28 : n < 51450
                                                          · have hr : n - 51400 < 50 := by omega
                                                            have heq : n = (n - 51400) + 51400 := by omega
                                                            rw [heq]
                                                            exact pos_w1028 ⟨n - 51400, hr⟩
                                                          · by_cases h29 : n < 51500
                                                            · have hr : n - 51450 < 50 := by omega
                                                              have heq : n = (n - 51450) + 51450 := by omega
                                                              rw [heq]
                                                              exact pos_w1029 ⟨n - 51450, hr⟩
                                                            · by_cases h30 : n < 51550
                                                              · have hr : n - 51500 < 50 := by omega
                                                                have heq : n = (n - 51500) + 51500 := by omega
                                                                rw [heq]
                                                                exact pos_w1030 ⟨n - 51500, hr⟩
                                                              · by_cases h31 : n < 51600
                                                                · have hr : n - 51550 < 50 := by omega
                                                                  have heq : n = (n - 51550) + 51550 := by omega
                                                                  rw [heq]
                                                                  exact pos_w1031 ⟨n - 51550, hr⟩
                                                                · by_cases h32 : n < 51650
                                                                  · have hr : n - 51600 < 50 := by omega
                                                                    have heq : n = (n - 51600) + 51600 := by omega
                                                                    rw [heq]
                                                                    exact pos_w1032 ⟨n - 51600, hr⟩
                                                                  · by_cases h33 : n < 51700
                                                                    · have hr : n - 51650 < 50 := by omega
                                                                      have heq : n = (n - 51650) + 51650 := by omega
                                                                      rw [heq]
                                                                      exact pos_w1033 ⟨n - 51650, hr⟩
                                                                    · by_cases h34 : n < 51750
                                                                      · have hr : n - 51700 < 50 := by omega
                                                                        have heq : n = (n - 51700) + 51700 := by omega
                                                                        rw [heq]
                                                                        exact pos_w1034 ⟨n - 51700, hr⟩
                                                                      · by_cases h35 : n < 51800
                                                                        · have hr : n - 51750 < 50 := by omega
                                                                          have heq : n = (n - 51750) + 51750 := by omega
                                                                          rw [heq]
                                                                          exact pos_w1035 ⟨n - 51750, hr⟩
                                                                        · by_cases h36 : n < 51850
                                                                          · have hr : n - 51800 < 50 := by omega
                                                                            have heq : n = (n - 51800) + 51800 := by omega
                                                                            rw [heq]
                                                                            exact pos_w1036 ⟨n - 51800, hr⟩
                                                                          · by_cases h37 : n < 51900
                                                                            · have hr : n - 51850 < 50 := by omega
                                                                              have heq : n = (n - 51850) + 51850 := by omega
                                                                              rw [heq]
                                                                              exact pos_w1037 ⟨n - 51850, hr⟩
                                                                            · by_cases h38 : n < 51950
                                                                              · have hr : n - 51900 < 50 := by omega
                                                                                have heq : n = (n - 51900) + 51900 := by omega
                                                                                rw [heq]
                                                                                exact pos_w1038 ⟨n - 51900, hr⟩
                                                                              · by_cases h39 : n < 52000
                                                                                · have hr : n - 51950 < 50 := by omega
                                                                                  have heq : n = (n - 51950) + 51950 := by omega
                                                                                  rw [heq]
                                                                                  exact pos_w1039 ⟨n - 51950, hr⟩
                                                                                · by_cases h40 : n < 52050
                                                                                  · have hr : n - 52000 < 50 := by omega
                                                                                    have heq : n = (n - 52000) + 52000 := by omega
                                                                                    rw [heq]
                                                                                    exact pos_w1040 ⟨n - 52000, hr⟩
                                                                                  · by_cases h41 : n < 52100
                                                                                    · have hr : n - 52050 < 50 := by omega
                                                                                      have heq : n = (n - 52050) + 52050 := by omega
                                                                                      rw [heq]
                                                                                      exact pos_w1041 ⟨n - 52050, hr⟩
                                                                                    · by_cases h42 : n < 52150
                                                                                      · have hr : n - 52100 < 50 := by omega
                                                                                        have heq : n = (n - 52100) + 52100 := by omega
                                                                                        rw [heq]
                                                                                        exact pos_w1042 ⟨n - 52100, hr⟩
                                                                                      · by_cases h43 : n < 52200
                                                                                        · have hr : n - 52150 < 50 := by omega
                                                                                          have heq : n = (n - 52150) + 52150 := by omega
                                                                                          rw [heq]
                                                                                          exact pos_w1043 ⟨n - 52150, hr⟩
                                                                                        · by_cases h44 : n < 52250
                                                                                          · have hr : n - 52200 < 50 := by omega
                                                                                            have heq : n = (n - 52200) + 52200 := by omega
                                                                                            rw [heq]
                                                                                            exact pos_w1044 ⟨n - 52200, hr⟩
                                                                                          · by_cases h45 : n < 52300
                                                                                            · have hr : n - 52250 < 50 := by omega
                                                                                              have heq : n = (n - 52250) + 52250 := by omega
                                                                                              rw [heq]
                                                                                              exact pos_w1045 ⟨n - 52250, hr⟩
                                                                                            · by_cases h46 : n < 52350
                                                                                              · have hr : n - 52300 < 50 := by omega
                                                                                                have heq : n = (n - 52300) + 52300 := by omega
                                                                                                rw [heq]
                                                                                                exact pos_w1046 ⟨n - 52300, hr⟩
                                                                                              · by_cases h47 : n < 52400
                                                                                                · have hr : n - 52350 < 50 := by omega
                                                                                                  have heq : n = (n - 52350) + 52350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact pos_w1047 ⟨n - 52350, hr⟩
                                                                                                · by_cases h48 : n < 52450
                                                                                                  · have hr : n - 52400 < 50 := by omega
                                                                                                    have heq : n = (n - 52400) + 52400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact pos_w1048 ⟨n - 52400, hr⟩
                                                                                                  · by_cases h49 : n < 52500
                                                                                                    · have hr : n - 52450 < 50 := by omega
                                                                                                      have heq : n = (n - 52450) + 52450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact pos_w1049 ⟨n - 52450, hr⟩
                                                                                                    · by_cases h50 : n < 52550
                                                                                                      · have hr : n - 52500 < 50 := by omega
                                                                                                        have heq : n = (n - 52500) + 52500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact pos_w1050 ⟨n - 52500, hr⟩
                                                                                                      · by_cases h51 : n < 52600
                                                                                                        · have hr : n - 52550 < 50 := by omega
                                                                                                          have heq : n = (n - 52550) + 52550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact pos_w1051 ⟨n - 52550, hr⟩
                                                                                                        · by_cases h52 : n < 52650
                                                                                                          · have hr : n - 52600 < 50 := by omega
                                                                                                            have heq : n = (n - 52600) + 52600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact pos_w1052 ⟨n - 52600, hr⟩
                                                                                                          · by_cases h53 : n < 52700
                                                                                                            · have hr : n - 52650 < 50 := by omega
                                                                                                              have heq : n = (n - 52650) + 52650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact pos_w1053 ⟨n - 52650, hr⟩
                                                                                                            · by_cases h54 : n < 52750
                                                                                                              · have hr : n - 52700 < 50 := by omega
                                                                                                                have heq : n = (n - 52700) + 52700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact pos_w1054 ⟨n - 52700, hr⟩
                                                                                                              · by_cases h55 : n < 52800
                                                                                                                · have hr : n - 52750 < 50 := by omega
                                                                                                                  have heq : n = (n - 52750) + 52750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact pos_w1055 ⟨n - 52750, hr⟩
                                                                                                                · by_cases h56 : n < 52850
                                                                                                                  · have hr : n - 52800 < 50 := by omega
                                                                                                                    have heq : n = (n - 52800) + 52800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact pos_w1056 ⟨n - 52800, hr⟩
                                                                                                                  · by_cases h57 : n < 52900
                                                                                                                    · have hr : n - 52850 < 50 := by omega
                                                                                                                      have heq : n = (n - 52850) + 52850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact pos_w1057 ⟨n - 52850, hr⟩
                                                                                                                    · by_cases h58 : n < 52950
                                                                                                                      · have hr : n - 52900 < 50 := by omega
                                                                                                                        have heq : n = (n - 52900) + 52900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact pos_w1058 ⟨n - 52900, hr⟩
                                                                                                                      · by_cases h59 : n < 53000
                                                                                                                        · have hr : n - 52950 < 50 := by omega
                                                                                                                          have heq : n = (n - 52950) + 52950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact pos_w1059 ⟨n - 52950, hr⟩
                                                                                                                        · by_cases h60 : n < 53050
                                                                                                                          · have hr : n - 53000 < 50 := by omega
                                                                                                                            have heq : n = (n - 53000) + 53000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact pos_w1060 ⟨n - 53000, hr⟩
                                                                                                                          · by_cases h61 : n < 53100
                                                                                                                            · have hr : n - 53050 < 50 := by omega
                                                                                                                              have heq : n = (n - 53050) + 53050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact pos_w1061 ⟨n - 53050, hr⟩
                                                                                                                            · by_cases h62 : n < 53150
                                                                                                                              · have hr : n - 53100 < 50 := by omega
                                                                                                                                have heq : n = (n - 53100) + 53100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact pos_w1062 ⟨n - 53100, hr⟩
                                                                                                                              · by_cases h63 : n < 53200
                                                                                                                                · have hr : n - 53150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 53150) + 53150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact pos_w1063 ⟨n - 53150, hr⟩
                                                                                                                                · by_cases h64 : n < 53250
                                                                                                                                  · have hr : n - 53200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 53200) + 53200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact pos_w1064 ⟨n - 53200, hr⟩
                                                                                                                                  · by_cases h65 : n < 53300
                                                                                                                                    · have hr : n - 53250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 53250) + 53250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact pos_w1065 ⟨n - 53250, hr⟩
                                                                                                                                    · by_cases h66 : n < 53350
                                                                                                                                      · have hr : n - 53300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 53300) + 53300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact pos_w1066 ⟨n - 53300, hr⟩
                                                                                                                                      · by_cases h67 : n < 53400
                                                                                                                                        · have hr : n - 53350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 53350) + 53350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact pos_w1067 ⟨n - 53350, hr⟩
                                                                                                                                        · by_cases h68 : n < 53450
                                                                                                                                          · have hr : n - 53400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 53400) + 53400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact pos_w1068 ⟨n - 53400, hr⟩
                                                                                                                                          · by_cases h69 : n < 53500
                                                                                                                                            · have hr : n - 53450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 53450) + 53450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact pos_w1069 ⟨n - 53450, hr⟩
                                                                                                                                            · by_cases h70 : n < 53550
                                                                                                                                              · have hr : n - 53500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 53500) + 53500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact pos_w1070 ⟨n - 53500, hr⟩
                                                                                                                                              · by_cases h71 : n < 53600
                                                                                                                                                · have hr : n - 53550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 53550) + 53550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact pos_w1071 ⟨n - 53550, hr⟩
                                                                                                                                                · by_cases h72 : n < 53650
                                                                                                                                                  · have hr : n - 53600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 53600) + 53600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact pos_w1072 ⟨n - 53600, hr⟩
                                                                                                                                                  · by_cases h73 : n < 53700
                                                                                                                                                    · have hr : n - 53650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 53650) + 53650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact pos_w1073 ⟨n - 53650, hr⟩
                                                                                                                                                    · by_cases h74 : n < 53750
                                                                                                                                                      · have hr : n - 53700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 53700) + 53700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact pos_w1074 ⟨n - 53700, hr⟩
                                                                                                                                                      · by_cases h75 : n < 53800
                                                                                                                                                        · have hr : n - 53750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 53750) + 53750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact pos_w1075 ⟨n - 53750, hr⟩
                                                                                                                                                        · by_cases h76 : n < 53850
                                                                                                                                                          · have hr : n - 53800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 53800) + 53800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact pos_w1076 ⟨n - 53800, hr⟩
                                                                                                                                                          · by_cases h77 : n < 53900
                                                                                                                                                            · have hr : n - 53850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 53850) + 53850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact pos_w1077 ⟨n - 53850, hr⟩
                                                                                                                                                            · by_cases h78 : n < 53950
                                                                                                                                                              · have hr : n - 53900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 53900) + 53900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact pos_w1078 ⟨n - 53900, hr⟩
                                                                                                                                                              · by_cases h79 : n < 54000
                                                                                                                                                                · have hr : n - 53950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 53950) + 53950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact pos_w1079 ⟨n - 53950, hr⟩
                                                                                                                                                                · by_cases h80 : n < 54050
                                                                                                                                                                  · have hr : n - 54000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 54000) + 54000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact pos_w1080 ⟨n - 54000, hr⟩
                                                                                                                                                                  · by_cases h81 : n < 54100
                                                                                                                                                                    · have hr : n - 54050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 54050) + 54050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact pos_w1081 ⟨n - 54050, hr⟩
                                                                                                                                                                    · by_cases h82 : n < 54150
                                                                                                                                                                      · have hr : n - 54100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 54100) + 54100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact pos_w1082 ⟨n - 54100, hr⟩
                                                                                                                                                                      · by_cases h83 : n < 54200
                                                                                                                                                                        · have hr : n - 54150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 54150) + 54150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact pos_w1083 ⟨n - 54150, hr⟩
                                                                                                                                                                        · by_cases h84 : n < 54250
                                                                                                                                                                          · have hr : n - 54200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 54200) + 54200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact pos_w1084 ⟨n - 54200, hr⟩
                                                                                                                                                                          · by_cases h85 : n < 54300
                                                                                                                                                                            · have hr : n - 54250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 54250) + 54250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact pos_w1085 ⟨n - 54250, hr⟩
                                                                                                                                                                            · by_cases h86 : n < 54350
                                                                                                                                                                              · have hr : n - 54300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 54300) + 54300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact pos_w1086 ⟨n - 54300, hr⟩
                                                                                                                                                                              · by_cases h87 : n < 54400
                                                                                                                                                                                · have hr : n - 54350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 54350) + 54350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact pos_w1087 ⟨n - 54350, hr⟩
                                                                                                                                                                                · by_cases h88 : n < 54450
                                                                                                                                                                                  · have hr : n - 54400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 54400) + 54400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact pos_w1088 ⟨n - 54400, hr⟩
                                                                                                                                                                                  · by_cases h89 : n < 54500
                                                                                                                                                                                    · have hr : n - 54450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 54450) + 54450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact pos_w1089 ⟨n - 54450, hr⟩
                                                                                                                                                                                    · by_cases h90 : n < 54550
                                                                                                                                                                                      · have hr : n - 54500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 54500) + 54500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact pos_w1090 ⟨n - 54500, hr⟩
                                                                                                                                                                                      · by_cases h91 : n < 54600
                                                                                                                                                                                        · have hr : n - 54550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 54550) + 54550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact pos_w1091 ⟨n - 54550, hr⟩
                                                                                                                                                                                        · by_cases h92 : n < 54650
                                                                                                                                                                                          · have hr : n - 54600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 54600) + 54600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact pos_w1092 ⟨n - 54600, hr⟩
                                                                                                                                                                                          · by_cases h93 : n < 54700
                                                                                                                                                                                            · have hr : n - 54650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 54650) + 54650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact pos_w1093 ⟨n - 54650, hr⟩
                                                                                                                                                                                            · by_cases h94 : n < 54750
                                                                                                                                                                                              · have hr : n - 54700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 54700) + 54700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact pos_w1094 ⟨n - 54700, hr⟩
                                                                                                                                                                                              · by_cases h95 : n < 54800
                                                                                                                                                                                                · have hr : n - 54750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 54750) + 54750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact pos_w1095 ⟨n - 54750, hr⟩
                                                                                                                                                                                                · by_cases h96 : n < 54850
                                                                                                                                                                                                  · have hr : n - 54800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 54800) + 54800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact pos_w1096 ⟨n - 54800, hr⟩
                                                                                                                                                                                                  · by_cases h97 : n < 54900
                                                                                                                                                                                                    · have hr : n - 54850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 54850) + 54850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact pos_w1097 ⟨n - 54850, hr⟩
                                                                                                                                                                                                    · by_cases h98 : n < 54950
                                                                                                                                                                                                      · have hr : n - 54900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 54900) + 54900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact pos_w1098 ⟨n - 54900, hr⟩
                                                                                                                                                                                                      · by_cases h99 : n < 55000
                                                                                                                                                                                                        · have hr : n - 54950 < 50 := by omega
                                                                                                                                                                                                          have heq : n = (n - 54950) + 54950 := by omega
                                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                                          exact pos_w1099 ⟨n - 54950, hr⟩
                                                                                                                                                                                                        · omega

end IntMul.Kappa.R8.Bit.Oppbank.DimBound10


