-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound11
-- name    : IntMul_Kappa_R8_Data_BitOppbankDimBound11
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:04:29.909063+00:00
-- url     : https://prove2.me/theorems/2ade9567-e392-4412-a8a7-5ed0194f15e9
-- title:
--   Densified dimF $\le 22$ pack 11 ($[55000,60000)$)
-- statement:
--   Pack 11 of the densified dimension-field bound.
--
--   For every densified node index $n$ with $55000\le n<60000$, the 5-bit field $\mathrm{dimF}(n)$ extracted from $\mathrm{DIMT}$ satisfies
--   $$1\le \mathrm{dimF}(n)\le 22.$$
--   Proved by `decide` on successive `Fin 50` windows (no `native_decide`).
-- source:
--   R8 BitNB densified DIMT field bound; Fin-window decide packs

-- DimBound pack 11: dimF bounds on n ∈ [55000, 60000)

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

namespace IntMul.Kappa.R8.Bit.Oppbank.DimBound11

private theorem le_w1100 : ∀ n : Fin 50, dimF (n.val + 55000) ≤ 22 := by decide
private theorem pos_w1100 : ∀ n : Fin 50, 0 < dimF (n.val + 55000) := by decide
private theorem le_w1101 : ∀ n : Fin 50, dimF (n.val + 55050) ≤ 22 := by decide
private theorem pos_w1101 : ∀ n : Fin 50, 0 < dimF (n.val + 55050) := by decide
private theorem le_w1102 : ∀ n : Fin 50, dimF (n.val + 55100) ≤ 22 := by decide
private theorem pos_w1102 : ∀ n : Fin 50, 0 < dimF (n.val + 55100) := by decide
private theorem le_w1103 : ∀ n : Fin 50, dimF (n.val + 55150) ≤ 22 := by decide
private theorem pos_w1103 : ∀ n : Fin 50, 0 < dimF (n.val + 55150) := by decide
private theorem le_w1104 : ∀ n : Fin 50, dimF (n.val + 55200) ≤ 22 := by decide
private theorem pos_w1104 : ∀ n : Fin 50, 0 < dimF (n.val + 55200) := by decide
private theorem le_w1105 : ∀ n : Fin 50, dimF (n.val + 55250) ≤ 22 := by decide
private theorem pos_w1105 : ∀ n : Fin 50, 0 < dimF (n.val + 55250) := by decide
private theorem le_w1106 : ∀ n : Fin 50, dimF (n.val + 55300) ≤ 22 := by decide
private theorem pos_w1106 : ∀ n : Fin 50, 0 < dimF (n.val + 55300) := by decide
private theorem le_w1107 : ∀ n : Fin 50, dimF (n.val + 55350) ≤ 22 := by decide
private theorem pos_w1107 : ∀ n : Fin 50, 0 < dimF (n.val + 55350) := by decide
private theorem le_w1108 : ∀ n : Fin 50, dimF (n.val + 55400) ≤ 22 := by decide
private theorem pos_w1108 : ∀ n : Fin 50, 0 < dimF (n.val + 55400) := by decide
private theorem le_w1109 : ∀ n : Fin 50, dimF (n.val + 55450) ≤ 22 := by decide
private theorem pos_w1109 : ∀ n : Fin 50, 0 < dimF (n.val + 55450) := by decide
private theorem le_w1110 : ∀ n : Fin 50, dimF (n.val + 55500) ≤ 22 := by decide
private theorem pos_w1110 : ∀ n : Fin 50, 0 < dimF (n.val + 55500) := by decide
private theorem le_w1111 : ∀ n : Fin 50, dimF (n.val + 55550) ≤ 22 := by decide
private theorem pos_w1111 : ∀ n : Fin 50, 0 < dimF (n.val + 55550) := by decide
private theorem le_w1112 : ∀ n : Fin 50, dimF (n.val + 55600) ≤ 22 := by decide
private theorem pos_w1112 : ∀ n : Fin 50, 0 < dimF (n.val + 55600) := by decide
private theorem le_w1113 : ∀ n : Fin 50, dimF (n.val + 55650) ≤ 22 := by decide
private theorem pos_w1113 : ∀ n : Fin 50, 0 < dimF (n.val + 55650) := by decide
private theorem le_w1114 : ∀ n : Fin 50, dimF (n.val + 55700) ≤ 22 := by decide
private theorem pos_w1114 : ∀ n : Fin 50, 0 < dimF (n.val + 55700) := by decide
private theorem le_w1115 : ∀ n : Fin 50, dimF (n.val + 55750) ≤ 22 := by decide
private theorem pos_w1115 : ∀ n : Fin 50, 0 < dimF (n.val + 55750) := by decide
private theorem le_w1116 : ∀ n : Fin 50, dimF (n.val + 55800) ≤ 22 := by decide
private theorem pos_w1116 : ∀ n : Fin 50, 0 < dimF (n.val + 55800) := by decide
private theorem le_w1117 : ∀ n : Fin 50, dimF (n.val + 55850) ≤ 22 := by decide
private theorem pos_w1117 : ∀ n : Fin 50, 0 < dimF (n.val + 55850) := by decide
private theorem le_w1118 : ∀ n : Fin 50, dimF (n.val + 55900) ≤ 22 := by decide
private theorem pos_w1118 : ∀ n : Fin 50, 0 < dimF (n.val + 55900) := by decide
private theorem le_w1119 : ∀ n : Fin 50, dimF (n.val + 55950) ≤ 22 := by decide
private theorem pos_w1119 : ∀ n : Fin 50, 0 < dimF (n.val + 55950) := by decide
private theorem le_w1120 : ∀ n : Fin 50, dimF (n.val + 56000) ≤ 22 := by decide
private theorem pos_w1120 : ∀ n : Fin 50, 0 < dimF (n.val + 56000) := by decide
private theorem le_w1121 : ∀ n : Fin 50, dimF (n.val + 56050) ≤ 22 := by decide
private theorem pos_w1121 : ∀ n : Fin 50, 0 < dimF (n.val + 56050) := by decide
private theorem le_w1122 : ∀ n : Fin 50, dimF (n.val + 56100) ≤ 22 := by decide
private theorem pos_w1122 : ∀ n : Fin 50, 0 < dimF (n.val + 56100) := by decide
private theorem le_w1123 : ∀ n : Fin 50, dimF (n.val + 56150) ≤ 22 := by decide
private theorem pos_w1123 : ∀ n : Fin 50, 0 < dimF (n.val + 56150) := by decide
private theorem le_w1124 : ∀ n : Fin 50, dimF (n.val + 56200) ≤ 22 := by decide
private theorem pos_w1124 : ∀ n : Fin 50, 0 < dimF (n.val + 56200) := by decide
private theorem le_w1125 : ∀ n : Fin 50, dimF (n.val + 56250) ≤ 22 := by decide
private theorem pos_w1125 : ∀ n : Fin 50, 0 < dimF (n.val + 56250) := by decide
private theorem le_w1126 : ∀ n : Fin 50, dimF (n.val + 56300) ≤ 22 := by decide
private theorem pos_w1126 : ∀ n : Fin 50, 0 < dimF (n.val + 56300) := by decide
private theorem le_w1127 : ∀ n : Fin 50, dimF (n.val + 56350) ≤ 22 := by decide
private theorem pos_w1127 : ∀ n : Fin 50, 0 < dimF (n.val + 56350) := by decide
private theorem le_w1128 : ∀ n : Fin 50, dimF (n.val + 56400) ≤ 22 := by decide
private theorem pos_w1128 : ∀ n : Fin 50, 0 < dimF (n.val + 56400) := by decide
private theorem le_w1129 : ∀ n : Fin 50, dimF (n.val + 56450) ≤ 22 := by decide
private theorem pos_w1129 : ∀ n : Fin 50, 0 < dimF (n.val + 56450) := by decide
private theorem le_w1130 : ∀ n : Fin 50, dimF (n.val + 56500) ≤ 22 := by decide
private theorem pos_w1130 : ∀ n : Fin 50, 0 < dimF (n.val + 56500) := by decide
private theorem le_w1131 : ∀ n : Fin 50, dimF (n.val + 56550) ≤ 22 := by decide
private theorem pos_w1131 : ∀ n : Fin 50, 0 < dimF (n.val + 56550) := by decide
private theorem le_w1132 : ∀ n : Fin 50, dimF (n.val + 56600) ≤ 22 := by decide
private theorem pos_w1132 : ∀ n : Fin 50, 0 < dimF (n.val + 56600) := by decide
private theorem le_w1133 : ∀ n : Fin 50, dimF (n.val + 56650) ≤ 22 := by decide
private theorem pos_w1133 : ∀ n : Fin 50, 0 < dimF (n.val + 56650) := by decide
private theorem le_w1134 : ∀ n : Fin 50, dimF (n.val + 56700) ≤ 22 := by decide
private theorem pos_w1134 : ∀ n : Fin 50, 0 < dimF (n.val + 56700) := by decide
private theorem le_w1135 : ∀ n : Fin 50, dimF (n.val + 56750) ≤ 22 := by decide
private theorem pos_w1135 : ∀ n : Fin 50, 0 < dimF (n.val + 56750) := by decide
private theorem le_w1136 : ∀ n : Fin 50, dimF (n.val + 56800) ≤ 22 := by decide
private theorem pos_w1136 : ∀ n : Fin 50, 0 < dimF (n.val + 56800) := by decide
private theorem le_w1137 : ∀ n : Fin 50, dimF (n.val + 56850) ≤ 22 := by decide
private theorem pos_w1137 : ∀ n : Fin 50, 0 < dimF (n.val + 56850) := by decide
private theorem le_w1138 : ∀ n : Fin 50, dimF (n.val + 56900) ≤ 22 := by decide
private theorem pos_w1138 : ∀ n : Fin 50, 0 < dimF (n.val + 56900) := by decide
private theorem le_w1139 : ∀ n : Fin 50, dimF (n.val + 56950) ≤ 22 := by decide
private theorem pos_w1139 : ∀ n : Fin 50, 0 < dimF (n.val + 56950) := by decide
private theorem le_w1140 : ∀ n : Fin 50, dimF (n.val + 57000) ≤ 22 := by decide
private theorem pos_w1140 : ∀ n : Fin 50, 0 < dimF (n.val + 57000) := by decide
private theorem le_w1141 : ∀ n : Fin 50, dimF (n.val + 57050) ≤ 22 := by decide
private theorem pos_w1141 : ∀ n : Fin 50, 0 < dimF (n.val + 57050) := by decide
private theorem le_w1142 : ∀ n : Fin 50, dimF (n.val + 57100) ≤ 22 := by decide
private theorem pos_w1142 : ∀ n : Fin 50, 0 < dimF (n.val + 57100) := by decide
private theorem le_w1143 : ∀ n : Fin 50, dimF (n.val + 57150) ≤ 22 := by decide
private theorem pos_w1143 : ∀ n : Fin 50, 0 < dimF (n.val + 57150) := by decide
private theorem le_w1144 : ∀ n : Fin 50, dimF (n.val + 57200) ≤ 22 := by decide
private theorem pos_w1144 : ∀ n : Fin 50, 0 < dimF (n.val + 57200) := by decide
private theorem le_w1145 : ∀ n : Fin 50, dimF (n.val + 57250) ≤ 22 := by decide
private theorem pos_w1145 : ∀ n : Fin 50, 0 < dimF (n.val + 57250) := by decide
private theorem le_w1146 : ∀ n : Fin 50, dimF (n.val + 57300) ≤ 22 := by decide
private theorem pos_w1146 : ∀ n : Fin 50, 0 < dimF (n.val + 57300) := by decide
private theorem le_w1147 : ∀ n : Fin 50, dimF (n.val + 57350) ≤ 22 := by decide
private theorem pos_w1147 : ∀ n : Fin 50, 0 < dimF (n.val + 57350) := by decide
private theorem le_w1148 : ∀ n : Fin 50, dimF (n.val + 57400) ≤ 22 := by decide
private theorem pos_w1148 : ∀ n : Fin 50, 0 < dimF (n.val + 57400) := by decide
private theorem le_w1149 : ∀ n : Fin 50, dimF (n.val + 57450) ≤ 22 := by decide
private theorem pos_w1149 : ∀ n : Fin 50, 0 < dimF (n.val + 57450) := by decide
private theorem le_w1150 : ∀ n : Fin 50, dimF (n.val + 57500) ≤ 22 := by decide
private theorem pos_w1150 : ∀ n : Fin 50, 0 < dimF (n.val + 57500) := by decide
private theorem le_w1151 : ∀ n : Fin 50, dimF (n.val + 57550) ≤ 22 := by decide
private theorem pos_w1151 : ∀ n : Fin 50, 0 < dimF (n.val + 57550) := by decide
private theorem le_w1152 : ∀ n : Fin 50, dimF (n.val + 57600) ≤ 22 := by decide
private theorem pos_w1152 : ∀ n : Fin 50, 0 < dimF (n.val + 57600) := by decide
private theorem le_w1153 : ∀ n : Fin 50, dimF (n.val + 57650) ≤ 22 := by decide
private theorem pos_w1153 : ∀ n : Fin 50, 0 < dimF (n.val + 57650) := by decide
private theorem le_w1154 : ∀ n : Fin 50, dimF (n.val + 57700) ≤ 22 := by decide
private theorem pos_w1154 : ∀ n : Fin 50, 0 < dimF (n.val + 57700) := by decide
private theorem le_w1155 : ∀ n : Fin 50, dimF (n.val + 57750) ≤ 22 := by decide
private theorem pos_w1155 : ∀ n : Fin 50, 0 < dimF (n.val + 57750) := by decide
private theorem le_w1156 : ∀ n : Fin 50, dimF (n.val + 57800) ≤ 22 := by decide
private theorem pos_w1156 : ∀ n : Fin 50, 0 < dimF (n.val + 57800) := by decide
private theorem le_w1157 : ∀ n : Fin 50, dimF (n.val + 57850) ≤ 22 := by decide
private theorem pos_w1157 : ∀ n : Fin 50, 0 < dimF (n.val + 57850) := by decide
private theorem le_w1158 : ∀ n : Fin 50, dimF (n.val + 57900) ≤ 22 := by decide
private theorem pos_w1158 : ∀ n : Fin 50, 0 < dimF (n.val + 57900) := by decide
private theorem le_w1159 : ∀ n : Fin 50, dimF (n.val + 57950) ≤ 22 := by decide
private theorem pos_w1159 : ∀ n : Fin 50, 0 < dimF (n.val + 57950) := by decide
private theorem le_w1160 : ∀ n : Fin 50, dimF (n.val + 58000) ≤ 22 := by decide
private theorem pos_w1160 : ∀ n : Fin 50, 0 < dimF (n.val + 58000) := by decide
private theorem le_w1161 : ∀ n : Fin 50, dimF (n.val + 58050) ≤ 22 := by decide
private theorem pos_w1161 : ∀ n : Fin 50, 0 < dimF (n.val + 58050) := by decide
private theorem le_w1162 : ∀ n : Fin 50, dimF (n.val + 58100) ≤ 22 := by decide
private theorem pos_w1162 : ∀ n : Fin 50, 0 < dimF (n.val + 58100) := by decide
private theorem le_w1163 : ∀ n : Fin 50, dimF (n.val + 58150) ≤ 22 := by decide
private theorem pos_w1163 : ∀ n : Fin 50, 0 < dimF (n.val + 58150) := by decide
private theorem le_w1164 : ∀ n : Fin 50, dimF (n.val + 58200) ≤ 22 := by decide
private theorem pos_w1164 : ∀ n : Fin 50, 0 < dimF (n.val + 58200) := by decide
private theorem le_w1165 : ∀ n : Fin 50, dimF (n.val + 58250) ≤ 22 := by decide
private theorem pos_w1165 : ∀ n : Fin 50, 0 < dimF (n.val + 58250) := by decide
private theorem le_w1166 : ∀ n : Fin 50, dimF (n.val + 58300) ≤ 22 := by decide
private theorem pos_w1166 : ∀ n : Fin 50, 0 < dimF (n.val + 58300) := by decide
private theorem le_w1167 : ∀ n : Fin 50, dimF (n.val + 58350) ≤ 22 := by decide
private theorem pos_w1167 : ∀ n : Fin 50, 0 < dimF (n.val + 58350) := by decide
private theorem le_w1168 : ∀ n : Fin 50, dimF (n.val + 58400) ≤ 22 := by decide
private theorem pos_w1168 : ∀ n : Fin 50, 0 < dimF (n.val + 58400) := by decide
private theorem le_w1169 : ∀ n : Fin 50, dimF (n.val + 58450) ≤ 22 := by decide
private theorem pos_w1169 : ∀ n : Fin 50, 0 < dimF (n.val + 58450) := by decide
private theorem le_w1170 : ∀ n : Fin 50, dimF (n.val + 58500) ≤ 22 := by decide
private theorem pos_w1170 : ∀ n : Fin 50, 0 < dimF (n.val + 58500) := by decide
private theorem le_w1171 : ∀ n : Fin 50, dimF (n.val + 58550) ≤ 22 := by decide
private theorem pos_w1171 : ∀ n : Fin 50, 0 < dimF (n.val + 58550) := by decide
private theorem le_w1172 : ∀ n : Fin 50, dimF (n.val + 58600) ≤ 22 := by decide
private theorem pos_w1172 : ∀ n : Fin 50, 0 < dimF (n.val + 58600) := by decide
private theorem le_w1173 : ∀ n : Fin 50, dimF (n.val + 58650) ≤ 22 := by decide
private theorem pos_w1173 : ∀ n : Fin 50, 0 < dimF (n.val + 58650) := by decide
private theorem le_w1174 : ∀ n : Fin 50, dimF (n.val + 58700) ≤ 22 := by decide
private theorem pos_w1174 : ∀ n : Fin 50, 0 < dimF (n.val + 58700) := by decide
private theorem le_w1175 : ∀ n : Fin 50, dimF (n.val + 58750) ≤ 22 := by decide
private theorem pos_w1175 : ∀ n : Fin 50, 0 < dimF (n.val + 58750) := by decide
private theorem le_w1176 : ∀ n : Fin 50, dimF (n.val + 58800) ≤ 22 := by decide
private theorem pos_w1176 : ∀ n : Fin 50, 0 < dimF (n.val + 58800) := by decide
private theorem le_w1177 : ∀ n : Fin 50, dimF (n.val + 58850) ≤ 22 := by decide
private theorem pos_w1177 : ∀ n : Fin 50, 0 < dimF (n.val + 58850) := by decide
private theorem le_w1178 : ∀ n : Fin 50, dimF (n.val + 58900) ≤ 22 := by decide
private theorem pos_w1178 : ∀ n : Fin 50, 0 < dimF (n.val + 58900) := by decide
private theorem le_w1179 : ∀ n : Fin 50, dimF (n.val + 58950) ≤ 22 := by decide
private theorem pos_w1179 : ∀ n : Fin 50, 0 < dimF (n.val + 58950) := by decide
private theorem le_w1180 : ∀ n : Fin 50, dimF (n.val + 59000) ≤ 22 := by decide
private theorem pos_w1180 : ∀ n : Fin 50, 0 < dimF (n.val + 59000) := by decide
private theorem le_w1181 : ∀ n : Fin 50, dimF (n.val + 59050) ≤ 22 := by decide
private theorem pos_w1181 : ∀ n : Fin 50, 0 < dimF (n.val + 59050) := by decide
private theorem le_w1182 : ∀ n : Fin 50, dimF (n.val + 59100) ≤ 22 := by decide
private theorem pos_w1182 : ∀ n : Fin 50, 0 < dimF (n.val + 59100) := by decide
private theorem le_w1183 : ∀ n : Fin 50, dimF (n.val + 59150) ≤ 22 := by decide
private theorem pos_w1183 : ∀ n : Fin 50, 0 < dimF (n.val + 59150) := by decide
private theorem le_w1184 : ∀ n : Fin 50, dimF (n.val + 59200) ≤ 22 := by decide
private theorem pos_w1184 : ∀ n : Fin 50, 0 < dimF (n.val + 59200) := by decide
private theorem le_w1185 : ∀ n : Fin 50, dimF (n.val + 59250) ≤ 22 := by decide
private theorem pos_w1185 : ∀ n : Fin 50, 0 < dimF (n.val + 59250) := by decide
private theorem le_w1186 : ∀ n : Fin 50, dimF (n.val + 59300) ≤ 22 := by decide
private theorem pos_w1186 : ∀ n : Fin 50, 0 < dimF (n.val + 59300) := by decide
private theorem le_w1187 : ∀ n : Fin 50, dimF (n.val + 59350) ≤ 22 := by decide
private theorem pos_w1187 : ∀ n : Fin 50, 0 < dimF (n.val + 59350) := by decide
private theorem le_w1188 : ∀ n : Fin 50, dimF (n.val + 59400) ≤ 22 := by decide
private theorem pos_w1188 : ∀ n : Fin 50, 0 < dimF (n.val + 59400) := by decide
private theorem le_w1189 : ∀ n : Fin 50, dimF (n.val + 59450) ≤ 22 := by decide
private theorem pos_w1189 : ∀ n : Fin 50, 0 < dimF (n.val + 59450) := by decide
private theorem le_w1190 : ∀ n : Fin 50, dimF (n.val + 59500) ≤ 22 := by decide
private theorem pos_w1190 : ∀ n : Fin 50, 0 < dimF (n.val + 59500) := by decide
private theorem le_w1191 : ∀ n : Fin 50, dimF (n.val + 59550) ≤ 22 := by decide
private theorem pos_w1191 : ∀ n : Fin 50, 0 < dimF (n.val + 59550) := by decide
private theorem le_w1192 : ∀ n : Fin 50, dimF (n.val + 59600) ≤ 22 := by decide
private theorem pos_w1192 : ∀ n : Fin 50, 0 < dimF (n.val + 59600) := by decide
private theorem le_w1193 : ∀ n : Fin 50, dimF (n.val + 59650) ≤ 22 := by decide
private theorem pos_w1193 : ∀ n : Fin 50, 0 < dimF (n.val + 59650) := by decide
private theorem le_w1194 : ∀ n : Fin 50, dimF (n.val + 59700) ≤ 22 := by decide
private theorem pos_w1194 : ∀ n : Fin 50, 0 < dimF (n.val + 59700) := by decide
private theorem le_w1195 : ∀ n : Fin 50, dimF (n.val + 59750) ≤ 22 := by decide
private theorem pos_w1195 : ∀ n : Fin 50, 0 < dimF (n.val + 59750) := by decide
private theorem le_w1196 : ∀ n : Fin 50, dimF (n.val + 59800) ≤ 22 := by decide
private theorem pos_w1196 : ∀ n : Fin 50, 0 < dimF (n.val + 59800) := by decide
private theorem le_w1197 : ∀ n : Fin 50, dimF (n.val + 59850) ≤ 22 := by decide
private theorem pos_w1197 : ∀ n : Fin 50, 0 < dimF (n.val + 59850) := by decide
private theorem le_w1198 : ∀ n : Fin 50, dimF (n.val + 59900) ≤ 22 := by decide
private theorem pos_w1198 : ∀ n : Fin 50, 0 < dimF (n.val + 59900) := by decide
private theorem le_w1199 : ∀ n : Fin 50, dimF (n.val + 59950) ≤ 22 := by decide
private theorem pos_w1199 : ∀ n : Fin 50, 0 < dimF (n.val + 59950) := by decide

theorem dimF_le_22_range : ∀ n, 55000 ≤ n → n < 60000 → dimF n ≤ 22 := by
  intro n hlo hhi
  by_cases h0 : n < 55050
  · have hr : n - 55000 < 50 := by omega
    have heq : n = (n - 55000) + 55000 := by omega
    rw [heq]
    exact le_w1100 ⟨n - 55000, hr⟩
  · by_cases h1 : n < 55100
    · have hr : n - 55050 < 50 := by omega
      have heq : n = (n - 55050) + 55050 := by omega
      rw [heq]
      exact le_w1101 ⟨n - 55050, hr⟩
    · by_cases h2 : n < 55150
      · have hr : n - 55100 < 50 := by omega
        have heq : n = (n - 55100) + 55100 := by omega
        rw [heq]
        exact le_w1102 ⟨n - 55100, hr⟩
      · by_cases h3 : n < 55200
        · have hr : n - 55150 < 50 := by omega
          have heq : n = (n - 55150) + 55150 := by omega
          rw [heq]
          exact le_w1103 ⟨n - 55150, hr⟩
        · by_cases h4 : n < 55250
          · have hr : n - 55200 < 50 := by omega
            have heq : n = (n - 55200) + 55200 := by omega
            rw [heq]
            exact le_w1104 ⟨n - 55200, hr⟩
          · by_cases h5 : n < 55300
            · have hr : n - 55250 < 50 := by omega
              have heq : n = (n - 55250) + 55250 := by omega
              rw [heq]
              exact le_w1105 ⟨n - 55250, hr⟩
            · by_cases h6 : n < 55350
              · have hr : n - 55300 < 50 := by omega
                have heq : n = (n - 55300) + 55300 := by omega
                rw [heq]
                exact le_w1106 ⟨n - 55300, hr⟩
              · by_cases h7 : n < 55400
                · have hr : n - 55350 < 50 := by omega
                  have heq : n = (n - 55350) + 55350 := by omega
                  rw [heq]
                  exact le_w1107 ⟨n - 55350, hr⟩
                · by_cases h8 : n < 55450
                  · have hr : n - 55400 < 50 := by omega
                    have heq : n = (n - 55400) + 55400 := by omega
                    rw [heq]
                    exact le_w1108 ⟨n - 55400, hr⟩
                  · by_cases h9 : n < 55500
                    · have hr : n - 55450 < 50 := by omega
                      have heq : n = (n - 55450) + 55450 := by omega
                      rw [heq]
                      exact le_w1109 ⟨n - 55450, hr⟩
                    · by_cases h10 : n < 55550
                      · have hr : n - 55500 < 50 := by omega
                        have heq : n = (n - 55500) + 55500 := by omega
                        rw [heq]
                        exact le_w1110 ⟨n - 55500, hr⟩
                      · by_cases h11 : n < 55600
                        · have hr : n - 55550 < 50 := by omega
                          have heq : n = (n - 55550) + 55550 := by omega
                          rw [heq]
                          exact le_w1111 ⟨n - 55550, hr⟩
                        · by_cases h12 : n < 55650
                          · have hr : n - 55600 < 50 := by omega
                            have heq : n = (n - 55600) + 55600 := by omega
                            rw [heq]
                            exact le_w1112 ⟨n - 55600, hr⟩
                          · by_cases h13 : n < 55700
                            · have hr : n - 55650 < 50 := by omega
                              have heq : n = (n - 55650) + 55650 := by omega
                              rw [heq]
                              exact le_w1113 ⟨n - 55650, hr⟩
                            · by_cases h14 : n < 55750
                              · have hr : n - 55700 < 50 := by omega
                                have heq : n = (n - 55700) + 55700 := by omega
                                rw [heq]
                                exact le_w1114 ⟨n - 55700, hr⟩
                              · by_cases h15 : n < 55800
                                · have hr : n - 55750 < 50 := by omega
                                  have heq : n = (n - 55750) + 55750 := by omega
                                  rw [heq]
                                  exact le_w1115 ⟨n - 55750, hr⟩
                                · by_cases h16 : n < 55850
                                  · have hr : n - 55800 < 50 := by omega
                                    have heq : n = (n - 55800) + 55800 := by omega
                                    rw [heq]
                                    exact le_w1116 ⟨n - 55800, hr⟩
                                  · by_cases h17 : n < 55900
                                    · have hr : n - 55850 < 50 := by omega
                                      have heq : n = (n - 55850) + 55850 := by omega
                                      rw [heq]
                                      exact le_w1117 ⟨n - 55850, hr⟩
                                    · by_cases h18 : n < 55950
                                      · have hr : n - 55900 < 50 := by omega
                                        have heq : n = (n - 55900) + 55900 := by omega
                                        rw [heq]
                                        exact le_w1118 ⟨n - 55900, hr⟩
                                      · by_cases h19 : n < 56000
                                        · have hr : n - 55950 < 50 := by omega
                                          have heq : n = (n - 55950) + 55950 := by omega
                                          rw [heq]
                                          exact le_w1119 ⟨n - 55950, hr⟩
                                        · by_cases h20 : n < 56050
                                          · have hr : n - 56000 < 50 := by omega
                                            have heq : n = (n - 56000) + 56000 := by omega
                                            rw [heq]
                                            exact le_w1120 ⟨n - 56000, hr⟩
                                          · by_cases h21 : n < 56100
                                            · have hr : n - 56050 < 50 := by omega
                                              have heq : n = (n - 56050) + 56050 := by omega
                                              rw [heq]
                                              exact le_w1121 ⟨n - 56050, hr⟩
                                            · by_cases h22 : n < 56150
                                              · have hr : n - 56100 < 50 := by omega
                                                have heq : n = (n - 56100) + 56100 := by omega
                                                rw [heq]
                                                exact le_w1122 ⟨n - 56100, hr⟩
                                              · by_cases h23 : n < 56200
                                                · have hr : n - 56150 < 50 := by omega
                                                  have heq : n = (n - 56150) + 56150 := by omega
                                                  rw [heq]
                                                  exact le_w1123 ⟨n - 56150, hr⟩
                                                · by_cases h24 : n < 56250
                                                  · have hr : n - 56200 < 50 := by omega
                                                    have heq : n = (n - 56200) + 56200 := by omega
                                                    rw [heq]
                                                    exact le_w1124 ⟨n - 56200, hr⟩
                                                  · by_cases h25 : n < 56300
                                                    · have hr : n - 56250 < 50 := by omega
                                                      have heq : n = (n - 56250) + 56250 := by omega
                                                      rw [heq]
                                                      exact le_w1125 ⟨n - 56250, hr⟩
                                                    · by_cases h26 : n < 56350
                                                      · have hr : n - 56300 < 50 := by omega
                                                        have heq : n = (n - 56300) + 56300 := by omega
                                                        rw [heq]
                                                        exact le_w1126 ⟨n - 56300, hr⟩
                                                      · by_cases h27 : n < 56400
                                                        · have hr : n - 56350 < 50 := by omega
                                                          have heq : n = (n - 56350) + 56350 := by omega
                                                          rw [heq]
                                                          exact le_w1127 ⟨n - 56350, hr⟩
                                                        · by_cases h28 : n < 56450
                                                          · have hr : n - 56400 < 50 := by omega
                                                            have heq : n = (n - 56400) + 56400 := by omega
                                                            rw [heq]
                                                            exact le_w1128 ⟨n - 56400, hr⟩
                                                          · by_cases h29 : n < 56500
                                                            · have hr : n - 56450 < 50 := by omega
                                                              have heq : n = (n - 56450) + 56450 := by omega
                                                              rw [heq]
                                                              exact le_w1129 ⟨n - 56450, hr⟩
                                                            · by_cases h30 : n < 56550
                                                              · have hr : n - 56500 < 50 := by omega
                                                                have heq : n = (n - 56500) + 56500 := by omega
                                                                rw [heq]
                                                                exact le_w1130 ⟨n - 56500, hr⟩
                                                              · by_cases h31 : n < 56600
                                                                · have hr : n - 56550 < 50 := by omega
                                                                  have heq : n = (n - 56550) + 56550 := by omega
                                                                  rw [heq]
                                                                  exact le_w1131 ⟨n - 56550, hr⟩
                                                                · by_cases h32 : n < 56650
                                                                  · have hr : n - 56600 < 50 := by omega
                                                                    have heq : n = (n - 56600) + 56600 := by omega
                                                                    rw [heq]
                                                                    exact le_w1132 ⟨n - 56600, hr⟩
                                                                  · by_cases h33 : n < 56700
                                                                    · have hr : n - 56650 < 50 := by omega
                                                                      have heq : n = (n - 56650) + 56650 := by omega
                                                                      rw [heq]
                                                                      exact le_w1133 ⟨n - 56650, hr⟩
                                                                    · by_cases h34 : n < 56750
                                                                      · have hr : n - 56700 < 50 := by omega
                                                                        have heq : n = (n - 56700) + 56700 := by omega
                                                                        rw [heq]
                                                                        exact le_w1134 ⟨n - 56700, hr⟩
                                                                      · by_cases h35 : n < 56800
                                                                        · have hr : n - 56750 < 50 := by omega
                                                                          have heq : n = (n - 56750) + 56750 := by omega
                                                                          rw [heq]
                                                                          exact le_w1135 ⟨n - 56750, hr⟩
                                                                        · by_cases h36 : n < 56850
                                                                          · have hr : n - 56800 < 50 := by omega
                                                                            have heq : n = (n - 56800) + 56800 := by omega
                                                                            rw [heq]
                                                                            exact le_w1136 ⟨n - 56800, hr⟩
                                                                          · by_cases h37 : n < 56900
                                                                            · have hr : n - 56850 < 50 := by omega
                                                                              have heq : n = (n - 56850) + 56850 := by omega
                                                                              rw [heq]
                                                                              exact le_w1137 ⟨n - 56850, hr⟩
                                                                            · by_cases h38 : n < 56950
                                                                              · have hr : n - 56900 < 50 := by omega
                                                                                have heq : n = (n - 56900) + 56900 := by omega
                                                                                rw [heq]
                                                                                exact le_w1138 ⟨n - 56900, hr⟩
                                                                              · by_cases h39 : n < 57000
                                                                                · have hr : n - 56950 < 50 := by omega
                                                                                  have heq : n = (n - 56950) + 56950 := by omega
                                                                                  rw [heq]
                                                                                  exact le_w1139 ⟨n - 56950, hr⟩
                                                                                · by_cases h40 : n < 57050
                                                                                  · have hr : n - 57000 < 50 := by omega
                                                                                    have heq : n = (n - 57000) + 57000 := by omega
                                                                                    rw [heq]
                                                                                    exact le_w1140 ⟨n - 57000, hr⟩
                                                                                  · by_cases h41 : n < 57100
                                                                                    · have hr : n - 57050 < 50 := by omega
                                                                                      have heq : n = (n - 57050) + 57050 := by omega
                                                                                      rw [heq]
                                                                                      exact le_w1141 ⟨n - 57050, hr⟩
                                                                                    · by_cases h42 : n < 57150
                                                                                      · have hr : n - 57100 < 50 := by omega
                                                                                        have heq : n = (n - 57100) + 57100 := by omega
                                                                                        rw [heq]
                                                                                        exact le_w1142 ⟨n - 57100, hr⟩
                                                                                      · by_cases h43 : n < 57200
                                                                                        · have hr : n - 57150 < 50 := by omega
                                                                                          have heq : n = (n - 57150) + 57150 := by omega
                                                                                          rw [heq]
                                                                                          exact le_w1143 ⟨n - 57150, hr⟩
                                                                                        · by_cases h44 : n < 57250
                                                                                          · have hr : n - 57200 < 50 := by omega
                                                                                            have heq : n = (n - 57200) + 57200 := by omega
                                                                                            rw [heq]
                                                                                            exact le_w1144 ⟨n - 57200, hr⟩
                                                                                          · by_cases h45 : n < 57300
                                                                                            · have hr : n - 57250 < 50 := by omega
                                                                                              have heq : n = (n - 57250) + 57250 := by omega
                                                                                              rw [heq]
                                                                                              exact le_w1145 ⟨n - 57250, hr⟩
                                                                                            · by_cases h46 : n < 57350
                                                                                              · have hr : n - 57300 < 50 := by omega
                                                                                                have heq : n = (n - 57300) + 57300 := by omega
                                                                                                rw [heq]
                                                                                                exact le_w1146 ⟨n - 57300, hr⟩
                                                                                              · by_cases h47 : n < 57400
                                                                                                · have hr : n - 57350 < 50 := by omega
                                                                                                  have heq : n = (n - 57350) + 57350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact le_w1147 ⟨n - 57350, hr⟩
                                                                                                · by_cases h48 : n < 57450
                                                                                                  · have hr : n - 57400 < 50 := by omega
                                                                                                    have heq : n = (n - 57400) + 57400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact le_w1148 ⟨n - 57400, hr⟩
                                                                                                  · by_cases h49 : n < 57500
                                                                                                    · have hr : n - 57450 < 50 := by omega
                                                                                                      have heq : n = (n - 57450) + 57450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact le_w1149 ⟨n - 57450, hr⟩
                                                                                                    · by_cases h50 : n < 57550
                                                                                                      · have hr : n - 57500 < 50 := by omega
                                                                                                        have heq : n = (n - 57500) + 57500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact le_w1150 ⟨n - 57500, hr⟩
                                                                                                      · by_cases h51 : n < 57600
                                                                                                        · have hr : n - 57550 < 50 := by omega
                                                                                                          have heq : n = (n - 57550) + 57550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact le_w1151 ⟨n - 57550, hr⟩
                                                                                                        · by_cases h52 : n < 57650
                                                                                                          · have hr : n - 57600 < 50 := by omega
                                                                                                            have heq : n = (n - 57600) + 57600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact le_w1152 ⟨n - 57600, hr⟩
                                                                                                          · by_cases h53 : n < 57700
                                                                                                            · have hr : n - 57650 < 50 := by omega
                                                                                                              have heq : n = (n - 57650) + 57650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact le_w1153 ⟨n - 57650, hr⟩
                                                                                                            · by_cases h54 : n < 57750
                                                                                                              · have hr : n - 57700 < 50 := by omega
                                                                                                                have heq : n = (n - 57700) + 57700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact le_w1154 ⟨n - 57700, hr⟩
                                                                                                              · by_cases h55 : n < 57800
                                                                                                                · have hr : n - 57750 < 50 := by omega
                                                                                                                  have heq : n = (n - 57750) + 57750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact le_w1155 ⟨n - 57750, hr⟩
                                                                                                                · by_cases h56 : n < 57850
                                                                                                                  · have hr : n - 57800 < 50 := by omega
                                                                                                                    have heq : n = (n - 57800) + 57800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact le_w1156 ⟨n - 57800, hr⟩
                                                                                                                  · by_cases h57 : n < 57900
                                                                                                                    · have hr : n - 57850 < 50 := by omega
                                                                                                                      have heq : n = (n - 57850) + 57850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact le_w1157 ⟨n - 57850, hr⟩
                                                                                                                    · by_cases h58 : n < 57950
                                                                                                                      · have hr : n - 57900 < 50 := by omega
                                                                                                                        have heq : n = (n - 57900) + 57900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact le_w1158 ⟨n - 57900, hr⟩
                                                                                                                      · by_cases h59 : n < 58000
                                                                                                                        · have hr : n - 57950 < 50 := by omega
                                                                                                                          have heq : n = (n - 57950) + 57950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact le_w1159 ⟨n - 57950, hr⟩
                                                                                                                        · by_cases h60 : n < 58050
                                                                                                                          · have hr : n - 58000 < 50 := by omega
                                                                                                                            have heq : n = (n - 58000) + 58000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact le_w1160 ⟨n - 58000, hr⟩
                                                                                                                          · by_cases h61 : n < 58100
                                                                                                                            · have hr : n - 58050 < 50 := by omega
                                                                                                                              have heq : n = (n - 58050) + 58050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact le_w1161 ⟨n - 58050, hr⟩
                                                                                                                            · by_cases h62 : n < 58150
                                                                                                                              · have hr : n - 58100 < 50 := by omega
                                                                                                                                have heq : n = (n - 58100) + 58100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact le_w1162 ⟨n - 58100, hr⟩
                                                                                                                              · by_cases h63 : n < 58200
                                                                                                                                · have hr : n - 58150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 58150) + 58150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact le_w1163 ⟨n - 58150, hr⟩
                                                                                                                                · by_cases h64 : n < 58250
                                                                                                                                  · have hr : n - 58200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 58200) + 58200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact le_w1164 ⟨n - 58200, hr⟩
                                                                                                                                  · by_cases h65 : n < 58300
                                                                                                                                    · have hr : n - 58250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 58250) + 58250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact le_w1165 ⟨n - 58250, hr⟩
                                                                                                                                    · by_cases h66 : n < 58350
                                                                                                                                      · have hr : n - 58300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 58300) + 58300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact le_w1166 ⟨n - 58300, hr⟩
                                                                                                                                      · by_cases h67 : n < 58400
                                                                                                                                        · have hr : n - 58350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 58350) + 58350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact le_w1167 ⟨n - 58350, hr⟩
                                                                                                                                        · by_cases h68 : n < 58450
                                                                                                                                          · have hr : n - 58400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 58400) + 58400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact le_w1168 ⟨n - 58400, hr⟩
                                                                                                                                          · by_cases h69 : n < 58500
                                                                                                                                            · have hr : n - 58450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 58450) + 58450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact le_w1169 ⟨n - 58450, hr⟩
                                                                                                                                            · by_cases h70 : n < 58550
                                                                                                                                              · have hr : n - 58500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 58500) + 58500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact le_w1170 ⟨n - 58500, hr⟩
                                                                                                                                              · by_cases h71 : n < 58600
                                                                                                                                                · have hr : n - 58550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 58550) + 58550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact le_w1171 ⟨n - 58550, hr⟩
                                                                                                                                                · by_cases h72 : n < 58650
                                                                                                                                                  · have hr : n - 58600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 58600) + 58600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact le_w1172 ⟨n - 58600, hr⟩
                                                                                                                                                  · by_cases h73 : n < 58700
                                                                                                                                                    · have hr : n - 58650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 58650) + 58650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact le_w1173 ⟨n - 58650, hr⟩
                                                                                                                                                    · by_cases h74 : n < 58750
                                                                                                                                                      · have hr : n - 58700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 58700) + 58700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact le_w1174 ⟨n - 58700, hr⟩
                                                                                                                                                      · by_cases h75 : n < 58800
                                                                                                                                                        · have hr : n - 58750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 58750) + 58750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact le_w1175 ⟨n - 58750, hr⟩
                                                                                                                                                        · by_cases h76 : n < 58850
                                                                                                                                                          · have hr : n - 58800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 58800) + 58800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact le_w1176 ⟨n - 58800, hr⟩
                                                                                                                                                          · by_cases h77 : n < 58900
                                                                                                                                                            · have hr : n - 58850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 58850) + 58850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact le_w1177 ⟨n - 58850, hr⟩
                                                                                                                                                            · by_cases h78 : n < 58950
                                                                                                                                                              · have hr : n - 58900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 58900) + 58900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact le_w1178 ⟨n - 58900, hr⟩
                                                                                                                                                              · by_cases h79 : n < 59000
                                                                                                                                                                · have hr : n - 58950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 58950) + 58950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact le_w1179 ⟨n - 58950, hr⟩
                                                                                                                                                                · by_cases h80 : n < 59050
                                                                                                                                                                  · have hr : n - 59000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 59000) + 59000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact le_w1180 ⟨n - 59000, hr⟩
                                                                                                                                                                  · by_cases h81 : n < 59100
                                                                                                                                                                    · have hr : n - 59050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 59050) + 59050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact le_w1181 ⟨n - 59050, hr⟩
                                                                                                                                                                    · by_cases h82 : n < 59150
                                                                                                                                                                      · have hr : n - 59100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 59100) + 59100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact le_w1182 ⟨n - 59100, hr⟩
                                                                                                                                                                      · by_cases h83 : n < 59200
                                                                                                                                                                        · have hr : n - 59150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 59150) + 59150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact le_w1183 ⟨n - 59150, hr⟩
                                                                                                                                                                        · by_cases h84 : n < 59250
                                                                                                                                                                          · have hr : n - 59200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 59200) + 59200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact le_w1184 ⟨n - 59200, hr⟩
                                                                                                                                                                          · by_cases h85 : n < 59300
                                                                                                                                                                            · have hr : n - 59250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 59250) + 59250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact le_w1185 ⟨n - 59250, hr⟩
                                                                                                                                                                            · by_cases h86 : n < 59350
                                                                                                                                                                              · have hr : n - 59300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 59300) + 59300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact le_w1186 ⟨n - 59300, hr⟩
                                                                                                                                                                              · by_cases h87 : n < 59400
                                                                                                                                                                                · have hr : n - 59350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 59350) + 59350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact le_w1187 ⟨n - 59350, hr⟩
                                                                                                                                                                                · by_cases h88 : n < 59450
                                                                                                                                                                                  · have hr : n - 59400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 59400) + 59400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact le_w1188 ⟨n - 59400, hr⟩
                                                                                                                                                                                  · by_cases h89 : n < 59500
                                                                                                                                                                                    · have hr : n - 59450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 59450) + 59450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact le_w1189 ⟨n - 59450, hr⟩
                                                                                                                                                                                    · by_cases h90 : n < 59550
                                                                                                                                                                                      · have hr : n - 59500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 59500) + 59500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact le_w1190 ⟨n - 59500, hr⟩
                                                                                                                                                                                      · by_cases h91 : n < 59600
                                                                                                                                                                                        · have hr : n - 59550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 59550) + 59550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact le_w1191 ⟨n - 59550, hr⟩
                                                                                                                                                                                        · by_cases h92 : n < 59650
                                                                                                                                                                                          · have hr : n - 59600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 59600) + 59600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact le_w1192 ⟨n - 59600, hr⟩
                                                                                                                                                                                          · by_cases h93 : n < 59700
                                                                                                                                                                                            · have hr : n - 59650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 59650) + 59650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact le_w1193 ⟨n - 59650, hr⟩
                                                                                                                                                                                            · by_cases h94 : n < 59750
                                                                                                                                                                                              · have hr : n - 59700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 59700) + 59700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact le_w1194 ⟨n - 59700, hr⟩
                                                                                                                                                                                              · by_cases h95 : n < 59800
                                                                                                                                                                                                · have hr : n - 59750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 59750) + 59750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact le_w1195 ⟨n - 59750, hr⟩
                                                                                                                                                                                                · by_cases h96 : n < 59850
                                                                                                                                                                                                  · have hr : n - 59800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 59800) + 59800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact le_w1196 ⟨n - 59800, hr⟩
                                                                                                                                                                                                  · by_cases h97 : n < 59900
                                                                                                                                                                                                    · have hr : n - 59850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 59850) + 59850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact le_w1197 ⟨n - 59850, hr⟩
                                                                                                                                                                                                    · by_cases h98 : n < 59950
                                                                                                                                                                                                      · have hr : n - 59900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 59900) + 59900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact le_w1198 ⟨n - 59900, hr⟩
                                                                                                                                                                                                      · by_cases h99 : n < 60000
                                                                                                                                                                                                        · have hr : n - 59950 < 50 := by omega
                                                                                                                                                                                                          have heq : n = (n - 59950) + 59950 := by omega
                                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                                          exact le_w1199 ⟨n - 59950, hr⟩
                                                                                                                                                                                                        · omega

theorem dimF_pos_range : ∀ n, 55000 ≤ n → n < 60000 → 0 < dimF n := by
  intro n hlo hhi
  by_cases h0 : n < 55050
  · have hr : n - 55000 < 50 := by omega
    have heq : n = (n - 55000) + 55000 := by omega
    rw [heq]
    exact pos_w1100 ⟨n - 55000, hr⟩
  · by_cases h1 : n < 55100
    · have hr : n - 55050 < 50 := by omega
      have heq : n = (n - 55050) + 55050 := by omega
      rw [heq]
      exact pos_w1101 ⟨n - 55050, hr⟩
    · by_cases h2 : n < 55150
      · have hr : n - 55100 < 50 := by omega
        have heq : n = (n - 55100) + 55100 := by omega
        rw [heq]
        exact pos_w1102 ⟨n - 55100, hr⟩
      · by_cases h3 : n < 55200
        · have hr : n - 55150 < 50 := by omega
          have heq : n = (n - 55150) + 55150 := by omega
          rw [heq]
          exact pos_w1103 ⟨n - 55150, hr⟩
        · by_cases h4 : n < 55250
          · have hr : n - 55200 < 50 := by omega
            have heq : n = (n - 55200) + 55200 := by omega
            rw [heq]
            exact pos_w1104 ⟨n - 55200, hr⟩
          · by_cases h5 : n < 55300
            · have hr : n - 55250 < 50 := by omega
              have heq : n = (n - 55250) + 55250 := by omega
              rw [heq]
              exact pos_w1105 ⟨n - 55250, hr⟩
            · by_cases h6 : n < 55350
              · have hr : n - 55300 < 50 := by omega
                have heq : n = (n - 55300) + 55300 := by omega
                rw [heq]
                exact pos_w1106 ⟨n - 55300, hr⟩
              · by_cases h7 : n < 55400
                · have hr : n - 55350 < 50 := by omega
                  have heq : n = (n - 55350) + 55350 := by omega
                  rw [heq]
                  exact pos_w1107 ⟨n - 55350, hr⟩
                · by_cases h8 : n < 55450
                  · have hr : n - 55400 < 50 := by omega
                    have heq : n = (n - 55400) + 55400 := by omega
                    rw [heq]
                    exact pos_w1108 ⟨n - 55400, hr⟩
                  · by_cases h9 : n < 55500
                    · have hr : n - 55450 < 50 := by omega
                      have heq : n = (n - 55450) + 55450 := by omega
                      rw [heq]
                      exact pos_w1109 ⟨n - 55450, hr⟩
                    · by_cases h10 : n < 55550
                      · have hr : n - 55500 < 50 := by omega
                        have heq : n = (n - 55500) + 55500 := by omega
                        rw [heq]
                        exact pos_w1110 ⟨n - 55500, hr⟩
                      · by_cases h11 : n < 55600
                        · have hr : n - 55550 < 50 := by omega
                          have heq : n = (n - 55550) + 55550 := by omega
                          rw [heq]
                          exact pos_w1111 ⟨n - 55550, hr⟩
                        · by_cases h12 : n < 55650
                          · have hr : n - 55600 < 50 := by omega
                            have heq : n = (n - 55600) + 55600 := by omega
                            rw [heq]
                            exact pos_w1112 ⟨n - 55600, hr⟩
                          · by_cases h13 : n < 55700
                            · have hr : n - 55650 < 50 := by omega
                              have heq : n = (n - 55650) + 55650 := by omega
                              rw [heq]
                              exact pos_w1113 ⟨n - 55650, hr⟩
                            · by_cases h14 : n < 55750
                              · have hr : n - 55700 < 50 := by omega
                                have heq : n = (n - 55700) + 55700 := by omega
                                rw [heq]
                                exact pos_w1114 ⟨n - 55700, hr⟩
                              · by_cases h15 : n < 55800
                                · have hr : n - 55750 < 50 := by omega
                                  have heq : n = (n - 55750) + 55750 := by omega
                                  rw [heq]
                                  exact pos_w1115 ⟨n - 55750, hr⟩
                                · by_cases h16 : n < 55850
                                  · have hr : n - 55800 < 50 := by omega
                                    have heq : n = (n - 55800) + 55800 := by omega
                                    rw [heq]
                                    exact pos_w1116 ⟨n - 55800, hr⟩
                                  · by_cases h17 : n < 55900
                                    · have hr : n - 55850 < 50 := by omega
                                      have heq : n = (n - 55850) + 55850 := by omega
                                      rw [heq]
                                      exact pos_w1117 ⟨n - 55850, hr⟩
                                    · by_cases h18 : n < 55950
                                      · have hr : n - 55900 < 50 := by omega
                                        have heq : n = (n - 55900) + 55900 := by omega
                                        rw [heq]
                                        exact pos_w1118 ⟨n - 55900, hr⟩
                                      · by_cases h19 : n < 56000
                                        · have hr : n - 55950 < 50 := by omega
                                          have heq : n = (n - 55950) + 55950 := by omega
                                          rw [heq]
                                          exact pos_w1119 ⟨n - 55950, hr⟩
                                        · by_cases h20 : n < 56050
                                          · have hr : n - 56000 < 50 := by omega
                                            have heq : n = (n - 56000) + 56000 := by omega
                                            rw [heq]
                                            exact pos_w1120 ⟨n - 56000, hr⟩
                                          · by_cases h21 : n < 56100
                                            · have hr : n - 56050 < 50 := by omega
                                              have heq : n = (n - 56050) + 56050 := by omega
                                              rw [heq]
                                              exact pos_w1121 ⟨n - 56050, hr⟩
                                            · by_cases h22 : n < 56150
                                              · have hr : n - 56100 < 50 := by omega
                                                have heq : n = (n - 56100) + 56100 := by omega
                                                rw [heq]
                                                exact pos_w1122 ⟨n - 56100, hr⟩
                                              · by_cases h23 : n < 56200
                                                · have hr : n - 56150 < 50 := by omega
                                                  have heq : n = (n - 56150) + 56150 := by omega
                                                  rw [heq]
                                                  exact pos_w1123 ⟨n - 56150, hr⟩
                                                · by_cases h24 : n < 56250
                                                  · have hr : n - 56200 < 50 := by omega
                                                    have heq : n = (n - 56200) + 56200 := by omega
                                                    rw [heq]
                                                    exact pos_w1124 ⟨n - 56200, hr⟩
                                                  · by_cases h25 : n < 56300
                                                    · have hr : n - 56250 < 50 := by omega
                                                      have heq : n = (n - 56250) + 56250 := by omega
                                                      rw [heq]
                                                      exact pos_w1125 ⟨n - 56250, hr⟩
                                                    · by_cases h26 : n < 56350
                                                      · have hr : n - 56300 < 50 := by omega
                                                        have heq : n = (n - 56300) + 56300 := by omega
                                                        rw [heq]
                                                        exact pos_w1126 ⟨n - 56300, hr⟩
                                                      · by_cases h27 : n < 56400
                                                        · have hr : n - 56350 < 50 := by omega
                                                          have heq : n = (n - 56350) + 56350 := by omega
                                                          rw [heq]
                                                          exact pos_w1127 ⟨n - 56350, hr⟩
                                                        · by_cases h28 : n < 56450
                                                          · have hr : n - 56400 < 50 := by omega
                                                            have heq : n = (n - 56400) + 56400 := by omega
                                                            rw [heq]
                                                            exact pos_w1128 ⟨n - 56400, hr⟩
                                                          · by_cases h29 : n < 56500
                                                            · have hr : n - 56450 < 50 := by omega
                                                              have heq : n = (n - 56450) + 56450 := by omega
                                                              rw [heq]
                                                              exact pos_w1129 ⟨n - 56450, hr⟩
                                                            · by_cases h30 : n < 56550
                                                              · have hr : n - 56500 < 50 := by omega
                                                                have heq : n = (n - 56500) + 56500 := by omega
                                                                rw [heq]
                                                                exact pos_w1130 ⟨n - 56500, hr⟩
                                                              · by_cases h31 : n < 56600
                                                                · have hr : n - 56550 < 50 := by omega
                                                                  have heq : n = (n - 56550) + 56550 := by omega
                                                                  rw [heq]
                                                                  exact pos_w1131 ⟨n - 56550, hr⟩
                                                                · by_cases h32 : n < 56650
                                                                  · have hr : n - 56600 < 50 := by omega
                                                                    have heq : n = (n - 56600) + 56600 := by omega
                                                                    rw [heq]
                                                                    exact pos_w1132 ⟨n - 56600, hr⟩
                                                                  · by_cases h33 : n < 56700
                                                                    · have hr : n - 56650 < 50 := by omega
                                                                      have heq : n = (n - 56650) + 56650 := by omega
                                                                      rw [heq]
                                                                      exact pos_w1133 ⟨n - 56650, hr⟩
                                                                    · by_cases h34 : n < 56750
                                                                      · have hr : n - 56700 < 50 := by omega
                                                                        have heq : n = (n - 56700) + 56700 := by omega
                                                                        rw [heq]
                                                                        exact pos_w1134 ⟨n - 56700, hr⟩
                                                                      · by_cases h35 : n < 56800
                                                                        · have hr : n - 56750 < 50 := by omega
                                                                          have heq : n = (n - 56750) + 56750 := by omega
                                                                          rw [heq]
                                                                          exact pos_w1135 ⟨n - 56750, hr⟩
                                                                        · by_cases h36 : n < 56850
                                                                          · have hr : n - 56800 < 50 := by omega
                                                                            have heq : n = (n - 56800) + 56800 := by omega
                                                                            rw [heq]
                                                                            exact pos_w1136 ⟨n - 56800, hr⟩
                                                                          · by_cases h37 : n < 56900
                                                                            · have hr : n - 56850 < 50 := by omega
                                                                              have heq : n = (n - 56850) + 56850 := by omega
                                                                              rw [heq]
                                                                              exact pos_w1137 ⟨n - 56850, hr⟩
                                                                            · by_cases h38 : n < 56950
                                                                              · have hr : n - 56900 < 50 := by omega
                                                                                have heq : n = (n - 56900) + 56900 := by omega
                                                                                rw [heq]
                                                                                exact pos_w1138 ⟨n - 56900, hr⟩
                                                                              · by_cases h39 : n < 57000
                                                                                · have hr : n - 56950 < 50 := by omega
                                                                                  have heq : n = (n - 56950) + 56950 := by omega
                                                                                  rw [heq]
                                                                                  exact pos_w1139 ⟨n - 56950, hr⟩
                                                                                · by_cases h40 : n < 57050
                                                                                  · have hr : n - 57000 < 50 := by omega
                                                                                    have heq : n = (n - 57000) + 57000 := by omega
                                                                                    rw [heq]
                                                                                    exact pos_w1140 ⟨n - 57000, hr⟩
                                                                                  · by_cases h41 : n < 57100
                                                                                    · have hr : n - 57050 < 50 := by omega
                                                                                      have heq : n = (n - 57050) + 57050 := by omega
                                                                                      rw [heq]
                                                                                      exact pos_w1141 ⟨n - 57050, hr⟩
                                                                                    · by_cases h42 : n < 57150
                                                                                      · have hr : n - 57100 < 50 := by omega
                                                                                        have heq : n = (n - 57100) + 57100 := by omega
                                                                                        rw [heq]
                                                                                        exact pos_w1142 ⟨n - 57100, hr⟩
                                                                                      · by_cases h43 : n < 57200
                                                                                        · have hr : n - 57150 < 50 := by omega
                                                                                          have heq : n = (n - 57150) + 57150 := by omega
                                                                                          rw [heq]
                                                                                          exact pos_w1143 ⟨n - 57150, hr⟩
                                                                                        · by_cases h44 : n < 57250
                                                                                          · have hr : n - 57200 < 50 := by omega
                                                                                            have heq : n = (n - 57200) + 57200 := by omega
                                                                                            rw [heq]
                                                                                            exact pos_w1144 ⟨n - 57200, hr⟩
                                                                                          · by_cases h45 : n < 57300
                                                                                            · have hr : n - 57250 < 50 := by omega
                                                                                              have heq : n = (n - 57250) + 57250 := by omega
                                                                                              rw [heq]
                                                                                              exact pos_w1145 ⟨n - 57250, hr⟩
                                                                                            · by_cases h46 : n < 57350
                                                                                              · have hr : n - 57300 < 50 := by omega
                                                                                                have heq : n = (n - 57300) + 57300 := by omega
                                                                                                rw [heq]
                                                                                                exact pos_w1146 ⟨n - 57300, hr⟩
                                                                                              · by_cases h47 : n < 57400
                                                                                                · have hr : n - 57350 < 50 := by omega
                                                                                                  have heq : n = (n - 57350) + 57350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact pos_w1147 ⟨n - 57350, hr⟩
                                                                                                · by_cases h48 : n < 57450
                                                                                                  · have hr : n - 57400 < 50 := by omega
                                                                                                    have heq : n = (n - 57400) + 57400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact pos_w1148 ⟨n - 57400, hr⟩
                                                                                                  · by_cases h49 : n < 57500
                                                                                                    · have hr : n - 57450 < 50 := by omega
                                                                                                      have heq : n = (n - 57450) + 57450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact pos_w1149 ⟨n - 57450, hr⟩
                                                                                                    · by_cases h50 : n < 57550
                                                                                                      · have hr : n - 57500 < 50 := by omega
                                                                                                        have heq : n = (n - 57500) + 57500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact pos_w1150 ⟨n - 57500, hr⟩
                                                                                                      · by_cases h51 : n < 57600
                                                                                                        · have hr : n - 57550 < 50 := by omega
                                                                                                          have heq : n = (n - 57550) + 57550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact pos_w1151 ⟨n - 57550, hr⟩
                                                                                                        · by_cases h52 : n < 57650
                                                                                                          · have hr : n - 57600 < 50 := by omega
                                                                                                            have heq : n = (n - 57600) + 57600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact pos_w1152 ⟨n - 57600, hr⟩
                                                                                                          · by_cases h53 : n < 57700
                                                                                                            · have hr : n - 57650 < 50 := by omega
                                                                                                              have heq : n = (n - 57650) + 57650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact pos_w1153 ⟨n - 57650, hr⟩
                                                                                                            · by_cases h54 : n < 57750
                                                                                                              · have hr : n - 57700 < 50 := by omega
                                                                                                                have heq : n = (n - 57700) + 57700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact pos_w1154 ⟨n - 57700, hr⟩
                                                                                                              · by_cases h55 : n < 57800
                                                                                                                · have hr : n - 57750 < 50 := by omega
                                                                                                                  have heq : n = (n - 57750) + 57750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact pos_w1155 ⟨n - 57750, hr⟩
                                                                                                                · by_cases h56 : n < 57850
                                                                                                                  · have hr : n - 57800 < 50 := by omega
                                                                                                                    have heq : n = (n - 57800) + 57800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact pos_w1156 ⟨n - 57800, hr⟩
                                                                                                                  · by_cases h57 : n < 57900
                                                                                                                    · have hr : n - 57850 < 50 := by omega
                                                                                                                      have heq : n = (n - 57850) + 57850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact pos_w1157 ⟨n - 57850, hr⟩
                                                                                                                    · by_cases h58 : n < 57950
                                                                                                                      · have hr : n - 57900 < 50 := by omega
                                                                                                                        have heq : n = (n - 57900) + 57900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact pos_w1158 ⟨n - 57900, hr⟩
                                                                                                                      · by_cases h59 : n < 58000
                                                                                                                        · have hr : n - 57950 < 50 := by omega
                                                                                                                          have heq : n = (n - 57950) + 57950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact pos_w1159 ⟨n - 57950, hr⟩
                                                                                                                        · by_cases h60 : n < 58050
                                                                                                                          · have hr : n - 58000 < 50 := by omega
                                                                                                                            have heq : n = (n - 58000) + 58000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact pos_w1160 ⟨n - 58000, hr⟩
                                                                                                                          · by_cases h61 : n < 58100
                                                                                                                            · have hr : n - 58050 < 50 := by omega
                                                                                                                              have heq : n = (n - 58050) + 58050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact pos_w1161 ⟨n - 58050, hr⟩
                                                                                                                            · by_cases h62 : n < 58150
                                                                                                                              · have hr : n - 58100 < 50 := by omega
                                                                                                                                have heq : n = (n - 58100) + 58100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact pos_w1162 ⟨n - 58100, hr⟩
                                                                                                                              · by_cases h63 : n < 58200
                                                                                                                                · have hr : n - 58150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 58150) + 58150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact pos_w1163 ⟨n - 58150, hr⟩
                                                                                                                                · by_cases h64 : n < 58250
                                                                                                                                  · have hr : n - 58200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 58200) + 58200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact pos_w1164 ⟨n - 58200, hr⟩
                                                                                                                                  · by_cases h65 : n < 58300
                                                                                                                                    · have hr : n - 58250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 58250) + 58250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact pos_w1165 ⟨n - 58250, hr⟩
                                                                                                                                    · by_cases h66 : n < 58350
                                                                                                                                      · have hr : n - 58300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 58300) + 58300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact pos_w1166 ⟨n - 58300, hr⟩
                                                                                                                                      · by_cases h67 : n < 58400
                                                                                                                                        · have hr : n - 58350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 58350) + 58350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact pos_w1167 ⟨n - 58350, hr⟩
                                                                                                                                        · by_cases h68 : n < 58450
                                                                                                                                          · have hr : n - 58400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 58400) + 58400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact pos_w1168 ⟨n - 58400, hr⟩
                                                                                                                                          · by_cases h69 : n < 58500
                                                                                                                                            · have hr : n - 58450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 58450) + 58450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact pos_w1169 ⟨n - 58450, hr⟩
                                                                                                                                            · by_cases h70 : n < 58550
                                                                                                                                              · have hr : n - 58500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 58500) + 58500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact pos_w1170 ⟨n - 58500, hr⟩
                                                                                                                                              · by_cases h71 : n < 58600
                                                                                                                                                · have hr : n - 58550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 58550) + 58550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact pos_w1171 ⟨n - 58550, hr⟩
                                                                                                                                                · by_cases h72 : n < 58650
                                                                                                                                                  · have hr : n - 58600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 58600) + 58600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact pos_w1172 ⟨n - 58600, hr⟩
                                                                                                                                                  · by_cases h73 : n < 58700
                                                                                                                                                    · have hr : n - 58650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 58650) + 58650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact pos_w1173 ⟨n - 58650, hr⟩
                                                                                                                                                    · by_cases h74 : n < 58750
                                                                                                                                                      · have hr : n - 58700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 58700) + 58700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact pos_w1174 ⟨n - 58700, hr⟩
                                                                                                                                                      · by_cases h75 : n < 58800
                                                                                                                                                        · have hr : n - 58750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 58750) + 58750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact pos_w1175 ⟨n - 58750, hr⟩
                                                                                                                                                        · by_cases h76 : n < 58850
                                                                                                                                                          · have hr : n - 58800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 58800) + 58800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact pos_w1176 ⟨n - 58800, hr⟩
                                                                                                                                                          · by_cases h77 : n < 58900
                                                                                                                                                            · have hr : n - 58850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 58850) + 58850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact pos_w1177 ⟨n - 58850, hr⟩
                                                                                                                                                            · by_cases h78 : n < 58950
                                                                                                                                                              · have hr : n - 58900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 58900) + 58900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact pos_w1178 ⟨n - 58900, hr⟩
                                                                                                                                                              · by_cases h79 : n < 59000
                                                                                                                                                                · have hr : n - 58950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 58950) + 58950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact pos_w1179 ⟨n - 58950, hr⟩
                                                                                                                                                                · by_cases h80 : n < 59050
                                                                                                                                                                  · have hr : n - 59000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 59000) + 59000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact pos_w1180 ⟨n - 59000, hr⟩
                                                                                                                                                                  · by_cases h81 : n < 59100
                                                                                                                                                                    · have hr : n - 59050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 59050) + 59050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact pos_w1181 ⟨n - 59050, hr⟩
                                                                                                                                                                    · by_cases h82 : n < 59150
                                                                                                                                                                      · have hr : n - 59100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 59100) + 59100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact pos_w1182 ⟨n - 59100, hr⟩
                                                                                                                                                                      · by_cases h83 : n < 59200
                                                                                                                                                                        · have hr : n - 59150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 59150) + 59150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact pos_w1183 ⟨n - 59150, hr⟩
                                                                                                                                                                        · by_cases h84 : n < 59250
                                                                                                                                                                          · have hr : n - 59200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 59200) + 59200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact pos_w1184 ⟨n - 59200, hr⟩
                                                                                                                                                                          · by_cases h85 : n < 59300
                                                                                                                                                                            · have hr : n - 59250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 59250) + 59250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact pos_w1185 ⟨n - 59250, hr⟩
                                                                                                                                                                            · by_cases h86 : n < 59350
                                                                                                                                                                              · have hr : n - 59300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 59300) + 59300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact pos_w1186 ⟨n - 59300, hr⟩
                                                                                                                                                                              · by_cases h87 : n < 59400
                                                                                                                                                                                · have hr : n - 59350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 59350) + 59350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact pos_w1187 ⟨n - 59350, hr⟩
                                                                                                                                                                                · by_cases h88 : n < 59450
                                                                                                                                                                                  · have hr : n - 59400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 59400) + 59400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact pos_w1188 ⟨n - 59400, hr⟩
                                                                                                                                                                                  · by_cases h89 : n < 59500
                                                                                                                                                                                    · have hr : n - 59450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 59450) + 59450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact pos_w1189 ⟨n - 59450, hr⟩
                                                                                                                                                                                    · by_cases h90 : n < 59550
                                                                                                                                                                                      · have hr : n - 59500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 59500) + 59500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact pos_w1190 ⟨n - 59500, hr⟩
                                                                                                                                                                                      · by_cases h91 : n < 59600
                                                                                                                                                                                        · have hr : n - 59550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 59550) + 59550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact pos_w1191 ⟨n - 59550, hr⟩
                                                                                                                                                                                        · by_cases h92 : n < 59650
                                                                                                                                                                                          · have hr : n - 59600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 59600) + 59600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact pos_w1192 ⟨n - 59600, hr⟩
                                                                                                                                                                                          · by_cases h93 : n < 59700
                                                                                                                                                                                            · have hr : n - 59650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 59650) + 59650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact pos_w1193 ⟨n - 59650, hr⟩
                                                                                                                                                                                            · by_cases h94 : n < 59750
                                                                                                                                                                                              · have hr : n - 59700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 59700) + 59700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact pos_w1194 ⟨n - 59700, hr⟩
                                                                                                                                                                                              · by_cases h95 : n < 59800
                                                                                                                                                                                                · have hr : n - 59750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 59750) + 59750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact pos_w1195 ⟨n - 59750, hr⟩
                                                                                                                                                                                                · by_cases h96 : n < 59850
                                                                                                                                                                                                  · have hr : n - 59800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 59800) + 59800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact pos_w1196 ⟨n - 59800, hr⟩
                                                                                                                                                                                                  · by_cases h97 : n < 59900
                                                                                                                                                                                                    · have hr : n - 59850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 59850) + 59850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact pos_w1197 ⟨n - 59850, hr⟩
                                                                                                                                                                                                    · by_cases h98 : n < 59950
                                                                                                                                                                                                      · have hr : n - 59900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 59900) + 59900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact pos_w1198 ⟨n - 59900, hr⟩
                                                                                                                                                                                                      · by_cases h99 : n < 60000
                                                                                                                                                                                                        · have hr : n - 59950 < 50 := by omega
                                                                                                                                                                                                          have heq : n = (n - 59950) + 59950 := by omega
                                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                                          exact pos_w1199 ⟨n - 59950, hr⟩
                                                                                                                                                                                                        · omega

end IntMul.Kappa.R8.Bit.Oppbank.DimBound11


