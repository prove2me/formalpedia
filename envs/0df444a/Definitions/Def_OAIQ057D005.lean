-- Prove2me | Definitions.Def_OAIQ057D005
-- name    : OAIQ057D005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T20:44:43.182763+00:00
-- url     : https://prove2.me/theorems/1b9a9f91-05a3-4fb9-acc0-84d794d75156
-- title:
--   Definitions bundle OAIQ057D005 of the split of OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DimensionTen.exists_channel_fin21`, carved from OpenAI's openai/math development (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 269 declarations of OpenAI's Lean: 269 definitions. The definitions and types are `OAI.DimensionTen.Mod131.pow9_4_mul_t`, `OAI.DimensionTen.Mod131.pow9_4_q`, `OAI.DimensionTen.Mod131.pow9_64`, `OAI.DimensionTen.Mod131.pow9_64_mul_t`, `OAI.DimensionTen.Mod131.pow9_64_q`, `OAI.DimensionTen.Mod131.pow9_65`, `OAI.DimensionTen.Mod131.pow9_65_mul_t`, `OAI.DimensionTen.Mod131.pow9_65_q`, `OAI.DimensionTen.Mod131.pow9_8`, `OAI.DimensionTen.Mod131.pow9_8_mul_t`, `OAI.DimensionTen.Mod131.pow9_8_q`, `OAI.DimensionTen.Mod131.separable_bezout_t`, `OAI.DimensionTen.Mod131.u0`, `OAI.DimensionTen.Mod139.a1`, `OAI.DimensionTen.Mod139.b1`, `OAI.DimensionTen.Mod139.bezout1_t`, `OAI.DimensionTen.Mod139.da`, `OAI.DimensionTen.Mod139.db`, `OAI.DimensionTen.Mod139.derivative_extra`, `OAI.DimensionTen.Mod139.df`, `OAI.DimensionTen.Mod139.div1_f`, `OAI.DimensionTen.Mod139.div1_u1`, `OAI.DimensionTen.Mod139.f`, `OAI.DimensionTen.Mod139.factor1_f_t`, `OAI.DimensionTen.Mod139.factor1_u1_t`, `OAI.DimensionTen.Mod139.g1`, `OAI.DimensionTen.Mod139.pow10_138`, `OAI.DimensionTen.Mod139.pow10_138_mul_t`, `OAI.DimensionTen.Mod139.pow10_138_q`, `OAI.DimensionTen.Mod139.pow10_139`, `OAI.DimensionTen.Mod139.pow10_139_mul_t`, `OAI.DimensionTen.Mod139.pow10_139_q`, `OAI.DimensionTen.Mod139.pow10_16`, `OAI.DimensionTen.Mod139.pow10_16_mul_t`, `OAI.DimensionTen.Mod139.pow10_16_q`, `OAI.DimensionTen.Mod139.pow10_17`, `OAI.DimensionTen.Mod139.pow10_17_mul_t`, `OAI.DimensionTen.Mod139.pow10_17_q`, `OAI.DimensionTen.Mod139.pow10_2`, `OAI.DimensionTen.Mod139.pow10_2_mul_t` and 229 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, lean/OAI/InformationTheory, in whole or in part: [`Quantum_DimensionTen_Mod131Model`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod131Model.lean), [`Quantum_DimensionTen_Mod131Powers05`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod131Powers05.lean), [`Quantum_DimensionTen_Mod131Result`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod131Result.lean), [`Quantum_DimensionTen_Mod139Model`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod139Model.lean), [`Quantum_DimensionTen_Mod139Powers01`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod139Powers01.lean), [`Quantum_DimensionTen_Mod139Powers05`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod139Powers05.lean), [`Quantum_DimensionTen_Mod139Powers06`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod139Powers06.lean), [`Quantum_DimensionTen_Mod139Powers07`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod139Powers07.lean), [`Quantum_DimensionTen_Mod139Powers08`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod139Powers08.lean), [`Quantum_DimensionTen_Mod139Powers09`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod139Powers09.lean), [`Quantum_DimensionTen_Mod139Result`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod139Result.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ057D009`; the statements `OAI_DimensionTen_fixed_mod139`, `OAI.DimensionTen.fixed_mod139_s2`, `OAI_DimensionTen_pow_mod139`, `OAI.DimensionTen.pow_mod139_s2`, `OAI_DimensionTen_root_action_full_symmetric` and `OAI.DimensionTen.root_action_full_symmetric_s2`.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis, lean/OAI/InformationTheory at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131

def u0 {R : Type*} [CommRing R] (z : R) : R := (0 + z * 1)

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Powers05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131

def pow9_4_q {R : Type*} [CommRing R] (z : R) : R := (94 + z * (122 + z * (89 + z * (78 + z * (107 + z * (35 + z * (111 + z * (25 + z * (44 + z * (10 + z * (5 + z * (42 + z * (5 + z * (15 + z * (42 + z * (72 + z * (59 + z * (89 + z * 41))))))))))))))))))

def pow9_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * ((-13) + z * ((-22) + z * ((-73) + z * ((-53) + z * ((-84) + z * (8 + z * (28 + z * (24 + z * (48 + z * (207 + z * (122 + z * (253 + z * (238 + z * (399 + z * (325 + z * (478 + z * (419 + z * (510 + z * (377 + z * (546 + z * (481 + z * (533 + z * (526 + z * (551 + z * (493 + z * (458 + z * (355 + z * (402 + z * (265 + z * (254 + z * (250 + z * (178 + z * (63 + z * (97 + z * (28 + z * (14 + z * (23 + z * 8))))))))))))))))))))))))))))))))))))))


def pow9_8 {R : Type*} [CommRing R] (z : R) : R := (75 + z * (74 + z * (9 + z * (76 + z * (68 + z * (123 + z * (121 + z * (23 + z * (52 + z * (7 + z * (120 + z * (102 + z * (7 + z * (83 + z * (34 + z * (121 + z * (22 + z * (56 + z * (103 + z * 57)))))))))))))))))))

def pow9_8_q {R : Type*} [CommRing R] (z : R) : R := (31 + z * (3 + z * (40 + z * (72 + z * (43 + z * (6 + z * (83 + z * (92 + z * (122 + z * (93 + z * (114 + z * (77 + z * (115 + z * (31 + z * (84 + z * (122 + z * (122 + z * (83 + z * 15))))))))))))))))))

def pow9_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (16 + z * (3 + z * ((-7) + z * (37 + z * (16 + z * (19 + z * (81 + z * ((-3) + z * ((-43) + z * ((-2) + z * (3 + z * ((-113) + z * ((-60) + z * (31 + z * (21 + z * (11 + z * (105 + z * (97 + z * (152 + z * ((-12) + z * (53 + z * (125 + z * (238 + z * (242 + z * (258 + z * (199 + z * (155 + z * (182 + z * (247 + z * (390 + z * (396 + z * (374 + z * (271 + z * (132 + z * (102 + z * (144 + z * (188 + z * (149 + z * 59))))))))))))))))))))))))))))))))))))))


def pow9_64 {R : Type*} [CommRing R] (z : R) : R := (45 + z * (10 + z * (101 + z * (111 + z * (121 + z * (86 + z * (104 + z * (28 + z * (100 + z * (21 + z * (123 + z * (89 + z * (66 + z * (43 + z * (59 + z * (107 + z * (22 + z * (58 + z * (34 + z * 43)))))))))))))))))))

def pow9_64_q {R : Type*} [CommRing R] (z : R) : R := (59 + z * (49 + z * (57 + z * (105 + z * (17 + z * (68 + z * (54 + z * (30 + z * (119 + z * (40 + z * (10 + z * (119 + z * (23 + z * (119 + z * (19 + z * (66 + z * (22 + z * (122 + z * 55))))))))))))))))))

def pow9_64_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-6) + z * (11 + z * (37 + z * (83 + z * (118 + z * (121 + z * (179 + z * (122 + z * (48 + z * (80 + z * (77 + z * (119 + z * (186 + z * (99 + z * (222 + z * (220 + z * (100 + z * (162 + z * (59 + z * (97 + z * (161 + z * (62 + z * (16 + z * (102 + z * ((-34) + z * ((-40) + z * ((-10) + z * (113 + z * (23 + z * ((-29) + z * ((-65) + z * (46 + z * ((-15) + z * ((-60) + z * (8 + z * ((-51) + z * ((-32) + z * ((-22) + z * 6))))))))))))))))))))))))))))))))))))))


def pow9_65 {R : Type*} [CommRing R] (z : R) : R := (43 + z * (83 + z * (12 + z * (17 + z * (33 + z * (106 + z * (79 + z * (93 + z * (26 + z * (101 + z * (102 + z * (68 + z * (115 + z * (40 + z * (61 + z * (68 + z * (68 + z * (103 + z * (102 + z * 108)))))))))))))))))))

def pow9_65_q {R : Type*} [CommRing R] (z : R) : R := (104 + z * (93 + z * (85 + z * (65 + z * (16 + z * (128 + z * (4 + z * (0 + z * (26 + z * (67 + z * (105 + z * (27 + z * (73 + z * (39 + z * (75 + z * (29 + z * (26 + z * (118 + z * 36))))))))))))))))))

def pow9_65_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-28) + z * ((-56) + z * ((-49) + z * ((-48) + z * (46 + z * ((-45) + z * (81 + z * (88 + z * (182 + z * (123 + z * (170 + z * (179 + z * (196 + z * (21 + z * (124 + z * (252 + z * (181 + z * (184 + z * (111 + z * (226 + z * (246 + z * (105 + z * (181 + z * (278 + z * (161 + z * (89 + z * (37 + z * (160 + z * ((-21) + z * (52 + z * (21 + z * (67 + z * (74 + z * ((-10) + z * (43 + z * ((-14) + z * (5 + z * (19 + z * 25))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Result
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131

def separable_bezout_t {R : Type*} [CommRing R] (z : R) : R := (68 + z * (172 + z * (283 + z * (319 + z * (324 + z * (307 + z * (365 + z * (541 + z * (646 + z * (556 + z * (685 + z * (804 + z * (807 + z * (997 + z * (1041 + z * (941 + z * (1063 + z * (1117 + z * (1343 + z * (1219 + z * (1055 + z * (1126 + z * (1013 + z * (899 + z * (861 + z * (1011 + z * (789 + z * (748 + z * (742 + z * (660 + z * (607 + z * (444 + z * (394 + z * (360 + z * (254 + z * (213 + z * (129 + z * (72 + z * 13))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139
def f {R : Type*} [CommRing R] (z : R) : R := (105 + z * (122 + z * (125 + z * (132 + z * (109 + z * (42 + z * (48 + z * (77 + z * (78 + z * (119 + z * (136 + z * (31 + z * (34 + z * (130 + z * (58 + z * (89 + z * (116 + z * (0 + z * (102 + z * (128 + z * 1))))))))))))))))))))

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Powers01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139

def pow1_2_q {R : Type*} [CommRing R] (_ : R) : R := 0

def pow1_69_q {R : Type*} [CommRing R] (_ : R) : R := 87

def pow1_139_q {R : Type*} [CommRing R] (_ : R) : R := 106

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Powers05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139


def pow10_2 {R : Type*} [CommRing R] (z : R) : R := (40 + z * (48 + z * (8 + z * (85 + z * (90 + z * (125 + z * (76 + z * (106 + z * (17 + z * (53 + z * (32 + z * (67 + z * (43 + z * (21 + z * (105 + z * (50 + z * (30 + z * (123 + z * (58 + z * 94)))))))))))))))))))

def pow10_2_q {R : Type*} [CommRing R] (z : R) : R := (52 + z * (97 + z * (71 + z * (44 + z * (106 + z * (107 + z * (33 + z * (26 + z * (4 + z * (64 + z * (64 + z * (138 + z * (122 + z * (97 + z * (98 + z * (82 + z * (124 + z * (91 + z * 125))))))))))))))))))

def pow10_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (24 + z * ((-7) + z * ((-40) + z * ((-102) + z * ((-154) + z * ((-177) + z * ((-140) + z * ((-121) + z * ((-158) + z * ((-45) + z * ((-50) + z * ((-196) + z * ((-313) + z * ((-300) + z * ((-325) + z * ((-230) + z * ((-143) + z * ((-149) + z * ((-241) + z * ((-235) + z * ((-384) + z * ((-273) + z * ((-85) + z * ((-128) + z * ((-132) + z * ((-120) + z * ((-35) + z * ((-181) + z * ((-61) + z * ((-3) + z * ((-20) + z * ((-22) + z * (108 + z * (42 + z * (16 + z * ((-20) + z * ((-59) + z * ((-89) + z * 25))))))))))))))))))))))))))))))))))))))


def pow10_4 {R : Type*} [CommRing R] (z : R) : R := (31 + z * (63 + z * (80 + z * (133 + z * (52 + z * (112 + z * (65 + z * (14 + z * (34 + z * (105 + z * (57 + z * (91 + z * (59 + z * (113 + z * (72 + z * (60 + z * (57 + z * (133 + z * (30 + z * 31)))))))))))))))))))

def pow10_4_q {R : Type*} [CommRing R] (z : R) : R := (7 + z * (98 + z * (101 + z * (12 + z * (79 + z * (106 + z * (44 + z * (138 + z * (116 + z * (91 + z * (123 + z * (117 + z * (98 + z * (59 + z * (15 + z * (135 + z * (37 + z * (97 + z * 79))))))))))))))))))

def pow10_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (6 + z * ((-53) + z * ((-148) + z * ((-139) + z * ((-149) + z * ((-192) + z * ((-128) + z * ((-153) + z * ((-205) + z * ((-256) + z * ((-259) + z * ((-420) + z * ((-364) + z * ((-420) + z * ((-420) + z * ((-481) + z * ((-429) + z * ((-508) + z * ((-432) + z * ((-393) + z * ((-474) + z * ((-305) + z * ((-104) + z * ((-218) + z * ((-168) + z * ((-336) + z * ((-302) + z * ((-362) + z * ((-205) + z * ((-131) + z * ((-178) + z * ((-102) + z * (19 + z * ((-8) + z * ((-16) + z * (37 + z * (43 + z * (5 + z * 63))))))))))))))))))))))))))))))))))))))


def pow10_8 {R : Type*} [CommRing R] (z : R) : R := (114 + z * (0 + z * (36 + z * (32 + z * (59 + z * (40 + z * (11 + z * (131 + z * (64 + z * (59 + z * (82 + z * (119 + z * (94 + z * (113 + z * (27 + z * (55 + z * (122 + z * (86 + z * (46 + z * 7)))))))))))))))))))

def pow10_8_q {R : Type*} [CommRing R] (z : R) : R := (110 + z * (10 + z * (52 + z * (96 + z * (18 + z * (11 + z * (95 + z * (29 + z * (60 + z * (50 + z * (66 + z * (95 + z * (17 + z * (29 + z * (28 + z * (95 + z * (49 + z * (60 + z * 127))))))))))))))))))

def pow10_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-77) + z * ((-76) + z * ((-83) + z * ((-100) + z * ((-51) + z * (49 + z * (47 + z * (5 + z * (41 + z * ((-81) + z * ((-133) + z * ((-37) + z * ((-17) + z * ((-74) + z * (196 + z * (57 + z * (18 + z * (117 + z * ((-13) + z * ((-75) + z * (154 + z * ((-64) + z * (122 + z * (126 + z * ((-47) + z * ((-75) + z * (80 + z * ((-10) + z * (51 + z * (31 + z * (75 + z * ((-30) + z * (40 + z * ((-60) + z * ((-51) + z * ((-7) + z * ((-83) + z * ((-104) + z * 6))))))))))))))))))))))))))))))))))))))


def pow10_16 {R : Type*} [CommRing R] (z : R) : R := (49 + z * (130 + z * (56 + z * (76 + z * (42 + z * (87 + z * (43 + z * (120 + z * (10 + z * (136 + z * (9 + z * (14 + z * (64 + z * (61 + z * (55 + z * (7 + z * (34 + z * (26 + z * (11 + z * 69)))))))))))))))))))

def pow10_16_q {R : Type*} [CommRing R] (z : R) : R := (73 + z * (45 + z * (47 + z * (74 + z * (112 + z * (136 + z * (26 + z * (85 + z * (22 + z * (76 + z * (106 + z * (9 + z * (44 + z * (134 + z * (25 + z * (17 + z * (76 + z * (71 + z * 49))))))))))))))))))

def pow10_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (38 + z * ((-99) + z * ((-82) + z * ((-155) + z * ((-186) + z * ((-288) + z * ((-330) + z * ((-182) + z * ((-282) + z * ((-255) + z * ((-276) + z * ((-142) + z * ((-182) + z * ((-301) + z * ((-302) + z * ((-160) + z * ((-117) + z * ((-167) + z * ((-158) + z * ((-233) + z * ((-113) + z * ((-41) + z * ((-54) + z * ((-31) + z * (178 + z * (84 + z * ((-10) + z * (150 + z * (88 + z * (84 + z * (100 + z * ((-63) + z * ((-67) + z * (63 + z * (27 + z * ((-53) + z * ((-78) + z * ((-41) + z * 0))))))))))))))))))))))))))))))))))))))


def pow10_17 {R : Type*} [CommRing R] (z : R) : R := (26 + z * (5 + z * (89 + z * (87 + z * (129 + z * (60 + z * (111 + z * (0 + z * (0 + z * (45 + z * (9 + z * (10 + z * (1 + z * (95 + z * (45 + z * (104 + z * (43 + z * (65 + z * (85 + z * 60)))))))))))))))))))

def pow10_17_q {R : Type*} [CommRing R] (z : R) : R := (37 + z * (30 + z * (52 + z * (17 + z * (52 + z * (133 + z * (108 + z * (127 + z * (101 + z * (20 + z * (40 + z * (11 + z * (4 + z * (27 + z * (23 + z * (96 + z * (86 + z * (106 + z * 109))))))))))))))))))

def pow10_17_mul_t {R : Type*} [CommRing R] (z : R) : R := (5 + z * (62 + z * (41 + z * (42 + z * ((-3) + z * ((-28) + z * ((-100) + z * ((-127) + z * ((-253) + z * ((-187) + z * ((-121) + z * ((-110) + z * ((-74) + z * ((-18) + z * (13 + z * ((-159) + z * ((-44) + z * ((-176) + z * ((-176) + z * ((-167) + z * ((-222) + z * ((-209) + z * (2 + z * ((-154) + z * ((-156) + z * ((-211) + z * ((-143) + z * ((-163) + z * ((-14) + z * ((-1) + z * ((-77) + z * ((-128) + z * ((-65) + z * ((-122) + z * ((-132) + z * ((-67) + z * ((-101) + z * ((-81) + z * 29))))))))))))))))))))))))))))))))))))))


def pow10_34 {R : Type*} [CommRing R] (z : R) : R := (11 + z * (73 + z * (129 + z * (45 + z * (127 + z * (70 + z * (63 + z * (136 + z * (73 + z * (75 + z * (3 + z * (90 + z * (118 + z * (77 + z * (6 + z * (66 + z * (5 + z * (104 + z * (78 + z * 8)))))))))))))))))))

def pow10_34_q {R : Type*} [CommRing R] (z : R) : R := (99 + z * (84 + z * (54 + z * (79 + z * (7 + z * (117 + z * (114 + z * (7 + z * (108 + z * (105 + z * (14 + z * (70 + z * (124 + z * (123 + z * (88 + z * (118 + z * (52 + z * (38 + z * 125))))))))))))))))))

def pow10_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-70) + z * ((-149) + z * ((-171) + z * ((-238) + z * ((-170) + z * ((-170) + z * ((-107) + z * ((-134) + z * ((-115) + z * ((-305) + z * ((-338) + z * ((-384) + z * ((-469) + z * ((-590) + z * ((-665) + z * ((-673) + z * ((-734) + z * ((-377) + z * ((-585) + z * ((-427) + z * ((-326) + z * ((-400) + z * ((-389) + z * ((-281) + z * ((-484) + z * ((-508) + z * ((-383) + z * ((-500) + z * ((-364) + z * ((-212) + z * ((-188) + z * ((-246) + z * ((-51) + z * ((-74) + z * ((-79) + z * (40 + z * ((-19) + z * ((-42) + z * 25))))))))))))))))))))))))))))))))))))))


def pow10_68 {R : Type*} [CommRing R] (z : R) : R := (131 + z * (47 + z * (108 + z * (74 + z * (71 + z * (68 + z * (85 + z * (7 + z * (16 + z * (69 + z * (31 + z * (108 + z * (124 + z * (125 + z * (5 + z * (114 + z * (69 + z * (48 + z * (85 + z * 69)))))))))))))))))))

def pow10_68_q {R : Type*} [CommRing R] (z : R) : R := (33 + z * (93 + z * (79 + z * (5 + z * (37 + z * (22 + z * (121 + z * (92 + z * (7 + z * (8 + z * (131 + z * (75 + z * (136 + z * (6 + z * (29 + z * (92 + z * (35 + z * (6 + z * 64))))))))))))))))))

def pow10_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-25) + z * ((-88) + z * ((-113) + z * ((-46) + z * ((-31) + z * (16 + z * (83 + z * ((-9) + z * (89 + z * (145 + z * ((-20) + z * (24 + z * ((-47) + z * (95 + z * (16 + z * ((-41) + z * ((-33) + z * ((-14) + z * (36 + z * (116 + z * ((-56) + z * ((-22) + z * (18 + z * (0 + z * (127 + z * ((-179) + z * ((-65) + z * ((-61) + z * ((-163) + z * (3 + z * (1 + z * ((-178) + z * (27 + z * ((-58) + z * ((-73) + z * (80 + z * (3 + z * ((-50) + z * 0))))))))))))))))))))))))))))))))))))))


def pow10_69 {R : Type*} [CommRing R] (z : R) : R := (134 + z * (113 + z * (46 + z * (63 + z * (6 + z * (108 + z * (23 + z * (26 + z * (56 + z * (14 + z * (108 + z * (1 + z * (46 + z * (77 + z * (37 + z * (8 + z * (5 + z * (95 + z * (22 + z * 18)))))))))))))))))))

def pow10_69_q {R : Type*} [CommRing R] (z : R) : R := (116 + z * (117 + z * (79 + z * (31 + z * (115 + z * (103 + z * (3 + z * (105 + z * (59 + z * (16 + z * (120 + z * (0 + z * (33 + z * (110 + z * (17 + z * (105 + z * (137 + z * (98 + z * 109))))))))))))))))))

def pow10_69_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * ((-81) + z * ((-99) + z * ((-138) + z * ((-169) + z * ((-175) + z * ((-91) + z * ((-169) + z * ((-281) + z * ((-153) + z * ((-279) + z * ((-215) + z * ((-73) + z * ((-95) + z * ((-221) + z * ((-36) + z * ((-143) + z * ((-208) + z * ((-188) + z * ((-172) + z * ((-313) + z * ((-22) + z * (3 + z * ((-301) + z * ((-30) + z * ((-27) + z * ((-163) + z * (94 + z * (128 + z * (11 + z * (131 + z * ((-59) + z * (33 + z * (8 + z * ((-39) + z * ((-20) + z * ((-68) + z * ((-49) + z * 29))))))))))))))))))))))))))))))))))))))


def pow10_138 {R : Type*} [CommRing R] (z : R) : R := (30 + z * (135 + z * (100 + z * (59 + z * (73 + z * (112 + z * (123 + z * (8 + z * (8 + z * (124 + z * (92 + z * (66 + z * (9 + z * (118 + z * (127 + z * (34 + z * (79 + z * (121 + z * (23 + z * 124)))))))))))))))))))

def pow10_138_q {R : Type*} [CommRing R] (z : R) : R := (86 + z * (31 + z * (7 + z * (73 + z * (84 + z * (104 + z * (25 + z * (129 + z * (60 + z * (61 + z * (5 + z * (40 + z * (89 + z * (15 + z * (112 + z * (60 + z * (7 + z * (47 + z * 46))))))))))))))))))

def pow10_138_mul_t {R : Type*} [CommRing R] (z : R) : R := (64 + z * (118 + z * (70 + z * (25 + z * ((-102) + z * ((-16) + z * ((-48) + z * ((-246) + z * ((-172) + z * ((-301) + z * ((-92) + z * ((-159) + z * ((-238) + z * ((-128) + z * ((-317) + z * ((-274) + z * ((-480) + z * ((-280) + z * ((-247) + z * ((-379) + z * ((-271) + z * ((-441) + z * ((-286) + z * ((-335) + z * ((-325) + z * ((-262) + z * ((-239) + z * ((-191) + z * ((-243) + z * ((-71) + z * ((-169) + z * ((-123) + z * ((-109) + z * ((-197) + z * ((-31) + z * ((-10) + z * ((-49) + z * ((-37) + z * 2))))))))))))))))))))))))))))))))))))))


def pow10_139 {R : Type*} [CommRing R] (z : R) : R := (3 + z * (74 + z * (108 + z * (44 + z * (32 + z * (73 + z * (63 + z * (2 + z * (54 + z * (96 + z * (10 + z * (53 + z * (60 + z * (122 + z * (54 + z * (17 + z * (69 + z * (106 + z * (95 + z * 40)))))))))))))))))))

def pow10_139_q {R : Type*} [CommRing R] (z : R) : R := (3 + z * (8 + z * (12 + z * (49 + z * (105 + z * (112 + z * (29 + z * (80 + z * (81 + z * (94 + z * (114 + z * (117 + z * (123 + z * (110 + z * (115 + z * (112 + z * (130 + z * (50 + z * 73))))))))))))))))))

def pow10_139_mul_t {R : Type*} [CommRing R] (z : R) : R := (18 + z * (100 + z * (144 + z * (118 + z * (39 + z * (9 + z * (46 + z * ((-42) + z * ((-110) + z * ((-80) + z * ((-3) + z * ((-91) + z * ((-302) + z * ((-312) + z * ((-235) + z * ((-168) + z * ((-219) + z * ((-256) + z * ((-141) + z * ((-63) + z * ((-162) + z * ((-166) + z * ((-169) + z * ((-197) + z * ((-245) + z * ((-237) + z * ((-101) + z * ((-176) + z * ((-98) + z * ((-71) + z * ((-46) + z * ((-81) + z * (52 + z * (54 + z * (23 + z * (33 + z * (71 + z * ((-30) + z * 53))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Powers06
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139
def pow11_2 {R : Type*} [CommRing R] (z : R) : R := (17 + z * (48 + z * (100 + z * (115 + z * (22 + z * (109 + z * (61 + z * (73 + z * (11 + z * (108 + z * (59 + z * (37 + z * (29 + z * (33 + z * (5 + z * (124 + z * (68 + z * (11 + z * (45 + z * 9)))))))))))))))))))

def pow11_2_q {R : Type*} [CommRing R] (z : R) : R := (82 + z * (70 + z * (122 + z * (77 + z * (123 + z * (16 + z * (46 + z * (33 + z * (83 + z * (119 + z * (124 + z * (63 + z * (102 + z * (137 + z * (123 + z * (54 + z * (11 + z * (41 + z * 71))))))))))))))))))

def pow11_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-62) + z * ((-122) + z * ((-184) + z * ((-190) + z * ((-269) + z * ((-280) + z * ((-234) + z * ((-163) + z * ((-239) + z * ((-352) + z * ((-384) + z * ((-427) + z * ((-556) + z * ((-573) + z * ((-438) + z * ((-450) + z * ((-596) + z * ((-522) + z * ((-390) + z * ((-354) + z * ((-363) + z * ((-330) + z * ((-317) + z * ((-354) + z * ((-246) + z * ((-187) + z * ((-136) + z * ((-231) + z * ((-297) + z * ((-109) + z * (23 + z * ((-30) + z * ((-78) + z * ((-74) + z * (67 + z * (144 + z * (36 + z * ((-11) + z * 11))))))))))))))))))))))))))))))))))))))


def pow11_4 {R : Type*} [CommRing R] (z : R) : R := (86 + z * (49 + z * (7 + z * (43 + z * (46 + z * (23 + z * (2 + z * (27 + z * (103 + z * (12 + z * (137 + z * (0 + z * (78 + z * (97 + z * (86 + z * (65 + z * (75 + z * (76 + z * (26 + z * 102)))))))))))))))))))

def pow11_4_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (122 + z * (62 + z * (87 + z * (21 + z * (122 + z * (84 + z * (131 + z * (41 + z * (63 + z * (101 + z * (65 + z * (87 + z * (99 + z * (47 + z * (74 + z * (23 + z * (33 + z * 81))))))))))))))))))

def pow11_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-28) + z * ((-115) + z * ((-148) + z * ((-170) + z * ((-138) + z * ((-148) + z * ((-154) + z * ((-200) + z * ((-167) + z * ((-275) + z * ((-299) + z * ((-303) + z * ((-185) + z * ((-417) + z * ((-422) + z * ((-480) + z * ((-447) + z * ((-380) + z * ((-241) + z * ((-479) + z * ((-423) + z * ((-370) + z * ((-361) + z * ((-403) + z * ((-267) + z * ((-306) + z * ((-363) + z * ((-234) + z * ((-304) + z * ((-255) + z * ((-127) + z * ((-172) + z * ((-140) + z * ((-86) + z * ((-92) + z * ((-30) + z * ((-74) + z * ((-69) + z * 0))))))))))))))))))))))))))))))))))))))


def pow11_8 {R : Type*} [CommRing R] (z : R) : R := (110 + z * (83 + z * (16 + z * (95 + z * (39 + z * (67 + z * (26 + z * (36 + z * (92 + z * (93 + z * (53 + z * (45 + z * (39 + z * (4 + z * (78 + z * (31 + z * (131 + z * (18 + z * (109 + z * 7)))))))))))))))))))

def pow11_8_q {R : Type*} [CommRing R] (z : R) : R := (31 + z * (107 + z * (98 + z * (99 + z * (68 + z * (128 + z * (8 + z * (3 + z * (19 + z * (98 + z * (30 + z * (6 + z * (59 + z * (29 + z * (42 + z * (122 + z * (38 + z * (69 + z * 118))))))))))))))))))

def pow11_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (29 + z * ((-48) + z * ((-170) + z * ((-229) + z * ((-265) + z * ((-367) + z * ((-357) + z * ((-285) + z * ((-164) + z * ((-291) + z * ((-219) + z * ((-295) + z * ((-315) + z * ((-197) + z * ((-232) + z * ((-314) + z * ((-265) + z * ((-291) + z * ((-375) + z * ((-450) + z * ((-195) + z * ((-347) + z * ((-128) + z * ((-59) + z * ((-88) + z * ((-66) + z * (106 + z * (108 + z * ((-155) + z * (258 + z * ((-13) + z * ((-26) + z * (103 + z * ((-29) + z * ((-74) + z * (52 + z * ((-34) + z * ((-71) + z * 74))))))))))))))))))))))))))))))))))))))


def pow11_16 {R : Type*} [CommRing R] (z : R) : R := (126 + z * (26 + z * (46 + z * (20 + z * (85 + z * (119 + z * (69 + z * (9 + z * (133 + z * (1 + z * (20 + z * (51 + z * (133 + z * (3 + z * (45 + z * (77 + z * (71 + z * (57 + z * (106 + z * 31)))))))))))))))))))

def pow11_16_q {R : Type*} [CommRing R] (z : R) : R := (73 + z * (20 + z * (19 + z * (109 + z * (31 + z * (22 + z * (42 + z * (102 + z * (69 + z * (103 + z * (25 + z * (95 + z * (114 + z * (95 + z * (47 + z * (46 + z * (104 + z * (119 + z * 49))))))))))))))))))

def pow11_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (31 + z * (52 + z * ((-23) + z * ((-17) + z * ((-36) + z * ((-24) + z * ((-34) + z * ((-145) + z * ((-20) + z * ((-80) + z * ((-166) + z * ((-156) + z * ((-208) + z * ((-374) + z * ((-232) + z * ((-292) + z * ((-337) + z * ((-252) + z * ((-328) + z * ((-283) + z * ((-392) + z * ((-307) + z * ((-425) + z * ((-205) + z * ((-205) + z * ((-289) + z * ((-280) + z * ((-293) + z * ((-209) + z * ((-231) + z * ((-186) + z * ((-287) + z * ((-52) + z * ((-118) + z * (51 + z * ((-142) + z * ((-59) + z * ((-35) + z * 0))))))))))))))))))))))))))))))))))))))


def pow11_17 {R : Type*} [CommRing R] (z : R) : R := (106 + z * (125 + z * (134 + z * (27 + z * (131 + z * (86 + z * (64 + z * (102 + z * (20 + z * (33 + z * (124 + z * (62 + z * (51 + z * (62 + z * (19 + z * (100 + z * (102 + z * (67 + z * (107 + z * 118)))))))))))))))))))

def pow11_17_q {R : Type*} [CommRing R] (z : R) : R := (131 + z * (95 + z * (108 + z * (81 + z * (113 + z * (9 + z * (53 + z * (88 + z * (61 + z * (17 + z * (87 + z * (87 + z * (126 + z * (31 + z * (47 + z * (51 + z * (81 + z * (114 + z * 128))))))))))))))))))

def pow11_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-97) + z * ((-120) + z * ((-171) + z * ((-281) + z * ((-362) + z * ((-246) + z * ((-167) + z * ((-232) + z * ((-257) + z * ((-212) + z * ((-349) + z * ((-389) + z * ((-427) + z * ((-300) + z * ((-336) + z * ((-474) + z * ((-434) + z * ((-264) + z * ((-401) + z * ((-513) + z * ((-471) + z * ((-280) + z * ((-311) + z * ((-163) + z * ((-93) + z * ((-232) + z * ((-308) + z * ((-245) + z * ((-157) + z * ((-45) + z * ((-142) + z * ((-151) + z * ((-57) + z * ((-85) + z * ((-43) + z * ((-3) + z * ((-87) + z * ((-67) + z * 8))))))))))))))))))))))))))))))))))))))


def pow11_34 {R : Type*} [CommRing R] (z : R) : R := (51 + z * (129 + z * (86 + z * (78 + z * (50 + z * (95 + z * (32 + z * (1 + z * (73 + z * (36 + z * (5 + z * (138 + z * (89 + z * (48 + z * (7 + z * (72 + z * (134 + z * (113 + z * (0 + z * 1)))))))))))))))))))

def pow11_34_q {R : Type*} [CommRing R] (z : R) : R := (133 + z * (90 + z * (59 + z * (112 + z * (57 + z * (67 + z * (12 + z * (102 + z * (19 + z * (117 + z * (122 + z * (83 + z * (16 + z * (110 + z * (74 + z * (104 + z * (106 + z * (79 + z * 24))))))))))))))))))

def pow11_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * (5 + z * (73 + z * ((-62) + z * ((-7) + z * (50 + z * (165 + z * (75 + z * (92 + z * ((-44) + z * ((-160) + z * ((-3) + z * (3 + z * ((-248) + z * ((-108) + z * ((-106) + z * ((-190) + z * ((-4) + z * ((-129) + z * ((-34) + z * (178 + z * (127 + z * (50 + z * (51 + z * ((-64) + z * ((-31) + z * ((-50) + z * ((-60) + z * ((-3) + z * ((-7) + z * (2 + z * (41 + z * (1 + z * (58 + z * (165 + z * (120 + z * (105 + z * (159 + z * 100))))))))))))))))))))))))))))))))))))))


def pow11_68 {R : Type*} [CommRing R] (z : R) : R := (11 + z * (23 + z * (22 + z * (3 + z * (120 + z * (42 + z * (45 + z * (12 + z * (57 + z * (75 + z * (44 + z * (24 + z * (39 + z * (126 + z * (126 + z * (94 + z * (4 + z * (136 + z * (93 + z * 38)))))))))))))))))))

def pow11_68_q {R : Type*} [CommRing R] (z : R) : R := (71 + z * (126 + z * (89 + z * (45 + z * (37 + z * (49 + z * (136 + z * (69 + z * (62 + z * (105 + z * (83 + z * (135 + z * (95 + z * (123 + z * (135 + z * (34 + z * (106 + z * (11 + z * 1))))))))))))))))))

def pow11_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-35) + z * ((-63) + z * ((-59) + z * ((-76) + z * ((-89) + z * ((-56) + z * ((-49) + z * ((-162) + z * ((-240) + z * ((-304) + z * ((-413) + z * ((-420) + z * ((-271) + z * ((-295) + z * ((-469) + z * ((-602) + z * ((-428) + z * ((-230) + z * ((-267) + z * ((-398) + z * ((-381) + z * ((-380) + z * ((-341) + z * ((-347) + z * ((-369) + z * ((-384) + z * ((-338) + z * ((-157) + z * (13 + z * ((-237) + z * ((-253) + z * ((-129) + z * ((-62) + z * (58 + z * ((-18) + z * ((-104) + z * ((-10) + z * ((-1) + z * 0))))))))))))))))))))))))))))))))))))))


def pow11_69 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (9 + z * (97 + z * (88 + z * (130 + z * (132 + z * (14 + z * (103 + z * (78 + z * (61 + z * (15 + z * (92 + z * (25 + z * (48 + z * (110 + z * (115 + z * (63 + z * (1 + z * (62 + z * 73)))))))))))))))))))

def pow11_69_q {R : Type*} [CommRing R] (z : R) : R := (130 + z * (81 + z * (59 + z * (31 + z * (98 + z * (137 + z * (65 + z * (43 + z * (72 + z * (134 + z * (38 + z * (116 + z * (80 + z * (76 + z * (25 + z * (53 + z * (72 + z * (3 + z * 130))))))))))))))))))

def pow11_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-98) + z * ((-169) + z * ((-212) + z * ((-239) + z * ((-303) + z * ((-292) + z * ((-263) + z * ((-331) + z * ((-406) + z * ((-456) + z * ((-424) + z * ((-472) + z * ((-505) + z * ((-555) + z * ((-515) + z * ((-453) + z * ((-439) + z * ((-306) + z * ((-479) + z * ((-464) + z * ((-378) + z * ((-320) + z * ((-186) + z * ((-161) + z * ((-306) + z * ((-229) + z * (4 + z * ((-103) + z * ((-150) + z * ((-46) + z * (94 + z * (48 + z * (77 + z * (49 + z * ((-26) + z * (115 + z * (33 + z * ((-67) + z * 10))))))))))))))))))))))))))))))))))))))


def pow11_138 {R : Type*} [CommRing R] (z : R) : R := (105 + z * (127 + z * (0 + z * (23 + z * (23 + z * (105 + z * (20 + z * (66 + z * (3 + z * (74 + z * (65 + z * (69 + z * (16 + z * (68 + z * (44 + z * (65 + z * (120 + z * (29 + z * (35 + z * 129)))))))))))))))))))

def pow11_138_q {R : Type*} [CommRing R] (z : R) : R := (125 + z * (4 + z * (26 + z * (112 + z * (50 + z * (36 + z * (125 + z * (38 + z * (111 + z * (68 + z * (40 + z * (37 + z * (130 + z * (42 + z * (13 + z * (60 + z * (66 + z * (117 + z * 47))))))))))))))))))

def pow11_138_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-95) + z * ((-113) + z * ((-128) + z * ((-211) + z * ((-173) + z * ((-89) + z * ((-87) + z * ((-27) + z * ((-91) + z * ((-85) + z * ((-155) + z * ((-43) + z * ((-119) + z * ((-246) + z * ((-146) + z * ((-203) + z * ((-187) + z * ((-86) + z * ((-91) + z * ((-197) + z * (24 + z * ((-133) + z * ((-70) + z * (160 + z * ((-120) + z * ((-232) + z * ((-75) + z * ((-143) + z * ((-110) + z * (90 + z * ((-13) + z * ((-161) + z * ((-20) + z * (35 + z * (34 + z * ((-80) + z * ((-114) + z * (21 + z * 38))))))))))))))))))))))))))))))))))))))


def pow11_139 {R : Type*} [CommRing R] (z : R) : R := (95 + z * (69 + z * (130 + z * (13 + z * (126 + z * (81 + z * (93 + z * (54 + z * (134 + z * (105 + z * (113 + z * (46 + z * (118 + z * (14 + z * (133 + z * (102 + z * (114 + z * (62 + z * (81 + z * 92)))))))))))))))))))

def pow11_139_q {R : Type*} [CommRing R] (z : R) : R := (108 + z * (19 + z * (39 + z * (35 + z * (34 + z * (101 + z * (4 + z * (124 + z * (107 + z * (106 + z * (113 + z * (131 + z * (62 + z * (54 + z * (108 + z * (135 + z * (80 + z * (81 + z * 17))))))))))))))))))

def pow11_139_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-80) + z * ((-51) + z * (5 + z * ((-48) + z * ((-118) + z * ((-106) + z * ((-34) + z * ((-161) + z * ((-268) + z * ((-287) + z * ((-372) + z * ((-417) + z * ((-386) + z * ((-377) + z * ((-368) + z * ((-545) + z * ((-517) + z * ((-464) + z * ((-443) + z * ((-447) + z * ((-408) + z * ((-347) + z * ((-223) + z * ((-400) + z * ((-365) + z * ((-319) + z * ((-389) + z * ((-242) + z * ((-130) + z * ((-187) + z * ((-208) + z * ((-82) + z * (34 + z * ((-60) + z * ((-42) + z * (11 + z * (43 + z * (82 + z * 37))))))))))))))))))))))))))))))))))))))


def pow12_2 {R : Type*} [CommRing R] (z : R) : R := (73 + z * (114 + z * (65 + z * (30 + z * (73 + z * (91 + z * (4 + z * (73 + z * (10 + z * (31 + z * (32 + z * (88 + z * (98 + z * (14 + z * (48 + z * (87 + z * (100 + z * (80 + z * (15 + z * 41)))))))))))))))))))

def pow12_2_q {R : Type*} [CommRing R] (z : R) : R := (121 + z * (101 + z * (4 + z * (23 + z * (67 + z * (125 + z * (77 + z * (33 + z * (27 + z * (121 + z * (61 + z * (71 + z * (135 + z * (98 + z * (51 + z * (130 + z * (94 + z * (5 + z * 124))))))))))))))))))

def pow12_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-27) + z * ((-89) + z * (11 + z * ((-80) + z * (41 + z * ((-34) + z * (119 + z * ((-49) + z * (118 + z * (35 + z * (186 + z * (89 + z * (231 + z * ((-98) + z * (160 + z * ((-62) + z * (246 + z * (170 + z * (249 + z * (28 + z * (331 + z * (232 + z * (194 + z * (274 + z * (285 + z * (49 + z * (299 + z * (164 + z * (33 + z * (132 + z * (139 + z * ((-25) + z * (96 + z * (170 + z * (3 + z * (132 + z * (33 + z * ((-7) + z * 60))))))))))))))))))))))))))))))))))))))


def pow12_4 {R : Type*} [CommRing R] (z : R) : R := (58 + z * (66 + z * (131 + z * (66 + z * (43 + z * (80 + z * (8 + z * (46 + z * (137 + z * (91 + z * (93 + z * (9 + z * (8 + z * (22 + z * (133 + z * (40 + z * (22 + z * (29 + z * (81 + z * 45)))))))))))))))))))

def pow12_4_q {R : Type*} [CommRing R] (z : R) : R := (78 + z * (103 + z * (52 + z * (105 + z * (106 + z * (116 + z * (88 + z * (43 + z * (37 + z * (55 + z * (55 + z * (2 + z * (15 + z * (111 + z * (112 + z * (131 + z * (129 + z * (122 + z * 13))))))))))))))))))

def pow12_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-21) + z * ((-27) + z * ((-39) + z * ((-154) + z * ((-222) + z * ((-186) + z * ((-234) + z * ((-292) + z * ((-278) + z * ((-295) + z * ((-368) + z * ((-255) + z * ((-97) + z * ((-316) + z * ((-396) + z * ((-401) + z * ((-375) + z * ((-431) + z * ((-495) + z * ((-511) + z * ((-414) + z * ((-287) + z * ((-344) + z * ((-380) + z * ((-357) + z * ((-381) + z * ((-213) + z * ((-120) + z * ((-114) + z * ((-194) + z * ((-149) + z * ((-109) + z * ((-185) + z * ((-148) + z * ((-108) + z * ((-133) + z * ((-74) + z * ((-4) + z * 12))))))))))))))))))))))))))))))))))))))


def pow12_8 {R : Type*} [CommRing R] (z : R) : R := (90 + z * (63 + z * (85 + z * (3 + z * (60 + z * (82 + z * (36 + z * (35 + z * (121 + z * (90 + z * (89 + z * (67 + z * (104 + z * (7 + z * (35 + z * (67 + z * (90 + z * (10 + z * (116 + z * 12)))))))))))))))))))

def pow12_8_q {R : Type*} [CommRing R] (z : R) : R := (10 + z * (111 + z * (71 + z * (107 + z * (14 + z * (76 + z * (130 + z * (72 + z * (101 + z * (72 + z * (89 + z * (39 + z * (26 + z * (10 + z * (20 + z * (53 + z * (95 + z * (97 + z * 79))))))))))))))))))

def pow12_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (16 + z * ((-38) + z * ((-20) + z * ((-73) + z * ((-60) + z * ((-92) + z * ((-177) + z * ((-162) + z * ((-202) + z * ((-193) + z * ((-107) + z * ((-195) + z * ((-172) + z * ((-195) + z * ((-203) + z * ((-182) + z * ((-175) + z * ((-231) + z * ((-269) + z * ((-348) + z * ((-376) + z * ((-365) + z * ((-145) + z * ((-67) + z * ((-220) + z * ((-351) + z * ((-217) + z * ((-132) + z * ((-27) + z * ((-127) + z * ((-178) + z * ((-152) + z * ((-9) + z * ((-47) + z * ((-127) + z * ((-111) + z * ((-82) + z * ((-21) + z * 14))))))))))))))))))))))))))))))))))))))


def pow12_16 {R : Type*} [CommRing R] (z : R) : R := (33 + z * (20 + z * (20 + z * (114 + z * (103 + z * (19 + z * (88 + z * (41 + z * (34 + z * (18 + z * (14 + z * (11 + z * (96 + z * (67 + z * (5 + z * (120 + z * (105 + z * (55 + z * (88 + z * 87)))))))))))))))))))

def pow12_16_q {R : Type*} [CommRing R] (z : R) : R := (53 + z * (78 + z * (113 + z * (39 + z * (32 + z * (39 + z * (44 + z * (35 + z * (133 + z * (9 + z * (131 + z * (97 + z * (20 + z * (102 + z * (102 + z * (110 + z * (74 + z * (59 + z * 5))))))))))))))))))

def pow12_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (18 + z * ((-24) + z * ((-63) + z * ((-169) + z * ((-144) + z * ((-113) + z * ((-70) + z * ((-71) + z * ((-95) + z * ((-61) + z * ((-95) + z * ((-246) + z * ((-108) + z * ((-144) + z * ((-232) + z * ((-359) + z * ((-193) + z * ((-311) + z * ((-225) + z * ((-198) + z * ((-102) + z * ((-282) + z * ((-81) + z * ((-170) + z * ((-176) + z * ((-143) + z * ((-127) + z * ((-92) + z * ((-45) + z * ((-288) + z * ((-84) + z * ((-141) + z * ((-143) + z * ((-97) + z * (2 + z * ((-80) + z * (40 + z * (15 + z * 1))))))))))))))))))))))))))))))))))))))


def pow12_17 {R : Type*} [CommRing R] (z : R) : R := (39 + z * (103 + z * (103 + z * (88 + z * (109 + z * (39 + z * (7 + z * (105 + z * (7 + z * (36 + z * (46 + z * (80 + z * (65 + z * (66 + z * (11 + z * (6 + z * (114 + z * (86 + z * (54 + z * 86)))))))))))))))))))

def pow12_17_q {R : Type*} [CommRing R] (z : R) : R := (97 + z * (32 + z * (121 + z * (29 + z * (41 + z * (11 + z * (3 + z * (0 + z * (117 + z * (27 + z * (102 + z * (24 + z * (48 + z * (110 + z * (46 + z * (56 + z * (129 + z * (49 + z * 81))))))))))))))))))

def pow12_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-51) + z * ((-80) + z * ((-153) + z * ((-140) + z * ((-95) + z * ((-30) + z * (14 + z * (64 + z * (84 + z * ((-44) + z * ((-113) + z * ((-116) + z * ((-28) + z * ((-79) + z * ((-23) + z * ((-72) + z * ((-95) + z * ((-65) + z * ((-106) + z * ((-6) + z * (77 + z * (89 + z * (181 + z * (83 + z * (119 + z * (103 + z * ((-84) + z * (88 + z * (10 + z * ((-18) + z * (143 + z * (65 + z * (12 + z * (136 + z * (87 + z * (57 + z * (21 + z * (34 + z * 57))))))))))))))))))))))))))))))))))))))


def pow12_34 {R : Type*} [CommRing R] (z : R) : R := (47 + z * (34 + z * (9 + z * (22 + z * (47 + z * (28 + z * (44 + z * (107 + z * (4 + z * (63 + z * (91 + z * (80 + z * (133 + z * (62 + z * (35 + z * (15 + z * (40 + z * (4 + z * (68 + z * 21)))))))))))))))))))

def pow12_34_q {R : Type*} [CommRing R] (z : R) : R := (112 + z * (93 + z * (132 + z * (4 + z * (85 + z * (105 + z * (135 + z * (51 + z * (102 + z * (14 + z * (70 + z * (12 + z * (87 + z * (15 + z * (116 + z * (47 + z * (53 + z * (16 + z * 29))))))))))))))))))

def pow12_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-74) + z * ((-111) + z * ((-148) + z * ((-107) + z * ((-95) + z * ((-76) + z * ((-166) + z * ((-205) + z * ((-266) + z * ((-349) + z * ((-394) + z * ((-232) + z * ((-243) + z * ((-211) + z * ((-255) + z * ((-461) + z * ((-414) + z * ((-275) + z * ((-255) + z * ((-178) + z * ((-64) + z * ((-161) + z * ((-136) + z * ((-70) + z * ((-246) + z * ((-215) + z * ((-56) + z * ((-108) + z * (8 + z * (69 + z * (3 + z * ((-43) + z * (25 + z * ((-14) + z * (42 + z * (147 + z * (91 + z * (40 + z * 53))))))))))))))))))))))))))))))))))))))


def pow12_68 {R : Type*} [CommRing R] (z : R) : R := (69 + z * (122 + z * (136 + z * (71 + z * (8 + z * (120 + z * (122 + z * (79 + z * (57 + z * (22 + z * (33 + z * (115 + z * (42 + z * (125 + z * (90 + z * (74 + z * (21 + z * (38 + z * (55 + z * 15)))))))))))))))))))

def pow12_68_q {R : Type*} [CommRing R] (z : R) : R := (27 + z * (31 + z * (127 + z * (99 + z * (113 + z * (71 + z * (123 + z * (53 + z * (62 + z * (68 + z * (73 + z * (42 + z * (5 + z * (71 + z * (128 + z * (135 + z * (107 + z * (62 + z * 24))))))))))))))))))

def pow12_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-5) + z * ((-25) + z * ((-134) + z * ((-221) + z * ((-294) + z * ((-351) + z * ((-417) + z * ((-349) + z * ((-381) + z * ((-414) + z * ((-395) + z * ((-385) + z * ((-383) + z * ((-361) + z * ((-398) + z * ((-585) + z * ((-558) + z * ((-613) + z * ((-601) + z * ((-461) + z * ((-481) + z * ((-412) + z * ((-334) + z * ((-319) + z * ((-364) + z * ((-263) + z * ((-280) + z * ((-259) + z * ((-198) + z * ((-260) + z * ((-165) + z * ((-175) + z * ((-233) + z * ((-257) + z * ((-180) + z * ((-129) + z * ((-41) + z * ((-2) + z * 3))))))))))))))))))))))))))))))))))))))


def pow12_69 {R : Type*} [CommRing R] (z : R) : R := (41 + z * (9 + z * (20 + z * (51 + z * (25 + z * (81 + z * (54 + z * (86 + z * (137 + z * (107 + z * (84 + z * (19 + z * (85 + z * (45 + z * (124 + z * (17 + z * (56 + z * (58 + z * (56 + z * 7)))))))))))))))))))

def pow12_69_q {R : Type*} [CommRing R] (z : R) : R := (21 + z * (118 + z * (129 + z * (82 + z * (126 + z * (67 + z * (32 + z * (56 + z * (85 + z * (80 + z * (105 + z * (114 + z * (118 + z * (42 + z * (112 + z * (15 + z * (15 + z * (49 + z * 129))))))))))))))))))

def pow12_69_mul_t {R : Type*} [CommRing R] (z : R) : R := (31 + z * (10 + z * ((-2) + z * ((-65) + z * ((-170) + z * ((-141) + z * ((-21) + z * (73 + z * (5 + z * (21 + z * ((-21) + z * ((-114) + z * ((-175) + z * ((-61) + z * ((-154) + z * (75 + z * (57 + z * (46 + z * ((-82) + z * (28 + z * ((-109) + z * ((-41) + z * ((-19) + z * (30 + z * ((-21) + z * (64 + z * ((-58) + z * ((-120) + z * ((-87) + z * (63 + z * ((-19) + z * ((-32) + z * (48 + z * ((-40) + z * (1 + z * (23 + z * ((-76) + z * ((-74) + z * 9))))))))))))))))))))))))))))))))))))))


def pow12_138 {R : Type*} [CommRing R] (z : R) : R := (91 + z * (134 + z * (13 + z * (115 + z * (89 + z * (118 + z * (108 + z * (87 + z * (92 + z * (25 + z * (33 + z * (81 + z * (39 + z * (64 + z * (136 + z * (20 + z * (41 + z * (3 + z * (50 + z * 18)))))))))))))))))))

def pow12_138_q {R : Type*} [CommRing R] (z : R) : R := (35 + z * (116 + z * (0 + z * (101 + z * (109 + z * (58 + z * (92 + z * (128 + z * (87 + z * (94 + z * (134 + z * (23 + z * (34 + z * (129 + z * (113 + z * (17 + z * (20 + z * (72 + z * 49))))))))))))))))))

def pow12_138_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * ((-114) + z * ((-121) + z * ((-182) + z * ((-285) + z * ((-267) + z * ((-294) + z * ((-373) + z * ((-345) + z * ((-384) + z * ((-468) + z * ((-442) + z * ((-283) + z * ((-387) + z * ((-408) + z * ((-268) + z * ((-383) + z * ((-334) + z * ((-265) + z * ((-363) + z * ((-350) + z * ((-133) + z * ((-201) + z * ((-283) + z * ((-88) + z * ((-158) + z * ((-137) + z * ((-185) + z * ((-144) + z * ((-214) + z * ((-30) + z * ((-67) + z * ((-144) + z * ((-136) + z * ((-1) + z * ((-19) + z * ((-74) + z * ((-40) + z * 0))))))))))))))))))))))))))))))))))))))


def pow12_139 {R : Type*} [CommRing R] (z : R) : R := (28 + z * (52 + z * (119 + z * (45 + z * (122 + z * (2 + z * (134 + z * (26 + z * (82 + z * (45 + z * (43 + z * (55 + z * (119 + z * (30 + z * (71 + z * (36 + z * (7 + z * (90 + z * (135 + z * 30)))))))))))))))))))

def pow12_139_q {R : Type*} [CommRing R] (z : R) : R := (45 + z * (25 + z * (138 + z * (134 + z * (88 + z * (16 + z * (80 + z * (25 + z * (113 + z * (18 + z * (44 + z * (72 + z * (4 + z * (85 + z * (43 + z * (70 + z * (128 + z * (88 + z * 127))))))))))))))))))

def pow12_139_mul_t {R : Type*} [CommRing R] (z : R) : R := (28 + z * (78 + z * ((-7) + z * ((-69) + z * ((-143) + z * (34 + z * ((-36) + z * (101 + z * (123 + z * (167 + z * (98 + z * (76 + z * (85 + z * (150 + z * (201 + z * (246 + z * (87 + z * ((-20) + z * ((-73) + z * (6 + z * (67 + z * ((-131) + z * (101 + z * (108 + z * (26 + z * ((-27) + z * ((-103) + z * ((-148) + z * (7 + z * ((-95) + z * (2 + z * ((-169) + z * ((-110) + z * ((-70) + z * ((-172) + z * ((-117) + z * ((-136) + z * ((-74) + z * 11))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Powers07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139
def pow13_2 {R : Type*} [CommRing R] (z : R) : R := (124 + z * (63 + z * (29 + z * (18 + z * (98 + z * (30 + z * (65 + z * (74 + z * (51 + z * (19 + z * (59 + z * (134 + z * (23 + z * (100 + z * (85 + z * (115 + z * (108 + z * (88 + z * (16 + z * 103)))))))))))))))))))

def pow13_2_q {R : Type*} [CommRing R] (z : R) : R := (46 + z * (69 + z * (48 + z * (32 + z * (73 + z * (43 + z * (60 + z * (57 + z * (63 + z * (16 + z * (44 + z * (44 + z * (102 + z * (135 + z * (68 + z * (18 + z * (138 + z * (69 + z * 66))))))))))))))))))

def pow13_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-30) + z * ((-72) + z * ((-71) + z * ((-65) + z * ((-44) + z * ((-70) + z * (25 + z * ((-100) + z * (50 + z * ((-133) + z * (51 + z * ((-168) + z * (42 + z * ((-192) + z * ((-111) + z * ((-222) + z * ((-201) + z * ((-363) + z * ((-100) + z * ((-204) + z * ((-97) + z * ((-108) + z * ((-131) + z * ((-155) + z * (14 + z * ((-163) + z * ((-195) + z * ((-175) + z * ((-140) + z * ((-78) + z * ((-12) + z * ((-182) + z * ((-164) + z * ((-67) + z * ((-86) + z * (0 + z * (57 + z * ((-3) + z * 6))))))))))))))))))))))))))))))))))))))


def pow13_4 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (32 + z * (10 + z * (38 + z * (11 + z * (55 + z * (24 + z * (124 + z * (78 + z * (17 + z * (64 + z * (121 + z * (32 + z * (133 + z * (120 + z * (2 + z * (133 + z * (25 + z * (4 + z * 117)))))))))))))))))))

def pow13_4_q {R : Type*} [CommRing R] (z : R) : R := (108 + z * (117 + z * (76 + z * (120 + z * (124 + z * (32 + z * (31 + z * (78 + z * (67 + z * (31 + z * (105 + z * (15 + z * (11 + z * (74 + z * (118 + z * (17 + z * (34 + z * (38 + z * 45))))))))))))))))))

def pow13_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (29 + z * ((-71) + z * ((-177) + z * ((-307) + z * ((-266) + z * ((-288) + z * ((-223) + z * ((-222) + z * ((-201) + z * ((-316) + z * ((-372) + z * ((-171) + z * ((-223) + z * ((-268) + z * ((-238) + z * ((-16) + z * ((-223) + z * ((-111) + z * ((-162) + z * ((-63) + z * ((-120) + z * (58 + z * ((-23) + z * ((-6) + z * (141 + z * (170 + z * (143 + z * (190 + z * (176 + z * (140 + z * (365 + z * (185 + z * (171 + z * (107 + z * (172 + z * (121 + z * (64 + z * ((-18) + z * 76))))))))))))))))))))))))))))))))))))))


def pow13_8 {R : Type*} [CommRing R] (z : R) : R := (55 + z * (34 + z * (116 + z * (112 + z * (84 + z * (73 + z * (123 + z * (87 + z * (29 + z * (66 + z * (56 + z * (123 + z * (128 + z * (11 + z * (83 + z * (73 + z * (110 + z * (88 + z * (125 + z * 50)))))))))))))))))))

def pow13_8_q {R : Type*} [CommRing R] (z : R) : R := (99 + z * (77 + z * (26 + z * (84 + z * (100 + z * (124 + z * (95 + z * (48 + z * (63 + z * (107 + z * (57 + z * (55 + z * (58 + z * (22 + z * (23 + z * (58 + z * (60 + z * (5 + z * 67))))))))))))))))))

def pow13_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-75) + z * ((-143) + z * ((-169) + z * ((-243) + z * ((-305) + z * ((-358) + z * ((-390) + z * ((-448) + z * ((-407) + z * ((-492) + z * ((-493) + z * ((-458) + z * ((-415) + z * ((-514) + z * ((-361) + z * ((-357) + z * ((-425) + z * ((-288) + z * ((-308) + z * ((-409) + z * ((-198) + z * (9 + z * ((-173) + z * ((-40) + z * (106 + z * ((-105) + z * (190 + z * (277 + z * ((-104) + z * (161 + z * (287 + z * ((-113) + z * (240 + z * (139 + z * ((-138) + z * (166 + z * ((-12) + z * ((-55) + z * 98))))))))))))))))))))))))))))))))))))))


def pow13_16 {R : Type*} [CommRing R] (z : R) : R := (69 + z * (6 + z * (18 + z * (29 + z * (98 + z * (28 + z * (100 + z * (50 + z * (73 + z * (55 + z * (7 + z * (16 + z * (25 + z * (2 + z * (98 + z * (42 + z * (129 + z * (65 + z * (36 + z * 38)))))))))))))))))))

def pow13_16_q {R : Type*} [CommRing R] (z : R) : R := (3 + z * (89 + z * (32 + z * (130 + z * (22 + z * (101 + z * (115 + z * (85 + z * (126 + z * (39 + z * (47 + z * (105 + z * (138 + z * (91 + z * (138 + z * (13 + z * (91 + z * (107 + z * 137))))))))))))))))))

def pow13_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (19 + z * ((-43) + z * ((-5) + z * ((-64) + z * ((-29) + z * ((-28) + z * ((-9) + z * ((-35) + z * ((-49) + z * ((-29) + z * ((-109) + z * ((-96) + z * ((-75) + z * ((-94) + z * ((-116) + z * ((-191) + z * ((-197) + z * ((-70) + z * (11 + z * ((-105) + z * ((-29) + z * ((-86) + z * ((-12) + z * (123 + z * ((-80) + z * ((-72) + z * ((-145) + z * ((-181) + z * (73 + z * (96 + z * (9 + z * ((-104) + z * ((-51) + z * (16 + z * (112 + z * (75 + z * ((-24) + z * ((-37) + z * 17))))))))))))))))))))))))))))))))))))))


def pow13_17 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (75 + z * (42 + z * (62 + z * (21 + z * (42 + z * (65 + z * (55 + z * (5 + z * (123 + z * (12 + z * (131 + z * (38 + z * (19 + z * (8 + z * (95 + z * (115 + z * (11 + z * (39 + z * 106)))))))))))))))))))

def pow13_17_q {R : Type*} [CommRing R] (z : R) : R := (54 + z * (16 + z * (53 + z * (31 + z * (82 + z * (115 + z * (34 + z * (101 + z * (110 + z * (135 + z * (12 + z * (25 + z * (111 + z * (95 + z * (48 + z * (97 + z * (120 + z * (124 + z * 28))))))))))))))))))

def pow13_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-27) + z * ((-33) + z * ((-38) + z * ((-96) + z * ((-86) + z * ((-187) + z * ((-89) + z * ((-216) + z * ((-169) + z * ((-336) + z * ((-203) + z * ((-302) + z * ((-243) + z * ((-401) + z * ((-347) + z * ((-458) + z * ((-446) + z * ((-528) + z * ((-401) + z * ((-502) + z * ((-300) + z * ((-373) + z * ((-292) + z * ((-354) + z * ((-312) + z * ((-345) + z * ((-283) + z * ((-329) + z * ((-233) + z * ((-140) + z * ((-209) + z * ((-228) + z * ((-142) + z * ((-60) + z * ((-13) + z * ((-86) + z * ((-62) + z * (18 + z * 8))))))))))))))))))))))))))))))))))))))


def pow13_34 {R : Type*} [CommRing R] (z : R) : R := (131 + z * (23 + z * (53 + z * (102 + z * (63 + z * (110 + z * (132 + z * (88 + z * (63 + z * (84 + z * (108 + z * (28 + z * (79 + z * (25 + z * (35 + z * (63 + z * (47 + z * (0 + z * (47 + z * 108)))))))))))))))))))

def pow13_34_q {R : Type*} [CommRing R] (z : R) : R := (79 + z * (34 + z * (3 + z * (91 + z * (115 + z * (93 + z * (117 + z * (36 + z * (119 + z * (111 + z * (52 + z * (60 + z * (119 + z * (111 + z * (111 + z * (99 + z * (122 + z * (92 + z * 116))))))))))))))))))

def pow13_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-59) + z * ((-79) + z * ((-54) + z * ((-119) + z * ((-180) + z * ((-238) + z * ((-301) + z * ((-325) + z * ((-357) + z * ((-424) + z * ((-377) + z * ((-392) + z * ((-332) + z * ((-588) + z * ((-558) + z * ((-639) + z * ((-662) + z * ((-607) + z * ((-661) + z * ((-848) + z * ((-414) + z * ((-567) + z * ((-498) + z * ((-558) + z * ((-494) + z * ((-390) + z * ((-357) + z * ((-359) + z * ((-310) + z * ((-320) + z * ((-162) + z * ((-272) + z * ((-250) + z * ((-243) + z * ((-68) + z * (1 + z * ((-143) + z * ((-48) + z * 80))))))))))))))))))))))))))))))))))))))


def pow13_68 {R : Type*} [CommRing R] (z : R) : R := (2 + z * (3 + z * (106 + z * (105 + z * (11 + z * (55 + z * (52 + z * (136 + z * (96 + z * (126 + z * (16 + z * (88 + z * (47 + z * (96 + z * (56 + z * (8 + z * (38 + z * (134 + z * (104 + z * 17)))))))))))))))))))

def pow13_68_q {R : Type*} [CommRing R] (z : R) : R := (129 + z * (20 + z * (117 + z * (21 + z * (62 + z * (47 + z * (35 + z * (115 + z * (131 + z * (115 + z * (96 + z * (27 + z * (69 + z * (78 + z * (74 + z * (49 + z * (90 + z * (12 + z * 127))))))))))))))))))

def pow13_68_mul_t {R : Type*} [CommRing R] (z : R) : R := (26 + z * ((-85) + z * ((-119) + z * ((-50) + z * ((-118) + z * (31 + z * (122 + z * (36 + z * ((-17) + z * ((-49) + z * ((-69) + z * ((-111) + z * (35 + z * ((-80) + z * ((-76) + z * ((-59) + z * ((-203) + z * ((-286) + z * ((-323) + z * ((-140) + z * ((-301) + z * ((-198) + z * ((-137) + z * ((-289) + z * ((-79) + z * ((-126) + z * ((-278) + z * ((-269) + z * ((-222) + z * ((-122) + z * ((-100) + z * ((-161) + z * ((-184) + z * ((-99) + z * ((-88) + z * ((-19) + z * ((-89) + z * ((-44) + z * 83))))))))))))))))))))))))))))))))))))))


def pow13_69 {R : Type*} [CommRing R] (z : R) : R := (80 + z * (82 + z * (71 + z * (12 + z * (64 + z * (86 + z * (117 + z * (10 + z * (104 + z * (98 + z * (38 + z * (83 + z * (114 + z * (132 + z * (67 + z * (112 + z * (80 + z * (131 + z * (103 + z * 25)))))))))))))))))))

def pow13_69_q {R : Type*} [CommRing R] (z : R) : R := (107 + z * (111 + z * (98 + z * (137 + z * (13 + z * (27 + z * (9 + z * (130 + z * (16 + z * (124 + z * (114 + z * (8 + z * (52 + z * (52 + z * (66 + z * (21 + z * (24 + z * (44 + z * 93))))))))))))))))))

def pow13_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-81) + z * ((-177) + z * ((-244) + z * ((-327) + z * ((-273) + z * ((-226) + z * ((-151) + z * ((-183) + z * ((-120) + z * ((-148) + z * ((-366) + z * ((-212) + z * ((-289) + z * ((-179) + z * ((-163) + z * ((-43) + z * ((-368) + z * ((-164) + z * ((-286) + z * ((-160) + z * ((-30) + z * (36 + z * ((-171) + z * ((-11) + z * (105 + z * (28 + z * (7 + z * ((-25) + z * ((-148) + z * (52 + z * (87 + z * (31 + z * ((-10) + z * ((-86) + z * (20 + z * (152 + z * (32 + z * ((-47) + z * 3))))))))))))))))))))))))))))))))))))))


def pow13_138 {R : Type*} [CommRing R] (z : R) : R := (86 + z * (73 + z * (96 + z * (47 + z * (117 + z * (101 + z * (125 + z * (61 + z * (73 + z * (134 + z * (50 + z * (120 + z * (9 + z * (65 + z * (31 + z * (59 + z * (87 + z * (112 + z * (58 + z * 1)))))))))))))))))))

def pow13_138_q {R : Type*} [CommRing R] (z : R) : R := (125 + z * (28 + z * (125 + z * (120 + z * (29 + z * (44 + z * (113 + z * (37 + z * (24 + z * (62 + z * (135 + z * (137 + z * (121 + z * (128 + z * (132 + z * (79 + z * (60 + z * (71 + z * 69))))))))))))))))))

def pow13_138_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-49) + z * ((-37) + z * ((-102) + z * ((-247) + z * ((-241) + z * ((-159) + z * ((-112) + z * ((-157) + z * ((-87) + z * ((-141) + z * ((-180) + z * ((-213) + z * ((-272) + z * ((-291) + z * ((-174) + z * ((-328) + z * ((-353) + z * (55 + z * ((-89) + z * ((-140) + z * ((-107) + z * ((-80) + z * ((-14) + z * (173 + z * (69 + z * (16 + z * (124 + z * (63 + z * (58 + z * (73 + z * (130 + z * (87 + z * (64 + z * (57 + z * (107 + z * (115 + z * (7 + z * ((-27) + z * 4))))))))))))))))))))))))))))))))))))))


def pow13_139 {R : Type*} [CommRing R] (z : R) : R := (82 + z * (85 + z * (128 + z * (125 + z * (89 + z * (72 + z * (18 + z * (116 + z * (63 + z * (21 + z * (127 + z * (70 + z * (15 + z * (52 + z * (25 + z * (92 + z * (4 + z * (74 + z * (10 + z * 128)))))))))))))))))))

def pow13_139_q {R : Type*} [CommRing R] (z : R) : R := (136 + z * (74 + z * (65 + z * (106 + z * (121 + z * (111 + z * (44 + z * (75 + z * (67 + z * (118 + z * (124 + z * (107 + z * (36 + z * (119 + z * (4 + z * (9 + z * (88 + z * (120 + z * 30))))))))))))))))))

def pow13_139_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-86) + z * ((-129) + z * ((-117) + z * ((-198) + z * ((-198) + z * ((-246) + z * ((-114) + z * ((-202) + z * ((-91) + z * ((-240) + z * ((-249) + z * ((-284) + z * ((-215) + z * ((-361) + z * ((-335) + z * ((-166) + z * ((-352) + z * ((-196) + z * ((-304) + z * ((-301) + z * ((-304) + z * ((-145) + z * ((-141) + z * ((-120) + z * ((-129) + z * ((-142) + z * ((-255) + z * ((-114) + z * ((-56) + z * ((-105) + z * ((-79) + z * ((-82) + z * ((-130) + z * (11 + z * (75 + z * ((-4) + z * ((-52) + z * ((-15) + z * 0))))))))))))))))))))))))))))))))))))))


def pow14_2 {R : Type*} [CommRing R] (z : R) : R := (79 + z * (97 + z * (110 + z * (22 + z * (128 + z * (72 + z * (91 + z * (9 + z * (128 + z * (69 + z * (108 + z * (52 + z * (118 + z * (4 + z * (129 + z * (89 + z * (9 + z * (118 + z * (59 + z * 70)))))))))))))))))))

def pow14_2_q {R : Type*} [CommRing R] (z : R) : R := (103 + z * (81 + z * (137 + z * (41 + z * (131 + z * (29 + z * (101 + z * (99 + z * (104 + z * (105 + z * (73 + z * (85 + z * (4 + z * (9 + z * (36 + z * (35 + z * (19 + z * (138 + z * 121))))))))))))))))))

def pow14_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-30) + z * ((-52) + z * ((-65) + z * ((-18) + z * ((-41) + z * (25 + z * ((-41) + z * ((-21) + z * ((-114) + z * ((-202) + z * ((-178) + z * ((-198) + z * ((-114) + z * ((-116) + z * ((-127) + z * ((-97) + z * ((-267) + z * ((-197) + z * ((-320) + z * ((-341) + z * ((-264) + z * ((-181) + z * ((-80) + z * ((-178) + z * ((-173) + z * ((-222) + z * ((-145) + z * ((-239) + z * ((-156) + z * (42 + z * ((-52) + z * ((-156) + z * (8 + z * ((-188) + z * (62 + z * ((-101) + z * ((-79) + z * ((-94) + z * 117))))))))))))))))))))))))))))))))))))))


def pow14_4 {R : Type*} [CommRing R] (z : R) : R := (124 + z * (107 + z * (46 + z * (82 + z * (86 + z * (103 + z * (89 + z * (67 + z * (30 + z * (105 + z * (115 + z * (41 + z * (36 + z * (80 + z * (114 + z * (31 + z * (12 + z * (67 + z * (44 + z * 135)))))))))))))))))))

def pow14_4_q {R : Type*} [CommRing R] (z : R) : R := (94 + z * (90 + z * (115 + z * (103 + z * (71 + z * (35 + z * (73 + z * (63 + z * (44 + z * (89 + z * (20 + z * (18 + z * (13 + z * (41 + z * (66 + z * (31 + z * (48 + z * (27 + z * 35))))))))))))))))))

def pow14_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-27) + z * ((-41) + z * ((-58) + z * ((-171) + z * ((-144) + z * ((-95) + z * (12 + z * ((-118) + z * (26 + z * ((-79) + z * (53 + z * ((-71) + z * (194 + z * (17 + z * (271 + z * (55 + z * (190 + z * (28 + z * (253 + z * (199 + z * (298 + z * (175 + z * (207 + z * (336 + z * (211 + z * (216 + z * (259 + z * (253 + z * (147 + z * (338 + z * (78 + z * (210 + z * (107 + z * (92 + z * (104 + z * (45 + z * (93 + z * (27 + z * 35))))))))))))))))))))))))))))))))))))))


def pow14_8 {R : Type*} [CommRing R] (z : R) : R := (115 + z * (81 + z * (35 + z * (90 + z * (23 + z * (22 + z * (127 + z * (49 + z * (101 + z * (45 + z * (107 + z * (101 + z * (49 + z * (65 + z * (75 + z * (118 + z * (137 + z * (81 + z * (89 + z * 83)))))))))))))))))))

def pow14_8_q {R : Type*} [CommRing R] (z : R) : R := (54 + z * (33 + z * (30 + z * (81 + z * (90 + z * (50 + z * (21 + z * (110 + z * (34 + z * (104 + z * (30 + z * (62 + z * (116 + z * (59 + z * (9 + z * (43 + z * (56 + z * (102 + z * 16))))))))))))))))))

def pow14_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (69 + z * (118 + z * (64 + z * (48 + z * (55 + z * (110 + z * (152 + z * (80 + z * (47 + z * (107 + z * (197 + z * (95 + z * ((-12) + z * ((-1) + z * (196 + z * (149 + z * ((-45) + z * ((-16) + z * (38 + z * (186 + z * (118 + z * ((-29) + z * ((-17) + z * (162 + z * (210 + z * ((-91) + z * ((-64) + z * ((-14) + z * (103 + z * (121 + z * ((-94) + z * ((-44) + z * (78 + z * (117 + z * (6 + z * ((-61) + z * (38 + z * (70 + z * 131))))))))))))))))))))))))))))))))))))))


def pow14_16 {R : Type*} [CommRing R] (z : R) : R := (58 + z * (4 + z * (95 + z * (33 + z * (31 + z * (24 + z * (122 + z * (41 + z * (8 + z * (123 + z * (92 + z * (65 + z * (131 + z * (91 + z * (138 + z * (99 + z * (91 + z * (111 + z * (111 + z * 1)))))))))))))))))))

def pow14_16_q {R : Type*} [CommRing R] (z : R) : R := (42 + z * (118 + z * (110 + z * (33 + z * (30 + z * (124 + z * (36 + z * (127 + z * (76 + z * (9 + z * (71 + z * (89 + z * (106 + z * (7 + z * (135 + z * (54 + z * (76 + z * (64 + z * 78))))))))))))))))))

def pow14_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (63 + z * (8 + z * ((-120) + z * ((-78) + z * ((-144) + z * ((-251) + z * ((-26) + z * ((-121) + z * ((-159) + z * ((-115) + z * ((-160) + z * ((-116) + z * ((-124) + z * ((-70) + z * ((-155) + z * ((-221) + z * (53 + z * ((-31) + z * ((-21) + z * (124 + z * ((-180) + z * ((-40) + z * (232 + z * (62 + z * (115 + z * (212 + z * (148 + z * (147 + z * (186 + z * (220 + z * (89 + z * (165 + z * (203 + z * (133 + z * (192 + z * (150 + z * (37 + z * (34 + z * 49))))))))))))))))))))))))))))))))))))))


def pow14_17 {R : Type*} [CommRing R] (z : R) : R := (107 + z * (104 + z * (80 + z * (56 + z * (33 + z * (123 + z * (35 + z * (99 + z * (118 + z * (70 + z * (53 + z * (15 + z * (84 + z * (16 + z * (24 + z * (26 + z * (1 + z * (19 + z * (6 + z * 98)))))))))))))))))))

def pow14_17_q {R : Type*} [CommRing R] (z : R) : R := (129 + z * (66 + z * (72 + z * (37 + z * (72 + z * (61 + z * (75 + z * (44 + z * (101 + z * (103 + z * (113 + z * (41 + z * (120 + z * (96 + z * (22 + z * (97 + z * (55 + z * (58 + z * 128))))))))))))))))))

def pow14_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-64) + z * ((-126) + z * ((-117) + z * ((-140) + z * ((-149) + z * ((-121) + z * ((-116) + z * ((-100) + z * ((-200) + z * ((-197) + z * ((-262) + z * ((-217) + z * ((-179) + z * ((-193) + z * ((-133) + z * ((-193) + z * ((-128) + z * (26 + z * ((-284) + z * ((-145) + z * ((-146) + z * ((-57) + z * ((-170) + z * ((-126) + z * ((-85) + z * ((-92) + z * ((-155) + z * ((-146) + z * ((-144) + z * (10 + z * ((-58) + z * ((-116) + z * (1 + z * (37 + z * ((-76) + z * (57 + z * ((-37) + z * ((-16) + z * 0))))))))))))))))))))))))))))))))))))))


def pow14_34 {R : Type*} [CommRing R] (z : R) : R := (43 + z * (118 + z * (20 + z * (29 + z * (12 + z * (14 + z * (3 + z * (74 + z * (55 + z * (49 + z * (124 + z * (62 + z * (10 + z * (38 + z * (101 + z * (102 + z * (5 + z * (64 + z * (69 + z * 108)))))))))))))))))))

def pow14_34_q {R : Type*} [CommRing R] (z : R) : R := (57 + z * (44 + z * (131 + z * (8 + z * (93 + z * (122 + z * (84 + z * (102 + z * (99 + z * (14 + z * (65 + z * (137 + z * (122 + z * (20 + z * (15 + z * (134 + z * (124 + z * (68 + z * 13))))))))))))))))))

def pow14_34_mul_t {R : Type*} [CommRing R] (z : R) : R := (39 + z * (76 + z * (12 + z * ((-9) + z * ((-101) + z * ((-54) + z * ((-99) + z * ((-69) + z * ((-56) + z * ((-57) + z * ((-27) + z * ((-252) + z * ((-191) + z * ((-177) + z * ((-308) + z * ((-418) + z * ((-450) + z * ((-445) + z * ((-654) + z * ((-405) + z * ((-502) + z * ((-544) + z * ((-330) + z * ((-488) + z * ((-393) + z * ((-533) + z * ((-393) + z * ((-231) + z * ((-247) + z * ((-270) + z * ((-395) + z * ((-233) + z * ((-151) + z * ((-141) + z * ((-186) + z * ((-162) + z * ((-46) + z * ((-4) + z * 69))))))))))))))))))))))))))))))))))))))


def pow14_68 {R : Type*} [CommRing R] (z : R) : R := (31 + z * (86 + z * (79 + z * (46 + z * (57 + z * (41 + z * (135 + z * (28 + z * (103 + z * (104 + z * (40 + z * (10 + z * (9 + z * (108 + z * (101 + z * (80 + z * (6 + z * (29 + z * (15 + z * 26)))))))))))))))))))

def pow14_68_q {R : Type*} [CommRing R] (z : R) : R := (61 + z * (111 + z * (83 + z * (41 + z * (48 + z * (54 + z * (41 + z * (89 + z * (45 + z * (37 + z * (1 + z * (79 + z * (35 + z * (53 + z * (64 + z * (17 + z * (72 + z * (38 + z * 127))))))))))))))))))

def pow14_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-33) + z * ((-65) + z * ((-103) + z * ((-210) + z * ((-241) + z * ((-267) + z * ((-246) + z * ((-267) + z * ((-208) + z * ((-270) + z * ((-239) + z * ((-181) + z * ((-229) + z * ((-321) + z * ((-325) + z * ((-226) + z * ((-295) + z * ((-323) + z * ((-247) + z * ((-270) + z * ((-251) + z * ((-286) + z * ((-166) + z * ((-169) + z * ((-35) + z * (12 + z * ((-85) + z * ((-83) + z * (95 + z * (158 + z * ((-36) + z * ((-113) + z * (20 + z * (78 + z * (18 + z * ((-23) + z * (5 + z * ((-10) + z * 83))))))))))))))))))))))))))))))))))))))


def pow14_69 {R : Type*} [CommRing R] (z : R) : R := (117 + z * (24 + z * (37 + z * (52 + z * (27 + z * (39 + z * (119 + z * (23 + z * (10 + z * (50 + z * (76 + z * (29 + z * (130 + z * (86 + z * (17 + z * (58 + z * (52 + z * (87 + z * (88 + z * 64)))))))))))))))))))

def pow14_69_q {R : Type*} [CommRing R] (z : R) : R := (129 + z * (101 + z * (13 + z * (121 + z * (6 + z * (34 + z * (84 + z * (28 + z * (70 + z * (51 + z * (87 + z * (6 + z * (136 + z * (11 + z * (15 + z * (106 + z * (7 + z * (7 + z * 131))))))))))))))))))

def pow14_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-80) + z * ((-120) + z * ((-87) + z * ((-134) + z * ((-88) + z * ((-27) + z * ((-2) + z * ((-41) + z * (36 + z * ((-7) + z * ((-128) + z * (24 + z * ((-95) + z * ((-144) + z * ((-85) + z * ((-96) + z * ((-99) + z * (42 + z * ((-186) + z * ((-320) + z * ((-77) + z * ((-113) + z * ((-277) + z * (56 + z * ((-73) + z * ((-137) + z * ((-107) + z * ((-120) + z * ((-212) + z * ((-22) + z * ((-78) + z * ((-262) + z * (94 + z * ((-64) + z * ((-105) + z * (4 + z * ((-61) + z * ((-105) + z * 23))))))))))))))))))))))))))))))))))))))


def pow14_138 {R : Type*} [CommRing R] (z : R) : R := (128 + z * (56 + z * (10 + z * (89 + z * (92 + z * (56 + z * (25 + z * (87 + z * (37 + z * (9 + z * (10 + z * (28 + z * (52 + z * (58 + z * (55 + z * (84 + z * (89 + z * (88 + z * (47 + z * 97)))))))))))))))))))

def pow14_138_q {R : Type*} [CommRing R] (z : R) : R := (104 + z * (87 + z * (88 + z * (35 + z * (59 + z * (99 + z * (102 + z * (70 + z * (60 + z * (68 + z * (129 + z * (129 + z * (82 + z * (70 + z * (26 + z * (123 + z * (15 + z * (25 + z * 65))))))))))))))))))

def pow14_138_mul_t {R : Type*} [CommRing R] (z : R) : R := (19 + z * ((-117) + z * ((-170) + z * ((-181) + z * ((-246) + z * ((-239) + z * ((-134) + z * ((-309) + z * ((-364) + z * ((-354) + z * ((-428) + z * ((-500) + z * ((-283) + z * ((-468) + z * ((-585) + z * ((-495) + z * ((-442) + z * ((-371) + z * ((-297) + z * ((-407) + z * ((-532) + z * ((-359) + z * ((-190) + z * ((-210) + z * ((-205) + z * ((-202) + z * ((-243) + z * ((-114) + z * ((-120) + z * ((-27) + z * (10 + z * ((-18) + z * (53 + z * ((-23) + z * ((-5) + z * (125 + z * (65 + z * (21 + z * 29))))))))))))))))))))))))))))))))))))))


def pow14_139 {R : Type*} [CommRing R] (z : R) : R := (102 + z * (126 + z * (14 + z * (108 + z * (2 + z * (133 + z * (5 + z * (72 + z * (44 + z * (33 + z * (117 + z * (67 + z * (127 + z * (118 + z * (87 + z * (46 + z * (24 + z * (117 + z * (56 + z * 77)))))))))))))))))))

def pow14_139_q {R : Type*} [CommRing R] (z : R) : R := (5 + z * (49 + z * (76 + z * (0 + z * (76 + z * (71 + z * (29 + z * (47 + z * (18 + z * (97 + z * (24 + z * (69 + z * (24 + z * (109 + z * (84 + z * (11 + z * (8 + z * (114 + z * 45))))))))))))))))))

def pow14_139_mul_t {R : Type*} [CommRing R] (z : R) : R := (71 + z * (69 + z * (53 + z * (109 + z * (74 + z * (49 + z * (37 + z * (137 + z * (95 + z * ((-33) + z * (60 + z * ((-30) + z * ((-110) + z * ((-104) + z * ((-122) + z * ((-53) + z * ((-47) + z * ((-70) + z * ((-38) + z * (90 + z * ((-76) + z * ((-79) + z * (55 + z * ((-65) + z * ((-57) + z * ((-65) + z * ((-4) + z * ((-148) + z * ((-97) + z * ((-21) + z * ((-59) + z * ((-20) + z * ((-53) + z * ((-55) + z * (142 + z * (25 + z * ((-2) + z * (8 + z * 89))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Powers08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139
def pow15_2 {R : Type*} [CommRing R] (z : R) : R := (110 + z * (44 + z * (117 + z * (109 + z * (125 + z * (57 + z * (49 + z * (116 + z * (37 + z * (132 + z * (115 + z * (36 + z * (125 + z * (48 + z * (90 + z * (58 + z * (121 + z * (14 + z * (23 + z * 38)))))))))))))))))))

def pow15_2_q {R : Type*} [CommRing R] (z : R) : R := (57 + z * (14 + z * (23 + z * (36 + z * (41 + z * (95 + z * (53 + z * (60 + z * (56 + z * (130 + z * (27 + z * (126 + z * (64 + z * (122 + z * (112 + z * (3 + z * (14 + z * (34 + z * 91))))))))))))))))))

def pow15_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (31 + z * (124 + z * (53 + z * (69 + z * (58 + z * (30 + z * (96 + z * ((-144) + z * (79 + z * ((-267) + z * (52 + z * ((-77) + z * ((-12) + z * (47 + z * ((-106) + z * (12 + z * ((-158) + z * (138 + z * (31 + z * ((-13) + z * (112 + z * ((-210) + z * (108 + z * ((-48) + z * (87 + z * (55 + z * (52 + z * ((-37) + z * ((-1) + z * (161 + z * (102 + z * (138 + z * (16 + z * ((-19) + z * (79 + z * (83 + z * (54 + z * ((-22) + z * 42))))))))))))))))))))))))))))))))))))))


def pow15_4 {R : Type*} [CommRing R] (z : R) : R := (11 + z * (131 + z * (134 + z * (32 + z * (83 + z * (1 + z * (92 + z * (5 + z * (73 + z * (37 + z * (45 + z * (21 + z * (82 + z * (57 + z * (42 + z * (90 + z * (79 + z * (110 + z * (105 + z * 96)))))))))))))))))))

def pow15_4_q {R : Type*} [CommRing R] (z : R) : R := (41 + z * (132 + z * (31 + z * (2 + z * (18 + z * (29 + z * (45 + z * (34 + z * (68 + z * (96 + z * (72 + z * (27 + z * (36 + z * (3 + z * (83 + z * (14 + z * (24 + z * (118 + z * 54))))))))))))))))))

def pow15_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (56 + z * ((-67) + z * (22 + z * (60 + z * (164 + z * (168 + z * (253 + z * (319 + z * (145 + z * (246 + z * (167 + z * (198 + z * (416 + z * (375 + z * (410 + z * (304 + z * (542 + z * (239 + z * (303 + z * (316 + z * (129 + z * (276 + z * (255 + z * (261 + z * (98 + z * (144 + z * (156 + z * ((-112) + z * (127 + z * (47 + z * ((-12) + z * (41 + z * ((-9) + z * ((-127) + z * ((-3) + z * ((-38) + z * ((-137) + z * ((-38) + z * 10))))))))))))))))))))))))))))))))))))))


def pow15_8 {R : Type*} [CommRing R] (z : R) : R := (68 + z * (74 + z * (84 + z * (57 + z * (28 + z * (121 + z * (72 + z * (108 + z * (64 + z * (78 + z * (98 + z * (2 + z * (49 + z * (14 + z * (75 + z * (46 + z * (17 + z * (52 + z * (126 + z * 91)))))))))))))))))))

def pow15_8_q {R : Type*} [CommRing R] (z : R) : R := (117 + z * (2 + z * (110 + z * (5 + z * (88 + z * (105 + z * (49 + z * (29 + z * (125 + z * (25 + z * (41 + z * (22 + z * (94 + z * (36 + z * (138 + z * (135 + z * (55 + z * (50 + z * 42))))))))))))))))))

def pow15_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-88) + z * ((-84) + z * ((-46) + z * (44 + z * ((-61) + z * ((-85) + z * ((-157) + z * ((-132) + z * ((-191) + z * ((-278) + z * ((-145) + z * ((-241) + z * ((-219) + z * ((-260) + z * ((-190) + z * ((-492) + z * ((-276) + z * ((-270) + z * ((-283) + z * ((-16) + z * (45 + z * ((-104) + z * ((-149) + z * ((-181) + z * ((-274) + z * ((-51) + z * ((-97) + z * ((-94) + z * ((-73) + z * (41 + z * ((-22) + z * (47 + z * (99 + z * (24 + z * (130 + z * (187 + z * (154 + z * (106 + z * 66))))))))))))))))))))))))))))))))))))))


def pow15_16 {R : Type*} [CommRing R] (z : R) : R := (54 + z * (74 + z * (103 + z * (96 + z * (73 + z * (109 + z * (124 + z * (31 + z * (78 + z * (14 + z * (20 + z * (58 + z * (3 + z * (54 + z * (112 + z * (68 + z * (17 + z * (17 + z * (7 + z * 54)))))))))))))))))))

def pow15_16_q {R : Type*} [CommRing R] (z : R) : R := (70 + z * (80 + z * (79 + z * (95 + z * (53 + z * (84 + z * (38 + z * (60 + z * (130 + z * (97 + z * (22 + z * (54 + z * (134 + z * (132 + z * (70 + z * (136 + z * (0 + z * (43 + z * 80))))))))))))))))))

def pow15_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * ((-50) + z * ((-72) + z * ((-135) + z * ((-187) + z * ((-138) + z * ((-95) + z * ((-18) + z * ((-77) + z * ((-158) + z * ((-104) + z * ((-181) + z * ((-180) + z * ((-329) + z * ((-281) + z * ((-367) + z * ((-472) + z * ((-353) + z * ((-443) + z * ((-200) + z * ((-155) + z * ((-351) + z * ((-335) + z * ((-169) + z * ((-74) + z * ((-138) + z * ((-117) + z * ((-240) + z * ((-204) + z * ((-79) + z * ((-218) + z * ((-270) + z * ((-44) + z * ((-58) + z * ((-82) + z * (84 + z * (84 + z * (91 + z * 59))))))))))))))))))))))))))))))))))))))


def pow15_17 {R : Type*} [CommRing R] (z : R) : R := (22 + z * (85 + z * (103 + z * (63 + z * (39 + z * (82 + z * (63 + z * (119 + z * (81 + z * (88 + z * (17 + z * (8 + z * (30 + z * (81 + z * (73 + z * (54 + z * (58 + z * (60 + z * (33 + z * 17)))))))))))))))))))

def pow15_17_q {R : Type*} [CommRing R] (z : R) : R := (133 + z * (29 + z * (56 + z * (44 + z * (73 + z * (93 + z * (66 + z * (104 + z * (129 + z * (96 + z * (27 + z * (117 + z * (11 + z * (114 + z * (92 + z * (129 + z * (2 + z * (95 + z * 127))))))))))))))))))

def pow15_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-61) + z * ((-36) + z * ((-40) + z * ((-22) + z * ((-67) + z * ((-2) + z * (8 + z * ((-92) + z * ((-183) + z * ((-269) + z * ((-322) + z * ((-199) + z * ((-229) + z * ((-216) + z * ((-165) + z * ((-253) + z * ((-245) + z * ((-315) + z * ((-398) + z * ((-304) + z * ((-254) + z * ((-397) + z * ((-295) + z * ((-326) + z * ((-329) + z * ((-224) + z * ((-291) + z * ((-353) + z * ((-243) + z * ((-168) + z * ((-218) + z * ((-161) + z * ((-97) + z * ((-198) + z * ((-149) + z * ((-41) + z * ((-123) + z * ((-92) + z * 29))))))))))))))))))))))))))))))))))))))


def pow15_34 {R : Type*} [CommRing R] (z : R) : R := (120 + z * (118 + z * (98 + z * (84 + z * (14 + z * (119 + z * (63 + z * (89 + z * (54 + z * (11 + z * (65 + z * (15 + z * (93 + z * (54 + z * (65 + z * (70 + z * (118 + z * (106 + z * (20 + z * 75)))))))))))))))))))

def pow15_34_q {R : Type*} [CommRing R] (z : R) : R := (22 + z * (46 + z * (87 + z * (128 + z * (65 + z * (124 + z * (59 + z * (130 + z * (0 + z * (133 + z * (126 + z * (28 + z * (71 + z * (11 + z * (110 + z * (57 + z * (112 + z * (131 + z * 11))))))))))))))))))

def pow15_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-14) + z * ((-28) + z * ((-42) + z * ((-90) + z * ((-135) + z * ((-225) + z * ((-217) + z * ((-207) + z * ((-93) + z * ((-121) + z * ((-198) + z * ((-278) + z * ((-355) + z * ((-357) + z * ((-237) + z * ((-232) + z * ((-337) + z * ((-461) + z * ((-478) + z * ((-491) + z * ((-414) + z * ((-287) + z * ((-274) + z * ((-323) + z * ((-315) + z * ((-407) + z * ((-308) + z * ((-260) + z * ((-285) + z * ((-222) + z * ((-211) + z * ((-104) + z * ((-148) + z * ((-166) + z * ((-78) + z * ((-157) + z * ((-107) + z * ((-3) + z * 2))))))))))))))))))))))))))))))))))))))


def pow15_68 {R : Type*} [CommRing R] (z : R) : R := (104 + z * (131 + z * (113 + z * (29 + z * (52 + z * (23 + z * (57 + z * (1 + z * (101 + z * (113 + z * (33 + z * (64 + z * (12 + z * (61 + z * (61 + z * (16 + z * (123 + z * (82 + z * (38 + z * 50)))))))))))))))))))

def pow15_68_q {R : Type*} [CommRing R] (z : R) : R := (111 + z * (23 + z * (104 + z * (17 + z * (126 + z * (56 + z * (88 + z * (29 + z * (53 + z * (29 + z * (99 + z * (50 + z * (138 + z * (108 + z * (103 + z * (125 + z * (78 + z * (101 + z * 65))))))))))))))))))

def pow15_68_mul_t {R : Type*} [CommRing R] (z : R) : R := (19 + z * (88 + z * (70 + z * (81 + z * ((-77) + z * (29 + z * (9 + z * (62 + z * (65 + z * ((-96) + z * ((-72) + z * ((-143) + z * ((-113) + z * ((-202) + z * ((-292) + z * ((-265) + z * ((-271) + z * ((-52) + z * ((-234) + z * ((-174) + z * ((-228) + z * ((-224) + z * ((-128) + z * ((-293) + z * ((-136) + z * ((-325) + z * ((-230) + z * ((-214) + z * ((-253) + z * ((-75) + z * ((-186) + z * ((-130) + z * ((-49) + z * ((-43) + z * ((-37) + z * (11 + z * ((-24) + z * ((-39) + z * 40))))))))))))))))))))))))))))))))))))))


def pow15_69 {R : Type*} [CommRing R] (z : R) : R := (65 + z * (108 + z * (42 + z * (136 + z * (40 + z * (116 + z * (97 + z * (71 + z * (3 + z * (24 + z * (121 + z * (121 + z * (136 + z * (134 + z * (29 + z * (103 + z * (12 + z * (35 + z * (77 + z * 66)))))))))))))))))))

def pow15_69_q {R : Type*} [CommRing R] (z : R) : R := (111 + z * (130 + z * (78 + z * (131 + z * (130 + z * (62 + z * (131 + z * (115 + z * (59 + z * (108 + z * (85 + z * (121 + z * (112 + z * (32 + z * (97 + z * (52 + z * (30 + z * (121 + z * 97))))))))))))))))))

def pow15_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-8) + z * ((-6) + z * ((-61) + z * ((-173) + z * ((-315) + z * ((-233) + z * ((-313) + z * ((-352) + z * ((-393) + z * ((-311) + z * ((-493) + z * ((-390) + z * ((-398) + z * ((-433) + z * ((-346) + z * ((-479) + z * ((-461) + z * ((-436) + z * ((-418) + z * ((-487) + z * ((-516) + z * ((-345) + z * ((-455) + z * ((-253) + z * ((-320) + z * ((-360) + z * ((-151) + z * ((-230) + z * ((-95) + z * ((-23) + z * ((-145) + z * ((-76) + z * ((-58) + z * ((-89) + z * ((-1) + z * (25 + z * ((-80) + z * ((-49) + z * 27))))))))))))))))))))))))))))))))))))))


def pow15_138 {R : Type*} [CommRing R] (z : R) : R := (127 + z * (18 + z * (8 + z * (95 + z * (102 + z * (102 + z * (77 + z * (96 + z * (8 + z * (112 + z * (80 + z * (74 + z * (60 + z * (129 + z * (16 + z * (12 + z * (17 + z * (29 + z * (0 + z * 35)))))))))))))))))))

def pow15_138_q {R : Type*} [CommRing R] (z : R) : R := (43 + z * (118 + z * (74 + z * (70 + z * (82 + z * (117 + z * (134 + z * (56 + z * (127 + z * (90 + z * (91 + z * (43 + z * (135 + z * (51 + z * (105 + z * (83 + z * (92 + z * (117 + z * 47))))))))))))))))))

def pow15_138_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-3) + z * ((-26) + z * ((-75) + z * ((-73) + z * ((-75) + z * ((-147) + z * ((-25) + z * ((-120) + z * ((-167) + z * ((-316) + z * ((-264) + z * ((-188) + z * ((-127) + z * ((-11) + z * ((-173) + z * ((-137) + z * ((-65) + z * ((-246) + z * ((-149) + z * ((-360) + z * ((-256) + z * ((-258) + z * ((-83) + z * ((-33) + z * ((-93) + z * ((-62) + z * ((-145) + z * ((-252) + z * ((-66) + z * ((-2) + z * ((-25) + z * ((-73) + z * ((-84) + z * ((-138) + z * ((-64) + z * ((-121) + z * ((-67) + z * (29 + z * 31))))))))))))))))))))))))))))))))))))))


def pow15_139 {R : Type*} [CommRing R] (z : R) : R := (134 + z * (115 + z * (50 + z * (21 + z * (78 + z * (128 + z * (94 + z * (113 + z * (17 + z * (72 + z * (82 + z * (137 + z * (28 + z * (122 + z * (89 + z * (66 + z * (119 + z * (120 + z * (87 + z * 10)))))))))))))))))))

def pow15_139_q {R : Type*} [CommRing R] (z : R) : R := (89 + z * (72 + z * (72 + z * (17 + z * (81 + z * (17 + z * (125 + z * (44 + z * (35 + z * (91 + z * (51 + z * (29 + z * (2 + z * (29 + z * (75 + z * (20 + z * (2 + z * (52 + z * 54))))))))))))))))))

def pow15_139_mul_t {R : Type*} [CommRing R] (z : R) : R := (25 + z * ((-5) + z * ((-163) + z * ((-48) + z * ((-102) + z * (53 + z * ((-53) + z * ((-40) + z * ((-55) + z * ((-157) + z * ((-21) + z * ((-83) + z * (119 + z * (58 + z * (127 + z * ((-24) + z * (41 + z * (123 + z * (67 + z * ((-53) + z * (29 + z * (80 + z * (116 + z * (164 + z * (117 + z * (7 + z * (140 + z * ((-11) + z * (11 + z * (54 + z * (66 + z * (43 + z * ((-9) + z * ((-107) + z * ((-16) + z * ((-13) + z * ((-42) + z * ((-36) + z * 19))))))))))))))))))))))))))))))))))))))


def pow16_2 {R : Type*} [CommRing R] (z : R) : R := (108 + z * (110 + z * (20 + z * (130 + z * (133 + z * (8 + z * (121 + z * (19 + z * (122 + z * (62 + z * (119 + z * (83 + z * (11 + z * (118 + z * (99 + z * (102 + z * (0 + z * (120 + z * (110 + z * 20)))))))))))))))))))

def pow16_2_q {R : Type*} [CommRing R] (z : R) : R := (121 + z * (136 + z * (134 + z * (133 + z * (119 + z * (27 + z * (43 + z * (69 + z * (12 + z * (138 + z * (4 + z * (19 + z * (8 + z * (69 + z * (90 + z * (36 + z * (12 + z * (60 + z * 100))))))))))))))))))

def pow16_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (37 + z * (12 + z * ((-138) + z * ((-333) + z * ((-349) + z * ((-124) + z * ((-26) + z * (3 + z * ((-88) + z * ((-155) + z * ((-121) + z * (111 + z * (63 + z * (6 + z * (129 + z * (133 + z * (165 + z * (250 + z * (317 + z * ((-3) + z * (168 + z * (223 + z * (238 + z * (349 + z * (394 + z * (215 + z * (270 + z * (249 + z * (204 + z * (328 + z * (242 + z * (209 + z * (125 + z * (77 + z * (136 + z * (112 + z * ((-57) + z * ((-80) + z * 0))))))))))))))))))))))))))))))))))))))


def pow16_4 {R : Type*} [CommRing R] (z : R) : R := (83 + z * (89 + z * (68 + z * (8 + z * (60 + z * (66 + z * (107 + z * (61 + z * (90 + z * (76 + z * (63 + z * (10 + z * (103 + z * (67 + z * (27 + z * (74 + z * (35 + z * (104 + z * (82 + z * 52)))))))))))))))))))

def pow16_4_q {R : Type*} [CommRing R] (z : R) : R := (105 + z * (118 + z * (120 + z * (39 + z * (109 + z * (123 + z * (46 + z * (125 + z * (126 + z * (70 + z * (89 + z * (18 + z * (102 + z * (23 + z * (0 + z * (61 + z * (64 + z * (43 + z * 122))))))))))))))))))

def pow16_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (4 + z * ((-11) + z * ((-171) + z * ((-107) + z * ((-4) + z * ((-202) + z * ((-84) + z * ((-43) + z * ((-230) + z * ((-149) + z * ((-179) + z * ((-139) + z * ((-85) + z * ((-111) + z * (186 + z * ((-108) + z * ((-33) + z * (62 + z * (100 + z * ((-6) + z * ((-242) + z * (218 + z * ((-26) + z * (83 + z * (93 + z * (22 + z * (4 + z * (89 + z * (161 + z * (92 + z * (92 + z * (26 + z * (213 + z * (31 + z * ((-72) + z * (99 + z * ((-8) + z * ((-81) + z * 2))))))))))))))))))))))))))))))))))))))


def pow16_8 {R : Type*} [CommRing R] (z : R) : R := (39 + z * (82 + z * (88 + z * (48 + z * (83 + z * (30 + z * (71 + z * (4 + z * (117 + z * (50 + z * (105 + z * (86 + z * (15 + z * (38 + z * (37 + z * (70 + z * (16 + z * (128 + z * (128 + z * 131)))))))))))))))))))

def pow16_8_q {R : Type*} [CommRing R] (z : R) : R := (52 + z * (57 + z * (50 + z * (95 + z * (105 + z * (99 + z * (53 + z * (41 + z * (40 + z * (131 + z * (22 + z * (119 + z * (37 + z * (62 + z * (25 + z * (117 + z * (94 + z * (47 + z * 63))))))))))))))))))

def pow16_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (10 + z * (17 + z * (3 + z * ((-120) + z * ((-188) + z * ((-197) + z * ((-115) + z * ((-123) + z * ((-74) + z * ((-133) + z * ((-104) + z * ((-238) + z * ((-184) + z * ((-204) + z * ((-127) + z * ((-220) + z * ((-256) + z * ((-193) + z * ((-214) + z * ((-251) + z * ((-205) + z * ((-157) + z * ((-174) + z * ((-63) + z * ((-113) + z * ((-69) + z * ((-55) + z * ((-63) + z * ((-148) + z * ((-63) + z * ((-49) + z * ((-83) + z * ((-9) + z * ((-29) + z * ((-55) + z * (27 + z * (36 + z * (3 + z * 19))))))))))))))))))))))))))))))))))))))


def pow16_16 {R : Type*} [CommRing R] (z : R) : R := (12 + z * (110 + z * (104 + z * (95 + z * (131 + z * (46 + z * (66 + z * (74 + z * (72 + z * (114 + z * (17 + z * (68 + z * (8 + z * (62 + z * (38 + z * (129 + z * (30 + z * (54 + z * (25 + z * 35)))))))))))))))))))

def pow16_16_q {R : Type*} [CommRing R] (z : R) : R := (66 + z * (101 + z * (94 + z * (106 + z * (91 + z * (112 + z * (67 + z * (25 + z * (120 + z * (18 + z * (36 + z * (4 + z * (95 + z * (118 + z * (125 + z * (12 + z * (113 + z * (46 + z * 64))))))))))))))))))

def pow16_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-39) + z * ((-89) + z * ((-122) + z * ((-186) + z * ((-236) + z * ((-273) + z * ((-262) + z * ((-267) + z * ((-278) + z * ((-267) + z * ((-195) + z * ((-196) + z * ((-129) + z * ((-324) + z * ((-357) + z * ((-455) + z * ((-450) + z * ((-425) + z * ((-316) + z * ((-63) + z * ((-128) + z * ((-100) + z * ((-203) + z * ((-91) + z * ((-200) + z * (92 + z * ((-69) + z * (79 + z * (135 + z * (79 + z * (12 + z * ((-153) + z * ((-81) + z * (24 + z * (131 + z * (128 + z * (269 + z * (182 + z * 123))))))))))))))))))))))))))))))))))))))


def pow16_17 {R : Type*} [CommRing R] (z : R) : R := (82 + z * (32 + z * (25 + z * (28 + z * (120 + z * (29 + z * (50 + z * (26 + z * (20 + z * (87 + z * (93 + z * (12 + z * (121 + z * (100 + z * (112 + z * (102 + z * (104 + z * (109 + z * (67 + z * 120)))))))))))))))))))

def pow16_17_q {R : Type*} [CommRing R] (z : R) : R := (135 + z * (93 + z * (23 + z * (99 + z * (98 + z * (14 + z * (117 + z * (137 + z * (30 + z * (31 + z * (55 + z * (26 + z * (22 + z * (40 + z * (95 + z * (29 + z * (48 + z * (56 + z * 72))))))))))))))))))

def pow16_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-91) + z * ((-73) + z * ((-25) + z * ((-88) + z * ((-111) + z * ((-46) + z * ((-45) + z * ((-108) + z * ((-20) + z * ((-19) + z * ((-166) + z * ((-9) + z * (67 + z * ((-22) + z * (17 + z * (144 + z * ((-97) + z * (19 + z * (124 + z * ((-28) + z * (134 + z * (103 + z * (48 + z * ((-37) + z * (137 + z * ((-11) + z * (44 + z * (4 + z * (69 + z * (36 + z * (35 + z * (65 + z * (25 + z * ((-12) + z * ((-10) + z * (2 + z * ((-55) + z * ((-43) + z * 2))))))))))))))))))))))))))))))))))))))


def pow16_34 {R : Type*} [CommRing R] (z : R) : R := (59 + z * (104 + z * (26 + z * (41 + z * (81 + z * (85 + z * (86 + z * (22 + z * (7 + z * (60 + z * (45 + z * (1 + z * (67 + z * (119 + z * (46 + z * (100 + z * (97 + z * (36 + z * (54 + z * 46)))))))))))))))))))

def pow16_34_q {R : Type*} [CommRing R] (z : R) : R := (37 + z * (6 + z * (118 + z * (28 + z * (90 + z * (58 + z * (135 + z * (4 + z * (78 + z * (135 + z * (55 + z * (30 + z * (138 + z * (108 + z * (3 + z * (128 + z * (50 + z * (35 + z * 83))))))))))))))))))

def pow16_34_mul_t {R : Type*} [CommRing R] (z : R) : R := (20 + z * (0 + z * ((-91) + z * ((-121) + z * ((-75) + z * ((-177) + z * ((-247) + z * ((-227) + z * ((-214) + z * ((-294) + z * ((-252) + z * ((-349) + z * ((-370) + z * ((-295) + z * ((-190) + z * ((-410) + z * ((-225) + z * ((-173) + z * ((-236) + z * ((-138) + z * ((-142) + z * ((-146) + z * ((-137) + z * (107 + z * ((-33) + z * ((-75) + z * (184 + z * (141 + z * (105 + z * (383 + z * (249 + z * (196 + z * (317 + z * (275 + z * (138 + z * (212 + z * (127 + z * (39 + z * 103))))))))))))))))))))))))))))))))))))))


def pow16_68 {R : Type*} [CommRing R] (z : R) : R := (110 + z * (8 + z * (110 + z * (107 + z * (80 + z * (3 + z * (78 + z * (91 + z * (63 + z * (33 + z * (65 + z * (101 + z * (61 + z * (94 + z * (69 + z * (8 + z * (37 + z * (51 + z * (28 + z * 59)))))))))))))))))))

def pow16_68_q {R : Type*} [CommRing R] (z : R) : R := (93 + z * (112 + z * (122 + z * (107 + z * (137 + z * (80 + z * (117 + z * (18 + z * (13 + z * (68 + z * (49 + z * (10 + z * (110 + z * (80 + z * (91 + z * (69 + z * (27 + z * (27 + z * 31))))))))))))))))))

def pow16_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-46) + z * ((-78) + z * ((-175) + z * ((-304) + z * ((-352) + z * ((-300) + z * ((-303) + z * ((-303) + z * ((-335) + z * ((-322) + z * ((-308) + z * ((-347) + z * ((-438) + z * ((-416) + z * ((-406) + z * ((-457) + z * ((-398) + z * ((-294) + z * ((-270) + z * ((-286) + z * ((-270) + z * ((-244) + z * ((-263) + z * ((-216) + z * ((-184) + z * ((-138) + z * ((-38) + z * ((-84) + z * ((-32) + z * (52 + z * ((-4) + z * (25 + z * (40 + z * ((-19) + z * (41 + z * (47 + z * ((-3) + z * (7 + z * 15))))))))))))))))))))))))))))))))))))))


def pow16_69 {R : Type*} [CommRing R] (z : R) : R := (7 + z * (65 + z * (56 + z * (34 + z * (42 + z * (7 + z * (8 + z * (48 + z * (53 + z * (15 + z * (6 + z * (80 + z * (73 + z * (108 + z * (40 + z * (77 + z * (104 + z * (118 + z * (45 + z * 51)))))))))))))))))))

def pow16_69_q {R : Type*} [CommRing R] (z : R) : R := (45 + z * (1 + z * (43 + z * (53 + z * (125 + z * (15 + z * (14 + z * (82 + z * (125 + z * (37 + z * (71 + z * (101 + z * (101 + z * (43 + z * (98 + z * (38 + z * (20 + z * (88 + z * 34))))))))))))))))))

def pow16_69_mul_t {R : Type*} [CommRing R] (z : R) : R := (72 + z * (58 + z * (78 + z * (92 + z * (52 + z * (6 + z * (30 + z * (135 + z * (54 + z * (68 + z * ((-37) + z * (34 + z * ((-64) + z * (98 + z * ((-11) + z * ((-10) + z * (35 + z * (51 + z * (52 + z * (93 + z * (43 + z * ((-40) + z * ((-55) + z * ((-46) + z * (85 + z * (33 + z * ((-99) + z * ((-123) + z * (50 + z * (42 + z * ((-51) + z * ((-22) + z * ((-17) + z * ((-77) + z * (41 + z * (26 + z * ((-34) + z * (7 + z * 4))))))))))))))))))))))))))))))))))))))


def pow16_138 {R : Type*} [CommRing R] (z : R) : R := (81 + z * (49 + z * (119 + z * (63 + z * (52 + z * (14 + z * (28 + z * (121 + z * (33 + z * (114 + z * (19 + z * (31 + z * (78 + z * (80 + z * (106 + z * (130 + z * (128 + z * (25 + z * (52 + z * 45)))))))))))))))))))

def pow16_138_q {R : Type*} [CommRing R] (z : R) : R := (50 + z * (11 + z * (104 + z * (128 + z * (128 + z * (15 + z * (109 + z * (116 + z * (113 + z * (17 + z * (113 + z * (136 + z * (96 + z * (89 + z * (53 + z * (84 + z * (129 + z * (119 + z * 99))))))))))))))))))

def pow16_138_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-38) + z * ((-46) + z * ((-98) + z * ((-190) + z * ((-294) + z * ((-294) + z * ((-385) + z * ((-444) + z * ((-436) + z * ((-424) + z * ((-548) + z * ((-626) + z * ((-646) + z * ((-679) + z * ((-585) + z * ((-603) + z * ((-734) + z * ((-746) + z * ((-725) + z * ((-708) + z * ((-701) + z * ((-719) + z * ((-668) + z * ((-507) + z * ((-360) + z * ((-451) + z * ((-492) + z * ((-308) + z * ((-101) + z * ((-133) + z * ((-92) + z * ((-143) + z * ((-33) + z * ((-18) + z * ((-31) + z * ((-54) + z * ((-82) + z * ((-59) + z * 18))))))))))))))))))))))))))))))))))))))


def pow16_139 {R : Type*} [CommRing R] (z : R) : R := (50 + z * (86 + z * (86 + z * (57 + z * (99 + z * (120 + z * (3 + z * (103 + z * (47 + z * (22 + z * (98 + z * (68 + z * (40 + z * (37 + z * (113 + z * (58 + z * (118 + z * (42 + z * (12 + z * 122)))))))))))))))))))

def pow16_139_q {R : Type*} [CommRing R] (z : R) : R := (42 + z * (50 + z * (69 + z * (89 + z * (22 + z * (67 + z * (116 + z * (1 + z * (69 + z * (57 + z * (98 + z * (113 + z * (126 + z * (63 + z * (10 + z * (122 + z * (94 + z * (72 + z * 33))))))))))))))))))

def pow16_139_mul_t {R : Type*} [CommRing R] (z : R) : R := (46 + z * (39 + z * (50 + z * ((-24) + z * ((-40) + z * ((-69) + z * ((-101) + z * (81 + z * (21 + z * (21 + z * ((-133) + z * ((-112) + z * ((-187) + z * ((-75) + z * (12 + z * ((-90) + z * ((-8) + z * (18 + z * ((-15) + z * ((-101) + z * (104 + z * ((-113) + z * ((-20) + z * (129 + z * ((-69) + z * ((-19) + z * (40 + z * (32 + z * ((-22) + z * (89 + z * (33 + z * (4 + z * (174 + z * (94 + z * ((-32) + z * ((-32) + z * ((-18) + z * (1 + z * 3))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Powers09
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139
def pow17_2 {R : Type*} [CommRing R] (z : R) : R := (1 + z * (110 + z * (129 + z * (19 + z * (43 + z * (94 + z * (94 + z * (24 + z * (8 + z * (41 + z * (86 + z * (62 + z * (67 + z * (116 + z * (119 + z * (81 + z * (80 + z * (50 + z * (11 + z * 130)))))))))))))))))))

def pow17_2_q {R : Type*} [CommRing R] (z : R) : R := (135 + z * (63 + z * (84 + z * (38 + z * (106 + z * (96 + z * (75 + z * (99 + z * (61 + z * (66 + z * (126 + z * (72 + z * (60 + z * (55 + z * (29 + z * (105 + z * (136 + z * (130 + z * 11))))))))))))))))))

def pow17_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-84) + z * ((-105) + z * ((-126) + z * ((-140) + z * ((-160) + z * ((-91) + z * ((-108) + z * ((-172) + z * ((-192) + z * ((-207) + z * ((-333) + z * ((-272) + z * ((-166) + z * ((-410) + z * ((-272) + z * ((-204) + z * ((-332) + z * ((-318) + z * ((-348) + z * ((-364) + z * ((-309) + z * ((-7) + z * ((-190) + z * ((-190) + z * ((-76) + z * ((-380) + z * ((-145) + z * ((-92) + z * ((-135) + z * ((-74) + z * ((-19) + z * ((-92) + z * ((-54) + z * (60 + z * ((-71) + z * ((-7) + z * ((-54) + z * (10 + z * 107))))))))))))))))))))))))))))))))))))))


def pow17_4 {R : Type*} [CommRing R] (z : R) : R := (89 + z * (44 + z * (66 + z * (56 + z * (10 + z * (46 + z * (99 + z * (58 + z * (92 + z * (46 + z * (53 + z * (95 + z * (116 + z * (26 + z * (84 + z * (78 + z * (37 + z * (63 + z * (7 + z * 59)))))))))))))))))))

def pow17_4_q {R : Type*} [CommRing R] (z : R) : R := (68 + z * (108 + z * (137 + z * (65 + z * (130 + z * (84 + z * (78 + z * (28 + z * (55 + z * (137 + z * (97 + z * (25 + z * (117 + z * (37 + z * (135 + z * (112 + z * (111 + z * (137 + z * 81))))))))))))))))))

def pow17_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-52) + z * ((-140) + z * ((-171) + z * ((-127) + z * ((-284) + z * ((-367) + z * ((-243) + z * ((-121) + z * ((-232) + z * ((-432) + z * ((-464) + z * ((-344) + z * ((-386) + z * ((-450) + z * ((-386) + z * ((-265) + z * ((-335) + z * ((-482) + z * ((-534) + z * ((-561) + z * ((-341) + z * ((-226) + z * ((-408) + z * ((-295) + z * ((-216) + z * ((-204) + z * ((-118) + z * ((-213) + z * ((-168) + z * (63 + z * ((-94) + z * ((-110) + z * ((-8) + z * ((-80) + z * ((-71) + z * ((-46) + z * ((-92) + z * ((-55) + z * 121))))))))))))))))))))))))))))))))))))))


def pow17_8 {R : Type*} [CommRing R] (z : R) : R := (29 + z * (47 + z * (8 + z * (123 + z * (82 + z * (71 + z * (104 + z * (28 + z * (133 + z * (66 + z * (8 + z * (100 + z * (19 + z * (136 + z * (71 + z * (44 + z * (27 + z * (118 + z * (33 + z * 28)))))))))))))))))))

def pow17_8_q {R : Type*} [CommRing R] (z : R) : R := (5 + z * (22 + z * (108 + z * (7 + z * (33 + z * (60 + z * (122 + z * (116 + z * (63 + z * (99 + z * (27 + z * (95 + z * (52 + z * (115 + z * (5 + z * (60 + z * (3 + z * (58 + z * 6))))))))))))))))))

def pow17_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (53 + z * (35 + z * ((-7) + z * ((-12) + z * ((-74) + z * ((-84) + z * ((-87) + z * ((-140) + z * ((-111) + z * ((-228) + z * ((-227) + z * ((-184) + z * ((-119) + z * ((-162) + z * ((-78) + z * ((-243) + z * ((-196) + z * ((-79) + z * ((-104) + z * ((-49) + z * ((-116) + z * ((-188) + z * ((-73) + z * ((-16) + z * ((-93) + z * ((-97) + z * ((-57) + z * ((-31) + z * ((-34) + z * (30 + z * ((-21) + z * (4 + z * ((-41) + z * (11 + z * (36 + z * ((-8) + z * ((-4) + z * (0 + z * 25))))))))))))))))))))))))))))))))))))))


def pow17_16 {R : Type*} [CommRing R] (z : R) : R := (54 + z * (103 + z * (91 + z * (7 + z * (111 + z * (100 + z * (0 + z * (17 + z * (119 + z * (89 + z * (22 + z * (71 + z * (107 + z * (107 + z * (111 + z * (6 + z * (41 + z * (69 + z * (91 + z * 16)))))))))))))))))))

def pow17_16_q {R : Type*} [CommRing R] (z : R) : R := (30 + z * (100 + z * (107 + z * (19 + z * (124 + z * (47 + z * (121 + z * (108 + z * (126 + z * (105 + z * (126 + z * (138 + z * (3 + z * (2 + z * (130 + z * (6 + z * (109 + z * (47 + z * 89))))))))))))))))))

def pow17_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-17) + z * ((-83) + z * ((-177) + z * ((-170) + z * ((-208) + z * ((-252) + z * ((-177) + z * ((-211) + z * ((-296) + z * ((-236) + z * ((-469) + z * ((-413) + z * ((-300) + z * ((-350) + z * ((-252) + z * ((-385) + z * ((-246) + z * ((-310) + z * ((-437) + z * ((-312) + z * ((-410) + z * ((-201) + z * ((-88) + z * ((-287) + z * ((-313) + z * ((-173) + z * ((-214) + z * ((-293) + z * ((-48) + z * ((-258) + z * ((-32) + z * (27 + z * ((-87) + z * ((-125) + z * ((-30) + z * ((-68) + z * ((-54) + z * ((-69) + z * 5))))))))))))))))))))))))))))))))))))))


def pow17_17 {R : Type*} [CommRing R] (z : R) : R := (127 + z * (70 + z * (108 + z * (19 + z * (94 + z * (15 + z * (22 + z * (27 + z * (99 + z * (84 + z * (135 + z * (6 + z * (88 + z * (125 + z * (112 + z * (80 + z * (21 + z * (63 + z * (5 + z * 37)))))))))))))))))))

def pow17_17_q {R : Type*} [CommRing R] (z : R) : R := (2 + z * (130 + z * (36 + z * (28 + z * (67 + z * (129 + z * (119 + z * (126 + z * (63 + z * (97 + z * (13 + z * (89 + z * (33 + z * (113 + z * (75 + z * (23 + z * (117 + z * (101 + z * 6))))))))))))))))))

def pow17_17_mul_t {R : Type*} [CommRing R] (z : R) : R := (17 + z * ((-30) + z * ((-14) + z * ((-27) + z * ((-52) + z * ((-52) + z * ((-70) + z * ((-219) + z * ((-259) + z * ((-187) + z * ((-254) + z * ((-261) + z * ((-59) + z * ((-142) + z * ((-278) + z * ((-165) + z * ((-202) + z * ((-351) + z * ((-105) + z * ((-161) + z * ((-293) + z * ((-127) + z * ((-174) + z * ((-135) + z * ((-149) + z * ((-192) + z * ((-245) + z * ((-48) + z * (132 + z * ((-79) + z * ((-42) + z * ((-12) + z * ((-77) + z * (45 + z * (1 + z * ((-99) + z * ((-25) + z * (75 + z * 14))))))))))))))))))))))))))))))))))))))


def pow17_34 {R : Type*} [CommRing R] (z : R) : R := (7 + z * (80 + z * (23 + z * (132 + z * (110 + z * (4 + z * (72 + z * (130 + z * (87 + z * (91 + z * (58 + z * (68 + z * (30 + z * (114 + z * (21 + z * (16 + z * (34 + z * (100 + z * (103 + z * 59)))))))))))))))))))

def pow17_34_q {R : Type*} [CommRing R] (z : R) : R := (90 + z * (64 + z * (15 + z * (113 + z * (94 + z * (62 + z * (4 + z * (127 + z * (27 + z * (54 + z * (0 + z * (25 + z * (26 + z * (20 + z * (66 + z * (19 + z * (18 + z * (0 + z * 118))))))))))))))))))

def pow17_34_mul_t {R : Type*} [CommRing R] (z : R) : R := (48 + z * (0 + z * (84 + z * ((-99) + z * ((-41) + z * ((-171) + z * ((-108) + z * ((-290) + z * ((-84) + z * ((-99) + z * (63 + z * ((-81) + z * (154 + z * (20 + z * (222 + z * (129 + z * (34 + z * (133 + z * (24 + z * ((-41) + z * ((-68) + z * (52 + z * (36 + z * (156 + z * (161 + z * (156 + z * (113 + z * (203 + z * (71 + z * (190 + z * (57 + z * (5 + z * (19 + z * ((-66) + z * ((-57) + z * ((-1) + z * ((-53) + z * ((-106) + z * 9))))))))))))))))))))))))))))))))))))))


def pow17_68 {R : Type*} [CommRing R] (z : R) : R := (99 + z * (47 + z * (67 + z * (45 + z * (15 + z * (1 + z * (76 + z * (18 + z * (88 + z * (40 + z * (18 + z * (35 + z * (17 + z * (107 + z * (41 + z * (87 + z * (29 + z * (35 + z * (36 + z * 19)))))))))))))))))))

def pow17_68_q {R : Type*} [CommRing R] (z : R) : R := (26 + z * (74 + z * (55 + z * (127 + z * (24 + z * (11 + z * (1 + z * (113 + z * (37 + z * (110 + z * (83 + z * (73 + z * (53 + z * (131 + z * (123 + z * (51 + z * (120 + z * (127 + z * 6))))))))))))))))))

def pow17_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * ((-71) + z * ((-82) + z * ((-196) + z * ((-103) + z * ((-91) + z * ((-54) + z * (31 + z * (6 + z * ((-77) + z * ((-2) + z * ((-86) + z * ((-96) + z * ((-171) + z * ((-73) + z * ((-178) + z * ((-280) + z * ((-364) + z * ((-339) + z * ((-262) + z * ((-67) + z * ((-29) + z * ((-129) + z * ((-238) + z * ((-65) + z * ((-89) + z * ((-146) + z * ((-182) + z * ((-148) + z * ((-231) + z * ((-134) + z * ((-91) + z * ((-236) + z * ((-171) + z * ((-5) + z * ((-27) + z * (39 + z * (81 + z * 25))))))))))))))))))))))))))))))))))))))


def pow17_69 {R : Type*} [CommRing R] (z : R) : R := (50 + z * (118 + z * (94 + z * (26 + z * (88 + z * (112 + z * (127 + z * (30 + z * (28 + z * (31 + z * (74 + z * (41 + z * (48 + z * (88 + z * (118 + z * (121 + z * (137 + z * (74 + z * (114 + z * 20)))))))))))))))))))

def pow17_69_q {R : Type*} [CommRing R] (z : R) : R := (93 + z * (34 + z * (52 + z * (18 + z * (12 + z * (89 + z * (8 + z * (5 + z * (23 + z * (109 + z * (76 + z * (11 + z * (0 + z * (56 + z * (79 + z * (114 + z * (4 + z * (94 + z * 94))))))))))))))))))

def pow17_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-35) + z * ((-30) + z * ((-39) + z * ((-51) + z * ((-13) + z * ((-15) + z * ((-50) + z * (29 + z * ((-8) + z * ((-115) + z * ((-94) + z * ((-66) + z * ((-110) + z * ((-62) + z * ((-64) + z * ((-142) + z * ((-37) + z * ((-110) + z * ((-272) + z * ((-223) + z * ((-95) + z * ((-167) + z * ((-38) + z * ((-142) + z * ((-212) + z * ((-82) + z * ((-112) + z * ((-112) + z * ((-229) + z * ((-20) + z * ((-74) + z * ((-100) + z * ((-15) + z * ((-183) + z * ((-59) + z * ((-18) + z * ((-116) + z * ((-54) + z * 16))))))))))))))))))))))))))))))))))))))


def pow17_138 {R : Type*} [CommRing R] (z : R) : R := (118 + z * (118 + z * (66 + z * (127 + z * (4 + z * (82 + z * (46 + z * (125 + z * (107 + z * (49 + z * (91 + z * (27 + z * (100 + z * (24 + z * (12 + z * (91 + z * (14 + z * (17 + z * (138 + z * 92)))))))))))))))))))

def pow17_138_q {R : Type*} [CommRing R] (z : R) : R := (118 + z * (88 + z * (41 + z * (85 + z * (31 + z * (105 + z * (62 + z * (71 + z * (54 + z * (110 + z * (119 + z * (7 + z * (126 + z * (135 + z * (93 + z * (67 + z * (46 + z * (64 + z * 122))))))))))))))))))

def pow17_138_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-72) + z * ((-86) + z * ((-47) + z * ((-114) + z * ((-140) + z * ((-62) + z * (58 + z * (14 + z * ((-98) + z * ((-248) + z * ((-249) + z * ((-133) + z * ((-220) + z * ((-436) + z * ((-293) + z * ((-193) + z * ((-165) + z * ((-29) + z * ((-75) + z * ((-81) + z * (53 + z * ((-50) + z * ((-90) + z * ((-94) + z * ((-51) + z * ((-225) + z * ((-152) + z * ((-103) + z * ((-105) + z * (117 + z * (193 + z * (81 + z * (159 + z * (111 + z * (101 + z * (71 + z * ((-34) + z * ((-80) + z * 2))))))))))))))))))))))))))))))))))))))


def pow17_139 {R : Type*} [CommRing R] (z : R) : R := (63 + z * (5 + z * (33 + z * (67 + z * (66 + z * (39 + z * (107 + z * (38 + z * (87 + z * (81 + z * (59 + z * (19 + z * (136 + z * (42 + z * (111 + z * (137 + z * (13 + z * (98 + z * (16 + z * 127)))))))))))))))))))

def pow17_139_q {R : Type*} [CommRing R] (z : R) : R := (45 + z * (78 + z * (63 + z * (48 + z * (30 + z * (122 + z * (109 + z * (6 + z * (28 + z * (100 + z * (33 + z * (95 + z * (75 + z * (108 + z * (107 + z * (89 + z * (78 + z * (41 + z * 104))))))))))))))))))

def pow17_139_mul_t {R : Type*} [CommRing R] (z : R) : R := (8 + z * (17 + z * (13 + z * (3 + z * (22 + z * (27 + z * ((-78) + z * (16 + z * (50 + z * ((-96) + z * (53 + z * ((-13) + z * ((-8) + z * ((-126) + z * ((-182) + z * ((-237) + z * ((-233) + z * ((-51) + z * ((-341) + z * ((-129) + z * ((-106) + z * ((-249) + z * ((-28) + z * ((-48) + z * ((-239) + z * ((-204) + z * (22 + z * ((-229) + z * ((-194) + z * ((-50) + z * ((-197) + z * ((-134) + z * ((-108) + z * ((-96) + z * (15 + z * (31 + z * ((-60) + z * (33 + z * 80))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Result
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139
def g1 {R : Type*} [CommRing R] (z : R) : R := (18 + z * 1)

def a1 {R : Type*} [CommRing R] (z : R) : R := (68 + z * (58 + z * (93 + z * (71 + z * (14 + z * (127 + z * (39 + z * (101 + z * (100 + z * (125 + z * (16 + z * (96 + z * (40 + z * (75 + z * (120 + z * (31 + z * (5 + z * 106)))))))))))))))))

def b1 {R : Type*} [CommRing R] (z : R) : R := (45 + z * (129 + z * (121 + z * (47 + z * (93 + z * (123 + z * (131 + z * (0 + z * (97 + z * (133 + z * (104 + z * (137 + z * (136 + z * (105 + z * (66 + z * (113 + z * (29 + z * (130 + z * 32))))))))))))))))))

def bezout1_t {R : Type*} [CommRing R] (z : R) : R := (93 + z * (264 + z * (441 + z * (515 + z * (583 + z * (749 + z * (815 + z * (763 + z * (912 + z * (1182 + z * (1231 + z * (1305 + z * (1464 + z * (1514 + z * (1464 + z * (1619 + z * (1588 + z * (1667 + z * (1671 + z * (1636 + z * (1563 + z * (1587 + z * (1268 + z * (1285 + z * (1227 + z * (995 + z * (937 + z * (1009 + z * (831 + z * (651 + z * (714 + z * (435 + z * (512 + z * (386 + z * (257 + z * (202 + z * (233 + z * 30)))))))))))))))))))))))))))))))))))))


def div1_f {R : Type*} [CommRing R] (z : R) : R := (29 + z * (121 + z * (62 + z * (112 + z * (23 + z * (86 + z * (106 + z * (37 + z * (10 + z * (91 + z * (72 + z * (129 + z * (126 + z * (62 + z * (77 + z * (47 + z * (27 + z * (68 + z * (110 + z * 1)))))))))))))))))))

def factor1_f_t {R : Type*} [CommRing R] (z : R) : R := ((-3) + z * ((-15) + z * ((-8) + z * ((-14) + z * ((-3) + z * ((-11) + z * ((-14) + z * ((-5) + z * ((-1) + z * ((-11) + z * ((-9) + z * ((-17) + z * ((-17) + z * ((-8) + z * ((-10) + z * ((-6) + z * ((-3) + z * ((-9) + z * ((-14) + z * (0 + z * 0))))))))))))))))))))


def div1_u1 {R : Type*} [CommRing R] (z : R) : R := (123 + z * (116 + z * (99 + z * (22 + z * (67 + z * (92 + z * (58 + z * (47 + z * (103 + z * (21 + z * (49 + z * (105 + z * (42 + z * (100 + z * (80 + z * (138 + z * (70 + z * (10 + z * 127))))))))))))))))))

def factor1_u1_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * ((-15) + z * ((-13) + z * ((-3) + z * ((-8) + z * ((-12) + z * ((-8) + z * ((-6) + z * ((-13) + z * ((-3) + z * ((-6) + z * ((-13) + z * ((-6) + z * ((-13) + z * ((-11) + z * ((-18) + z * ((-10) + z * ((-1) + z * ((-16) + z * 0)))))))))))))))))))


def df {R : Type*} [CommRing R] (z : R) : R := (122 + z * (111 + z * (118 + z * (19 + z * (71 + z * (10 + z * (122 + z * (68 + z * (98 + z * (109 + z * (63 + z * (130 + z * (22 + z * (117 + z * (84 + z * (49 + z * (0 + z * (29 + z * (69 + z * 20)))))))))))))))))))

def da {R : Type*} [CommRing R] (z : R) : R := (39 + z * (17 + z * (73 + z * (16 + z * (132 + z * (18 + z * (8 + z * (1 + z * (121 + z * (9 + z * (71 + z * (47 + z * (16 + z * (84 + z * (111 + z * (31 + z * (68 + z * (50 + z * 107))))))))))))))))))

def db {R : Type*} [CommRing R] (z : R) : R := (110 + z * (32 + z * (66 + z * (134 + z * (55 + z * (51 + z * (89 + z * (93 + z * (107 + z * (120 + z * (114 + z * (89 + z * (65 + z * (79 + z * (127 + z * (10 + z * (116 + z * (55 + z * (55 + z * 85)))))))))))))))))))

end DimensionTen.Mod139

section
noncomputable section
open Polynomial
namespace DimensionTen.Mod139

def derivative_extra {R : Type*} [CommRing R] (z : R) : R := (0 + z * (1 + z * (2 + z * (3 + z * (1 + z * (2 + z * (3 + z * (4 + z * (7 + z * (9 + z * (2 + z * (2 + z * (12 + z * (5 + z * (9 + z * (13 + z * (0 + z * (13 + z * (17 + z * 0)))))))))))))))))))

end DimensionTen.Mod139

end
end

end

end OAI
end


