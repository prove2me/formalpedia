-- Prove2me | Definitions.Def_OAIQ033D007
-- name    : OAIQ033D007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T01:47:00.405862+00:00
-- url     : https://prove2.me/theorems/bb20ad1c-8275-40b7-95eb-cc8cbae95249
-- title:
--   Definitions bundle OAIQ033D007 of the split of OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DimensionTen.main_pair`, carved from OpenAI's openai/math development (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 164 declarations of OpenAI's Lean: 163 definitions and 1 theorem. The definitions and types are `OAI.DimensionTen.Mod139.pow13_8`, `OAI.DimensionTen.Mod139.pow13_8_mul_t`, `OAI.DimensionTen.Mod139.pow13_8_q`, `OAI.DimensionTen.Mod139.pow14_138`, `OAI.DimensionTen.Mod139.pow14_138_mul_t`, `OAI.DimensionTen.Mod139.pow14_138_q`, `OAI.DimensionTen.Mod139.pow14_139`, `OAI.DimensionTen.Mod139.pow14_139_mul_t`, `OAI.DimensionTen.Mod139.pow14_139_q`, `OAI.DimensionTen.Mod139.pow14_16`, `OAI.DimensionTen.Mod139.pow14_16_mul_t`, `OAI.DimensionTen.Mod139.pow14_16_q`, `OAI.DimensionTen.Mod139.pow14_17`, `OAI.DimensionTen.Mod139.pow14_17_mul_t`, `OAI.DimensionTen.Mod139.pow14_17_q`, `OAI.DimensionTen.Mod139.pow14_2`, `OAI.DimensionTen.Mod139.pow14_2_mul_t`, `OAI.DimensionTen.Mod139.pow14_2_q`, `OAI.DimensionTen.Mod139.pow14_34`, `OAI.DimensionTen.Mod139.pow14_34_mul_t`, `OAI.DimensionTen.Mod139.pow14_34_q`, `OAI.DimensionTen.Mod139.pow14_4`, `OAI.DimensionTen.Mod139.pow14_4_mul_t`, `OAI.DimensionTen.Mod139.pow14_4_q`, `OAI.DimensionTen.Mod139.pow14_68`, `OAI.DimensionTen.Mod139.pow14_68_mul_t`, `OAI.DimensionTen.Mod139.pow14_68_q`, `OAI.DimensionTen.Mod139.pow14_69`, `OAI.DimensionTen.Mod139.pow14_69_mul_t`, `OAI.DimensionTen.Mod139.pow14_69_q`, `OAI.DimensionTen.Mod139.pow14_8`, `OAI.DimensionTen.Mod139.pow14_8_mul_t`, `OAI.DimensionTen.Mod139.pow14_8_q`, `OAI.DimensionTen.Mod139.pow15_138`, `OAI.DimensionTen.Mod139.pow15_138_mul_t`, `OAI.DimensionTen.Mod139.pow15_138_q`, `OAI.DimensionTen.Mod139.pow15_139`, `OAI.DimensionTen.Mod139.pow15_139_mul_t`, `OAI.DimensionTen.Mod139.pow15_139_q`, `OAI.DimensionTen.Mod139.pow15_16` and 123 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Quantum/DimensionTen, in whole or in part: [`Quantum_DimensionTen_Mod139Model`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod139Model.lean), [`Quantum_DimensionTen_Mod139Powers01`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod139Powers01.lean), [`Quantum_DimensionTen_Mod139Powers07`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod139Powers07.lean), [`Quantum_DimensionTen_Mod139Powers08`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod139Powers08.lean), [`Quantum_DimensionTen_Mod139Powers09`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod139Powers09.lean), [`Quantum_DimensionTen_Mod139Powers10`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod139Powers10.lean), [`Quantum_PPTSquare_GaloisAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/PPTSquare/GaloisAction.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ033D013`; the statements `OAI_DimensionTen_Mod131_iterate12` and `OAI_DimensionTen_Mod139_iterate11`; the proofs of `OAI_DimensionTen_Mod131_iterate12`, `OAI_DimensionTen_Mod139_iterate11` and `OAI_DimensionTen_exists_nineteen_cycle_of_mod139`.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Quantum/DimensionTen at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139

def u0 {R : Type*} [CommRing R] (z : R) : R := (0 + z * 1)

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139


def pow1_16 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 1))))))))))))))))

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139


def pow13_8 {R : Type*} [CommRing R] (z : R) : R := (55 + z * (34 + z * (116 + z * (112 + z * (84 + z * (73 + z * (123 + z * (87 + z * (29 + z * (66 + z * (56 + z * (123 + z * (128 + z * (11 + z * (83 + z * (73 + z * (110 + z * (88 + z * (125 + z * 50)))))))))))))))))))

def pow13_8_q {R : Type*} [CommRing R] (z : R) : R := (99 + z * (77 + z * (26 + z * (84 + z * (100 + z * (124 + z * (95 + z * (48 + z * (63 + z * (107 + z * (57 + z * (55 + z * (58 + z * (22 + z * (23 + z * (58 + z * (60 + z * (5 + z * 67))))))))))))))))))

def pow13_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-75) + z * ((-143) + z * ((-169) + z * ((-243) + z * ((-305) + z * ((-358) + z * ((-390) + z * ((-448) + z * ((-407) + z * ((-492) + z * ((-493) + z * ((-458) + z * ((-415) + z * ((-514) + z * ((-361) + z * ((-357) + z * ((-425) + z * ((-288) + z * ((-308) + z * ((-409) + z * ((-198) + z * (9 + z * ((-173) + z * ((-40) + z * (106 + z * ((-105) + z * (190 + z * (277 + z * ((-104) + z * (161 + z * (287 + z * ((-113) + z * (240 + z * (139 + z * ((-138) + z * (166 + z * ((-12) + z * ((-55) + z * 98))))))))))))))))))))))))))))))))))))))


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
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers08
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
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers09
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


def pow18_2 {R : Type*} [CommRing R] (z : R) : R := (93 + z * (115 + z * (7 + z * (121 + z * (89 + z * (36 + z * (73 + z * (35 + z * (138 + z * (122 + z * (55 + z * (40 + z * (90 + z * (72 + z * (52 + z * (5 + z * (116 + z * (97 + z * (6 + z * 104)))))))))))))))))))

def pow18_2_q {R : Type*} [CommRing R] (z : R) : R := (25 + z * (95 + z * (126 + z * (88 + z * (88 + z * (14 + z * (50 + z * (48 + z * (36 + z * (60 + z * (87 + z * (98 + z * (69 + z * (131 + z * (71 + z * (16 + z * (30 + z * (88 + z * 5))))))))))))))))))

def pow18_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (9 + z * ((-90) + z * ((-171) + z * ((-224) + z * ((-295) + z * ((-297) + z * ((-186) + z * ((-206) + z * ((-133) + z * ((-143) + z * ((-246) + z * ((-361) + z * ((-200) + z * ((-379) + z * ((-293) + z * ((-193) + z * ((-280) + z * ((-245) + z * ((-55) + z * ((-114) + z * ((-160) + z * (6 + z * ((-9) + z * (114 + z * (121 + z * (137 + z * ((-4) + z * (174 + z * (48 + z * (166 + z * ((-26) + z * (206 + z * (40 + z * (98 + z * (281 + z * ((-46) + z * (96 + z * (24 + z * 116))))))))))))))))))))))))))))))))))))))


def pow18_4 {R : Type*} [CommRing R] (z : R) : R := (42 + z * (42 + z * (88 + z * (21 + z * (89 + z * (91 + z * (123 + z * (114 + z * (28 + z * (81 + z * (87 + z * (117 + z * (81 + z * (89 + z * (43 + z * (82 + z * (9 + z * (21 + z * (17 + z * 60)))))))))))))))))))

def pow18_4_q {R : Type*} [CommRing R] (z : R) : R := (78 + z * (69 + z * (32 + z * (118 + z * (90 + z * (9 + z * (119 + z * (118 + z * (90 + z * (27 + z * (86 + z * (124 + z * (91 + z * (52 + z * (133 + z * (116 + z * (86 + z * (128 + z * 113))))))))))))))))))

def pow18_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (3 + z * (33 + z * ((-51) + z * ((-80) + z * ((-8) + z * ((-93) + z * ((-93) + z * ((-131) + z * ((-117) + z * (51 + z * ((-175) + z * ((-160) + z * ((-13) + z * ((-153) + z * ((-257) + z * ((-321) + z * ((-328) + z * ((-146) + z * ((-402) + z * ((-417) + z * ((-144) + z * ((-366) + z * ((-215) + z * ((-238) + z * ((-273) + z * ((-139) + z * ((-295) + z * ((-260) + z * ((-104) + z * ((-149) + z * ((-295) + z * ((-212) + z * ((-131) + z * ((-147) + z * ((-180) + z * (8 + z * ((-56) + z * ((-96) + z * 77))))))))))))))))))))))))))))))))))))))


def pow18_8 {R : Type*} [CommRing R] (z : R) : R := (16 + z * (85 + z * (18 + z * (78 + z * (88 + z * (114 + z * (67 + z * (76 + z * (22 + z * (10 + z * (10 + z * (68 + z * (1 + z * (34 + z * (6 + z * (108 + z * (42 + z * (60 + z * (69 + z * 49)))))))))))))))))))

def pow18_8_q {R : Type*} [CommRing R] (z : R) : R := (14 + z * (43 + z * (76 + z * (26 + z * (14 + z * (1 + z * (69 + z * (61 + z * (108 + z * (39 + z * (19 + z * (29 + z * (79 + z * (10 + z * (11 + z * (1 + z * (102 + z * (79 + z * 125))))))))))))))))))

def pow18_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (2 + z * ((-20) + z * ((-42) + z * ((-73) + z * ((-32) + z * ((-12) + z * (77 + z * (98 + z * (51 + z * (27 + z * (18 + z * (163 + z * (164 + z * (297 + z * (241 + z * (267 + z * (210 + z * (226 + z * (59 + z * (97 + z * (35 + z * (18 + z * (65 + z * (148 + z * (114 + z * ((-14) + z * ((-67) + z * ((-189) + z * ((-38) + z * ((-7) + z * ((-40) + z * ((-181) + z * ((-93) + z * ((-97) + z * ((-104) + z * ((-139) + z * ((-145) + z * ((-101) + z * 25))))))))))))))))))))))))))))))))))))))


def pow18_16 {R : Type*} [CommRing R] (z : R) : R := (66 + z * (55 + z * (17 + z * (131 + z * (111 + z * (21 + z * (55 + z * (69 + z * (0 + z * (77 + z * (99 + z * (19 + z * (115 + z * (56 + z * (129 + z * (122 + z * (25 + z * (82 + z * (75 + z * 41)))))))))))))))))))

def pow18_16_q {R : Type*} [CommRing R] (z : R) : R := (68 + z * (137 + z * (112 + z * (37 + z * (59 + z * (51 + z * (19 + z * (107 + z * (31 + z * (124 + z * (41 + z * (125 + z * (111 + z * (89 + z * (0 + z * (136 + z * (121 + z * (91 + z * 38))))))))))))))))))

def pow18_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-50) + z * ((-144) + z * ((-210) + z * ((-275) + z * ((-244) + z * ((-204) + z * ((-79) + z * ((-120) + z * ((-94) + z * ((-235) + z * ((-304) + z * ((-416) + z * ((-380) + z * ((-548) + z * ((-530) + z * ((-635) + z * ((-564) + z * ((-717) + z * ((-545) + z * ((-598) + z * ((-520) + z * ((-391) + z * ((-249) + z * ((-300) + z * ((-320) + z * ((-543) + z * ((-409) + z * ((-435) + z * ((-379) + z * ((-300) + z * ((-263) + z * ((-328) + z * ((-122) + z * ((-53) + z * ((-102) + z * ((-90) + z * ((-36) + z * (13 + z * 17))))))))))))))))))))))))))))))))))))))


def pow18_17 {R : Type*} [CommRing R] (z : R) : R := (48 + z * (55 + z * (36 + z * (114 + z * (77 + z * (69 + z * (7 + z * (86 + z * (135 + z * (19 + z * (56 + z * (98 + z * (111 + z * (60 + z * (93 + z * (124 + z * (73 + z * (82 + z * (98 + z * 31)))))))))))))))))))

def pow18_17_q {R : Type*} [CommRing R] (z : R) : R := (59 + z * (69 + z * (88 + z * (87 + z * (12 + z * (124 + z * (86 + z * (95 + z * (128 + z * (58 + z * (58 + z * (60 + z * (34 + z * (27 + z * (12 + z * (46 + z * (125 + z * (43 + z * 64))))))))))))))))))

def pow18_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * ((-77) + z * ((-155) + z * ((-157) + z * ((-160) + z * ((-241) + z * ((-188) + z * ((-203) + z * ((-329) + z * ((-295) + z * ((-319) + z * ((-376) + z * ((-205) + z * ((-185) + z * ((-195) + z * ((-113) + z * ((-229) + z * ((-184) + z * ((-134) + z * ((-166) + z * ((-148) + z * ((-108) + z * (84 + z * (30 + z * (5 + z * ((-58) + z * ((-3) + z * (113 + z * (99 + z * (230 + z * (98 + z * (119 + z * (115 + z * (142 + z * (32 + z * ((-58) + z * (25 + z * (14 + z * 37))))))))))))))))))))))))))))))))))))))


def pow18_34 {R : Type*} [CommRing R] (z : R) : R := (27 + z * (103 + z * (123 + z * (124 + z * (17 + z * (10 + z * (9 + z * (34 + z * (15 + z * (74 + z * (8 + z * (115 + z * (54 + z * (4 + z * (22 + z * (28 + z * (41 + z * (71 + z * (98 + z * 68)))))))))))))))))))

def pow18_34_q {R : Type*} [CommRing R] (z : R) : R := (117 + z * (10 + z * (46 + z * (66 + z * (57 + z * (11 + z * (124 + z * (131 + z * (45 + z * (82 + z * (122 + z * (3 + z * (131 + z * (14 + z * (65 + z * (125 + z * (120 + z * (106 + z * 127))))))))))))))))))

def pow18_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-72) + z * ((-73) + z * ((-103) + z * ((-104) + z * ((-91) + z * ((-37) + z * ((-104) + z * ((-179) + z * ((-102) + z * ((-265) + z * ((-328) + z * ((-69) + z * ((-128) + z * ((-242) + z * ((-132) + z * ((-17) + z * ((-248) + z * ((-217) + z * ((-181) + z * ((-232) + z * ((-112) + z * ((-72) + z * ((-78) + z * (43 + z * ((-55) + z * ((-223) + z * (10 + z * (9 + z * ((-116) + z * (136 + z * (65 + z * ((-101) + z * (60 + z * ((-19) + z * ((-103) + z * ((-41) + z * ((-86) + z * ((-74) + z * 6))))))))))))))))))))))))))))))))))))))


def pow18_68 {R : Type*} [CommRing R] (z : R) : R := (94 + z * (113 + z * (71 + z * (5 + z * (98 + z * (131 + z * (135 + z * (108 + z * (90 + z * (120 + z * (5 + z * (65 + z * (86 + z * (108 + z * (53 + z * (73 + z * (133 + z * (88 + z * (23 + z * 137)))))))))))))))))))

def pow18_68_q {R : Type*} [CommRing R] (z : R) : R := (59 + z * (31 + z * (15 + z * (19 + z * (26 + z * (56 + z * (41 + z * (82 + z * (103 + z * (77 + z * (6 + z * (75 + z * (32 + z * (69 + z * (97 + z * (26 + z * (49 + z * (113 + z * 37))))))))))))))))))

def pow18_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-40) + z * ((-36) + z * (32 + z * (119 + z * (173 + z * (109 + z * ((-5) + z * ((-162) + z * ((-230) + z * ((-267) + z * ((-201) + z * ((-183) + z * ((-40) + z * ((-111) + z * ((-163) + z * ((-360) + z * ((-414) + z * ((-419) + z * ((-299) + z * ((-169) + z * ((-26) + z * ((-188) + z * ((-211) + z * ((-326) + z * ((-407) + z * ((-259) + z * ((-279) + z * ((-296) + z * ((-47) + z * ((-37) + z * ((-114) + z * ((-118) + z * ((-188) + z * ((-124) + z * (30 + z * (12 + z * (7 + z * (61 + z * 33))))))))))))))))))))))))))))))))))))))


def pow18_69 {R : Type*} [CommRing R] (z : R) : R := (114 + z * (1 + z * (68 + z * (42 + z * (62 + z * (26 + z * (114 + z * (30 + z * (120 + z * (73 + z * (56 + z * (94 + z * (91 + z * (82 + z * (135 + z * (38 + z * (133 + z * (50 + z * (22 + z * 38)))))))))))))))))))

def pow18_69_q {R : Type*} [CommRing R] (z : R) : R := (99 + z * (83 + z * (36 + z * (121 + z * (61 + z * (67 + z * (133 + z * (42 + z * (115 + z * (44 + z * (5 + z * (87 + z * (82 + z * (82 + z * (27 + z * (136 + z * (76 + z * (95 + z * 24))))))))))))))))))

def pow18_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-33) + z * ((-95) + z * ((-131) + z * ((-215) + z * ((-181) + z * ((-164) + z * ((-188) + z * ((-189) + z * ((-174) + z * ((-176) + z * ((-179) + z * ((-128) + z * ((-72) + z * ((-142) + z * ((-80) + z * ((-129) + z * ((-229) + z * ((-104) + z * ((-187) + z * ((-36) + z * (76 + z * (66 + z * ((-13) + z * (230 + z * (37 + z * (84 + z * (80 + z * (32 + z * (199 + z * (70 + z * (20 + z * (117 + z * (85 + z * (71 + z * (80 + z * (20 + z * (74 + z * (14 + z * 125))))))))))))))))))))))))))))))))))))))


def pow18_138 {R : Type*} [CommRing R] (z : R) : R := (50 + z * (95 + z * (134 + z * (68 + z * (58 + z * (71 + z * (27 + z * (114 + z * (60 + z * (84 + z * (44 + z * (125 + z * (127 + z * (132 + z * (10 + z * (108 + z * (60 + z * (14 + z * (91 + z * 42)))))))))))))))))))

def pow18_138_q {R : Type*} [CommRing R] (z : R) : R := (118 + z * (72 + z * (97 + z * (35 + z * (101 + z * (50 + z * (94 + z * (59 + z * (59 + z * (134 + z * (117 + z * (119 + z * (46 + z * (79 + z * (88 + z * (59 + z * (72 + z * (42 + z * 54))))))))))))))))))

def pow18_138_mul_t {R : Type*} [CommRing R] (z : R) : R := (4 + z * ((-157) + z * ((-132) + z * ((-219) + z * ((-220) + z * ((-258) + z * ((-117) + z * ((-302) + z * ((-106) + z * ((-330) + z * ((-355) + z * ((-349) + z * ((-262) + z * ((-392) + z * ((-169) + z * ((-359) + z * ((-133) + z * ((-247) + z * ((-261) + z * ((-298) + z * ((-152) + z * ((-153) + z * (49 + z * ((-100) + z * ((-38) + z * ((-3) + z * ((-46) + z * (3 + z * (5 + z * ((-76) + z * (70 + z * ((-19) + z * ((-5) + z * ((-13) + z * ((-72) + z * ((-9) + z * ((-48) + z * ((-38) + z * 10))))))))))))))))))))))))))))))))))))))


def pow18_139 {R : Type*} [CommRing R] (z : R) : R := (130 + z * (10 + z * (112 + z * (54 + z * (135 + z * (70 + z * (46 + z * (28 + z * (90 + z * (123 + z * (68 + z * (75 + z * (129 + z * (32 + z * (65 + z * (132 + z * (102 + z * (14 + z * (106 + z * 38)))))))))))))))))))

def pow18_139_q {R : Type*} [CommRing R] (z : R) : R := (42 + z * (78 + z * (90 + z * (25 + z * (134 + z * (40 + z * (5 + z * (60 + z * (34 + z * (68 + z * (113 + z * (18 + z * (84 + z * (49 + z * (131 + z * (29 + z * (104 + z * (13 + z * 52))))))))))))))))))

def pow18_139_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-10) + z * ((-51) + z * ((-99) + z * ((-126) + z * ((-182) + z * ((-156) + z * ((-102) + z * ((-56) + z * ((-53) + z * ((-43) + z * ((-119) + z * ((-113) + z * ((-119) + z * ((-61) + z * ((-162) + z * (43 + z * ((-23) + z * ((-77) + z * ((-68) + z * (82 + z * ((-97) + z * (247 + z * (79 + z * ((-64) + z * (197 + z * (88 + z * (118 + z * (159 + z * (68 + z * ((-52) + z * (201 + z * (29 + z * (44 + z * (2 + z * (18 + z * (19 + z * (2 + z * (40 + z * 38))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139


def pow19_16 {R : Type*} [CommRing R] (z : R) : R := (61 + z * (23 + z * (52 + z * (49 + z * (30 + z * (134 + z * (23 + z * (90 + z * (87 + z * (124 + z * (96 + z * (67 + z * (20 + z * (64 + z * (126 + z * (48 + z * (96 + z * (15 + z * (136 + z * 134)))))))))))))))))))

def pow19_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-73) + z * ((-58) + z * ((-27) + z * ((-71) + z * ((-34) + z * ((-30) + z * ((-95) + z * ((-119) + z * ((-56) + z * ((-7) + z * (95 + z * (245 + z * (147 + z * ((-59) + z * ((-66) + z * ((-198) + z * ((-197) + z * (105 + z * (89 + z * (153 + z * (311 + z * (52 + z * (2 + z * (109 + z * (0 + z * (115 + z * (225 + z * (116 + z * (98 + z * (99 + z * (6 + z * ((-127) + z * ((-69) + z * (11 + z * (62 + z * (84 + z * (45 + z * (16 + z * 27))))))))))))))))))))))))))))))))))))))


def pow19_138 {R : Type*} [CommRing R] (z : R) : R := (128 + z * (77 + z * (67 + z * (14 + z * (71 + z * (65 + z * (45 + z * (126 + z * (111 + z * (28 + z * (64 + z * (46 + z * (104 + z * (33 + z * (118 + z * (3 + z * (105 + z * (87 + z * (137 + z * 100)))))))))))))))))))

def pow19_138_q {R : Type*} [CommRing R] (z : R) : R := (76 + z * (2 + z * (58 + z * (42 + z * (70 + z * (116 + z * (34 + z * (86 + z * (17 + z * (23 + z * (23 + z * (77 + z * (65 + z * (76 + z * (75 + z * (45 + z * (78 + z * (83 + z * 35))))))))))))))))))

def pow19_138_mul_t {R : Type*} [CommRing R] (z : R) : R := (47 + z * (121 + z * (180 + z * (176 + z * (197 + z * (67 + z * ((-22) + z * (18 + z * (108 + z * (81 + z * (47 + z * (128 + z * ((-44) + z * ((-227) + z * ((-266) + z * ((-198) + z * ((-187) + z * ((-153) + z * (9 + z * (111 + z * ((-50) + z * ((-150) + z * ((-49) + z * ((-155) + z * ((-157) + z * ((-61) + z * ((-65) + z * ((-108) + z * ((-119) + z * ((-117) + z * ((-173) + z * ((-155) + z * ((-111) + z * ((-1) + z * (105 + z * (75 + z * (67 + z * (83 + z * 35))))))))))))))))))))))))))))))))))))))


abbrev pow19_139 {R : Type*} [CommRing R] (z : R) : R := u0 z

def pow19_139_q {R : Type*} [CommRing R] (z : R) : R := (132 + z * (113 + z * (84 + z * (90 + z * (97 + z * (114 + z * (3 + z * (97 + z * (33 + z * (100 + z * (76 + z * (99 + z * (94 + z * (13 + z * (49 + z * (96 + z * (82 + z * (60 + z * 47))))))))))))))))))

def pow19_139_mul_t {R : Type*} [CommRing R] (z : R) : R := (20 + z * ((-120) + z * ((-110) + z * ((-239) + z * ((-163) + z * ((-218) + z * ((-165) + z * ((-179) + z * ((-119) + z * ((-134) + z * ((-183) + z * ((-226) + z * ((-98) + z * ((-299) + z * ((-156) + z * ((-228) + z * (22 + z * ((-181) + z * ((-96) + z * ((-157) + z * ((-76) + z * ((-12) + z * (133 + z * (114 + z * ((-6) + z * ((-22) + z * (134 + z * (82 + z * (100 + z * (101 + z * (70 + z * (34 + z * (171 + z * (90 + z * (97 + z * (62 + z * (48 + z * (70 + z * 27))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_PPTSquare_GaloisAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial

open scoped BigOperators
open Equiv Equiv.Perm Function
namespace GaloisAction
open NumberField
open scoped NumberField
attribute [local instance] Classical.propDecidable
local instance prime131 : Fact (Nat.Prime 131) := ⟨by decide⟩
end GaloisAction

end

end OAI
end


