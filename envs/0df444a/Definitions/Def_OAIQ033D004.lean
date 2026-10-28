-- Prove2me | Definitions.Def_OAIQ033D004
-- name    : OAIQ033D004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T01:46:35.494654+00:00
-- url     : https://prove2.me/theorems/ea77d4be-6352-438a-ad27-26847230b101
-- title:
--   Definitions bundle OAIQ033D004 of the split of OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DimensionTen.main_pair`, carved from OpenAI's openai/math development (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 185 declarations of OpenAI's Lean: 185 definitions. The definitions and types are `OAI.DimensionTen.Mod131.pow12_64`, `OAI.DimensionTen.Mod131.pow12_64_mul_t`, `OAI.DimensionTen.Mod131.pow12_64_q`, `OAI.DimensionTen.Mod131.pow12_65`, `OAI.DimensionTen.Mod131.pow12_65_mul_t`, `OAI.DimensionTen.Mod131.pow12_65_q`, `OAI.DimensionTen.Mod131.pow12_8`, `OAI.DimensionTen.Mod131.pow12_8_mul_t`, `OAI.DimensionTen.Mod131.pow12_8_q`, `OAI.DimensionTen.Mod131.pow13_130`, `OAI.DimensionTen.Mod131.pow13_130_mul_t`, `OAI.DimensionTen.Mod131.pow13_130_q`, `OAI.DimensionTen.Mod131.pow13_131`, `OAI.DimensionTen.Mod131.pow13_131_mul_t`, `OAI.DimensionTen.Mod131.pow13_131_q`, `OAI.DimensionTen.Mod131.pow13_16`, `OAI.DimensionTen.Mod131.pow13_16_mul_t`, `OAI.DimensionTen.Mod131.pow13_16_q`, `OAI.DimensionTen.Mod131.pow13_2`, `OAI.DimensionTen.Mod131.pow13_2_mul_t`, `OAI.DimensionTen.Mod131.pow13_2_q`, `OAI.DimensionTen.Mod131.pow13_32`, `OAI.DimensionTen.Mod131.pow13_32_mul_t`, `OAI.DimensionTen.Mod131.pow13_32_q`, `OAI.DimensionTen.Mod131.pow13_4`, `OAI.DimensionTen.Mod131.pow13_4_mul_t`, `OAI.DimensionTen.Mod131.pow13_4_q`, `OAI.DimensionTen.Mod131.pow13_64`, `OAI.DimensionTen.Mod131.pow13_64_mul_t`, `OAI.DimensionTen.Mod131.pow13_64_q`, `OAI.DimensionTen.Mod131.pow13_65`, `OAI.DimensionTen.Mod131.pow13_65_mul_t`, `OAI.DimensionTen.Mod131.pow13_65_q`, `OAI.DimensionTen.Mod131.pow13_8`, `OAI.DimensionTen.Mod131.pow13_8_mul_t`, `OAI.DimensionTen.Mod131.pow13_8_q`, `OAI.DimensionTen.Mod131.pow14_130`, `OAI.DimensionTen.Mod131.pow14_130_mul_t`, `OAI.DimensionTen.Mod131.pow14_130_q`, `OAI.DimensionTen.Mod131.pow14_131` and 145 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Quantum/DimensionTen, in whole or in part: [`Quantum_DimensionTen_Mod131Powers01`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod131Powers01.lean), [`Quantum_DimensionTen_Mod131Powers06`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod131Powers06.lean), [`Quantum_DimensionTen_Mod131Powers07`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod131Powers07.lean), [`Quantum_DimensionTen_Mod131Powers08`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod131Powers08.lean), [`Quantum_DimensionTen_Mod131Powers09`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod131Powers09.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ033D013`.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Quantum/DimensionTen at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod131Powers01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131
def pow1_2 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * 1))

def pow1_2_q {R : Type*} [CommRing R] (_ : R) : R := 0

def pow1_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * 0))


def pow1_4 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * 1))))

abbrev pow1_4_q {R : Type*} [CommRing R] (z : R) : R := pow1_2_q z

def pow1_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * 0))))


def pow1_8 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 1))))))))

abbrev pow1_8_q {R : Type*} [CommRing R] (z : R) : R := pow1_2_q z

def pow1_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 0))))))))


def pow1_16 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 1))))))))))))))))

abbrev pow1_16_q {R : Type*} [CommRing R] (z : R) : R := pow1_2_q z

def pow1_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 0))))))))))))))))


def pow1_32 {R : Type*} [CommRing R] (z : R) : R := (117 + z * (123 + z * (50 + z * (47 + z * (91 + z * (44 + z * (95 + z * (70 + z * (102 + z * (114 + z * (11 + z * (16 + z * (107 + z * (83 + z * (100 + z * (42 + z * (112 + z * (67 + z * (42 + z * 41)))))))))))))))))))

def pow1_32_q {R : Type*} [CommRing R] (z : R) : R := (16 + z * (48 + z * (12 + z * (105 + z * (7 + z * (65 + z * (12 + z * (25 + z * (2 + z * (59 + z * (105 + z * (65 + z * 1))))))))))))

def pow1_32_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-7) + z * ((-25) + z * ((-30) + z * ((-71) + z * ((-64) + z * ((-121) + z * ((-99) + z * ((-124) + z * ((-161) + z * ((-131) + z * ((-217) + z * ((-226) + z * ((-247) + z * ((-209) + z * ((-301) + z * ((-250) + z * ((-253) + z * ((-211) + z * ((-271) + z * ((-235) + z * ((-202) + z * ((-245) + z * ((-256) + z * ((-163) + z * ((-110) + z * ((-91) + z * ((-123) + z * ((-110) + z * ((-102) + z * ((-83) + z * ((-34) + z * ((-1) + z * 0))))))))))))))))))))))))))))))))


def pow1_64 {R : Type*} [CommRing R] (z : R) : R := (68 + z * (24 + z * (123 + z * (9 + z * (2 + z * (0 + z * (1 + z * (35 + z * (53 + z * (88 + z * (90 + z * (65 + z * (119 + z * (67 + z * (83 + z * (105 + z * (68 + z * (96 + z * (118 + z * 109)))))))))))))))))))

def pow1_64_q {R : Type*} [CommRing R] (z : R) : R := (34 + z * (124 + z * (2 + z * (114 + z * (120 + z * (51 + z * (66 + z * (120 + z * (65 + z * (79 + z * (78 + z * (54 + z * (16 + z * (114 + z * (13 + z * (120 + z * (82 + z * (49 + z * 109))))))))))))))))))

def pow1_64_mul_t {R : Type*} [CommRing R] (z : R) : R := (91 + z * (160 + z * (142 + z * (67 + z * (142 + z * (70 + z * (107 + z * (203 + z * (115 + z * (210 + z * (197 + z * ((-50) + z * (52 + z * (266 + z * (201 + z * (141 + z * (236 + z * (240 + z * (162 + z * (80 + z * (68 + z * (174 + z * (78 + z * (25 + z * (77 + z * (142 + z * ((-12) + z * (17 + z * (87 + z * (1 + z * (124 + z * (61 + z * (73 + z * (49 + z * ((-55) + z * (8 + z * ((-19) + z * ((-29) + z * 12))))))))))))))))))))))))))))))))))))))


def pow1_65 {R : Type*} [CommRing R] (z : R) : R := (52 + z * (54 + z * (122 + z * (105 + z * (130 + z * (21 + z * (44 + z * (100 + z * (8 + z * (62 + z * (69 + z * (22 + z * (101 + z * (110 + z * (90 + z * (111 + z * (32 + z * (98 + z * (84 + z * 129)))))))))))))))))))

def pow1_65_q {R : Type*} [CommRing R] (_ : R) : R := 109

def pow1_65_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-42) + z * ((-39) + z * ((-54) + z * ((-19) + z * ((-60) + z * ((-95) + z * ((-2) + z * ((-59) + z * ((-83) + z * ((-45) + z * ((-14) + z * ((-96) + z * ((-71) + z * ((-64) + z * ((-6) + z * ((-31) + z * ((-71) + z * ((-41) + z * ((-49) + z * ((-55) + z * 0))))))))))))))))))))


def pow1_130 {R : Type*} [CommRing R] (z : R) : R := (98 + z * (40 + z * (27 + z * (78 + z * (53 + z * (99 + z * (5 + z * (53 + z * (38 + z * (110 + z * (66 + z * (22 + z * (80 + z * (84 + z * (41 + z * (80 + z * (64 + z * (33 + z * (73 + z * 96)))))))))))))))))))

def pow1_130_q {R : Type*} [CommRing R] (z : R) : R := (115 + z * (27 + z * (118 + z * (75 + z * (35 + z * (118 + z * (104 + z * (51 + z * (8 + z * (23 + z * (1 + z * (66 + z * (82 + z * (94 + z * (94 + z * (99 + z * (47 + z * (55 + z * 4))))))))))))))))))

def pow1_130_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-24) + z * ((-9) + z * (8 + z * (79 + z * (138 + z * (89 + z * (177 + z * (37 + z * (52 + z * (72 + z * (34 + z * (27 + z * (44 + z * (37 + z * (157 + z * (195 + z * (278 + z * (292 + z * (151 + z * (398 + z * (339 + z * (450 + z * (342 + z * (227 + z * (135 + z * (207 + z * (304 + z * (275 + z * (281 + z * (300 + z * (243 + z * (326 + z * (332 + z * (220 + z * (238 + z * (138 + z * (217 + z * (163 + z * 127))))))))))))))))))))))))))))))))))))))


def pow1_131 {R : Type*} [CommRing R] (z : R) : R := (47 + z * (40 + z * (53 + z * (46 + z * (74 + z * (113 + z * (38 + z * (97 + z * (16 + z * (94 + z * (50 + z * (65 + z * (115 + z * (24 + z * (67 + z * (26 + z * (77 + z * (76 + z * (2 + z * 25)))))))))))))))))))

def pow1_131_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-37) + z * ((-34) + z * ((-47) + z * ((-17) + z * ((-52) + z * ((-84) + z * ((-1) + z * ((-52) + z * ((-73) + z * ((-40) + z * ((-12) + z * ((-85) + z * ((-63) + z * ((-56) + z * ((-5) + z * ((-27) + z * ((-63) + z * ((-36) + z * ((-43) + z * ((-48) + z * 0))))))))))))))))))))


def pow2_2 {R : Type*} [CommRing R] (z : R) : R := (3 + z * (58 + z * (128 + z * (98 + z * (24 + z * (97 + z * (13 + z * (22 + z * (34 + z * (127 + z * (84 + z * (119 + z * (86 + z * (102 + z * (55 + z * (78 + z * (108 + z * (17 + z * (13 + z * 44)))))))))))))))))))

def pow2_2_q {R : Type*} [CommRing R] (z : R) : R := (107 + z * (18 + z * (80 + z * (14 + z * (66 + z * (48 + z * (75 + z * (85 + z * (124 + z * (41 + z * (130 + z * (121 + z * (72 + z * (16 + z * (13 + z * (109 + z * (80 + z * (115 + z * 101))))))))))))))))))

def pow2_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-24) + z * ((-17) + z * ((-40) + z * (3 + z * ((-28) + z * ((-3) + z * (31 + z * (7 + z * ((-41) + z * (10 + z * (1 + z * ((-84) + z * ((-37) + z * ((-132) + z * (114 + z * ((-163) + z * ((-6) + z * ((-46) + z * ((-136) + z * ((-147) + z * ((-200) + z * (16 + z * ((-186) + z * ((-193) + z * ((-104) + z * ((-171) + z * ((-134) + z * ((-223) + z * ((-117) + z * ((-169) + z * ((-137) + z * ((-56) + z * ((-59) + z * ((-74) + z * ((-144) + z * ((-99) + z * ((-75) + z * ((-51) + z * 4))))))))))))))))))))))))))))))))))))))


def pow2_16 {R : Type*} [CommRing R] (z : R) : R := (37 + z * (44 + z * (129 + z * (3 + z * (104 + z * (64 + z * (85 + z * (87 + z * (127 + z * (77 + z * (35 + z * (125 + z * (49 + z * (84 + z * (16 + z * (107 + z * (94 + z * (60 + z * (94 + z * 126)))))))))))))))))))

def pow2_16_q {R : Type*} [CommRing R] (z : R) : R := (35 + z * (61 + z * (102 + z * (108 + z * (45 + z * (108 + z * (87 + z * (7 + z * (112 + z * (42 + z * (9 + z * (113 + z * (13 + z * (113 + z * (6 + z * (103 + z * (26 + z * (129 + z * 60))))))))))))))))))

def pow2_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (7 + z * ((-33) + z * ((-24) + z * ((-54) + z * ((-71) + z * ((-14) + z * ((-81) + z * (11 + z * (24 + z * (42 + z * (93 + z * (84 + z * (221 + z * (48 + z * (131 + z * (193 + z * (61 + z * (80 + z * (133 + z * ((-17) + z * (21 + z * (72 + z * ((-64) + z * (166 + z * ((-29) + z * (62 + z * (15 + z * ((-6) + z * ((-13) + z * ((-80) + z * ((-79) + z * (5 + z * ((-69) + z * ((-88) + z * ((-29) + z * ((-38) + z * ((-44) + z * (21 + z * 15))))))))))))))))))))))))))))))))))))))


def pow2_32 {R : Type*} [CommRing R] (z : R) : R := (36 + z * (101 + z * (94 + z * (12 + z * (26 + z * (31 + z * (129 + z * (9 + z * (23 + z * (0 + z * (92 + z * (114 + z * (51 + z * (8 + z * (124 + z * (18 + z * (62 + z * (42 + z * (10 + z * 89)))))))))))))))))))

def pow2_32_q {R : Type*} [CommRing R] (z : R) : R := (45 + z * (47 + z * (50 + z * (106 + z * (93 + z * (37 + z * (5 + z * (84 + z * (68 + z * (109 + z * (49 + z * (4 + z * (108 + z * (116 + z * (19 + z * (42 + z * (65 + z * (30 + z * 25))))))))))))))))))

def pow2_32_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-7) + z * ((-10) + z * (29 + z * ((-1) + z * (57 + z * ((-61) + z * (147 + z * (43 + z * (115 + z * (114 + z * (229 + z * (140 + z * (118 + z * (290 + z * (63 + z * (292 + z * (152 + z * (333 + z * (263 + z * (450 + z * (320 + z * (373 + z * (374 + z * (474 + z * (428 + z * (290 + z * (430 + z * (415 + z * (242 + z * (207 + z * (342 + z * (207 + z * (214 + z * (190 + z * (290 + z * (211 + z * (156 + z * (168 + z * 121))))))))))))))))))))))))))))))))))))))


def pow2_130 {R : Type*} [CommRing R] (z : R) : R := (124 + z * (3 + z * (88 + z * (1 + z * (31 + z * (105 + z * (20 + z * (124 + z * (33 + z * (87 + z * (47 + z * (77 + z * (38 + z * (34 + z * (10 + z * (13 + z * (3 + z * (95 + z * (78 + z * 8)))))))))))))))))))

def pow2_130_q {R : Type*} [CommRing R] (z : R) : R := (80 + z * (118 + z * (78 + z * (103 + z * (27 + z * (40 + z * (42 + z * (92 + z * (127 + z * (64 + z * (88 + z * (97 + z * (19 + z * (41 + z * (35 + z * (116 + z * (9 + z * (74 + z * 105))))))))))))))))))

def pow2_130_mul_t {R : Type*} [CommRing R] (z : R) : R := (7 + z * ((-51) + z * (27 + z * ((-87) + z * (49 + z * ((-52) + z * (76 + z * (74 + z * (6 + z * (36 + z * (65 + z * (148 + z * ((-105) + z * (114 + z * (85 + z * (131 + z * (126 + z * (154 + z * (247 + z * (3 + z * (243 + z * (247 + z * (164 + z * (188 + z * (325 + z * (186 + z * ((-11) + z * (209 + z * (102 + z * (150 + z * (95 + z * (147 + z * (207 + z * (65 + z * (88 + z * (57 + z * (32 + z * (44 + z * 24))))))))))))))))))))))))))))))))))))))


def pow2_131 {R : Type*} [CommRing R] (z : R) : R := (19 + z * (111 + z * (70 + z * (108 + z * (52 + z * (26 + z * (95 + z * (93 + z * (75 + z * (108 + z * (35 + z * (42 + z * (64 + z * (23 + z * (90 + z * (49 + z * (55 + z * (90 + z * (129 + z * 129)))))))))))))))))))

def pow2_131_q {R : Type*} [CommRing R] (z : R) : R := (14 + z * (29 + z * (94 + z * (65 + z * (65 + z * (119 + z * (43 + z * (72 + z * (32 + z * (16 + z * (57 + z * (28 + z * (17 + z * (98 + z * (11 + z * (49 + z * (100 + z * (32 + z * 69))))))))))))))))))

def pow2_131_mul_t {R : Type*} [CommRing R] (z : R) : R := (39 + z * (22 + z * (29 + z * ((-4) + z * (11 + z * (42 + z * ((-39) + z * (35 + z * ((-44) + z * (78 + z * ((-32) + z * (93 + z * (129 + z * ((-60) + z * (127 + z * ((-108) + z * (96 + z * (18 + z * ((-103) + z * (85 + z * ((-125) + z * ((-55) + z * (17 + z * ((-34) + z * ((-35) + z * ((-42) + z * ((-47) + z * ((-20) + z * ((-31) + z * ((-72) + z * ((-14) + z * ((-68) + z * ((-75) + z * ((-27) + z * ((-22) + z * ((-39) + z * ((-24) + z * ((-20) + z * 1))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod131Powers06
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131


def pow12_8 {R : Type*} [CommRing R] (z : R) : R := (41 + z * (53 + z * (5 + z * (55 + z * (58 + z * (57 + z * (35 + z * (9 + z * (40 + z * (84 + z * (92 + z * (107 + z * (74 + z * (48 + z * (24 + z * (110 + z * (24 + z * (63 + z * (40 + z * 57)))))))))))))))))))

def pow12_8_q {R : Type*} [CommRing R] (z : R) : R := (126 + z * (12 + z * (0 + z * (110 + z * (66 + z * (84 + z * (35 + z * (13 + z * (31 + z * (25 + z * (34 + z * (84 + z * (48 + z * (62 + z * (65 + z * (0 + z * (38 + z * (128 + z * 36))))))))))))))))))

def pow12_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * (15 + z * (19 + z * (67 + z * (13 + z * ((-41) + z * (90 + z * ((-10) + z * ((-7) + z * (32 + z * (86 + z * ((-63) + z * (0 + z * (117 + z * (76 + z * (169 + z * (21 + z * (201 + z * (105 + z * (222 + z * (304 + z * (206 + z * (128 + z * (153 + z * (265 + z * (64 + z * (347 + z * (167 + z * (236 + z * (100 + z * (152 + z * (329 + z * (281 + z * (98 + z * (151 + z * (176 + z * (29 + z * (166 + z * 119))))))))))))))))))))))))))))))))))))))


def pow12_64 {R : Type*} [CommRing R] (z : R) : R := (66 + z * (63 + z * (79 + z * (24 + z * (82 + z * (84 + z * (14 + z * (89 + z * (78 + z * (98 + z * (78 + z * (48 + z * (121 + z * (70 + z * (124 + z * (122 + z * (37 + z * (59 + z * (46 + z * 27)))))))))))))))))))

def pow12_64_q {R : Type*} [CommRing R] (z : R) : R := (66 + z * (26 + z * (87 + z * (105 + z * (84 + z * (5 + z * (2 + z * (31 + z * (12 + z * (115 + z * (34 + z * (81 + z * (59 + z * (66 + z * (68 + z * (4 + z * (14 + z * (86 + z * 1))))))))))))))))))

def pow12_64_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-22) + z * ((-23) + z * ((-58) + z * ((-61) + z * ((-86) + z * ((-59) + z * (14 + z * ((-22) + z * (25 + z * (41 + z * (60 + z * ((-73) + z * ((-21) + z * ((-23) + z * ((-93) + z * (1 + z * (60 + z * (159 + z * (122 + z * (84 + z * (23 + z * (33 + z * (40 + z * (128 + z * (112 + z * (20 + z * (118 + z * (11 + z * (17 + z * (21 + z * (91 + z * (82 + z * (50 + z * ((-49) + z * (44 + z * (15 + z * (1 + z * (0 + z * 0))))))))))))))))))))))))))))))))))))))


def pow12_65 {R : Type*} [CommRing R] (z : R) : R := (24 + z * (104 + z * (1 + z * (36 + z * (66 + z * (129 + z * (54 + z * (35 + z * (10 + z * (21 + z * (6 + z * (107 + z * (23 + z * (110 + z * (91 + z * (5 + z * (69 + z * (14 + z * (127 + z * 73)))))))))))))))))))

def pow12_65_q {R : Type*} [CommRing R] (z : R) : R := (32 + z * (5 + z * (71 + z * (41 + z * (115 + z * (45 + z * (89 + z * (128 + z * (42 + z * (57 + z * (106 + z * (13 + z * (100 + z * (113 + z * (101 + z * (79 + z * (83 + z * (23 + z * 19))))))))))))))))))

def pow12_65_mul_t {R : Type*} [CommRing R] (z : R) : R := (40 + z * (58 + z * (60 + z * (36 + z * (57 + z * (63 + z * (10 + z * ((-22) + z * (31 + z * ((-1) + z * (18 + z * ((-59) + z * (18 + z * (51 + z * (33 + z * ((-24) + z * (50 + z * ((-1) + z * ((-4) + z * (107 + z * (38 + z * (6 + z * (98 + z * (17 + z * (69 + z * (23 + z * (105 + z * (228 + z * (163 + z * (112 + z * (160 + z * (129 + z * (109 + z * (148 + z * (93 + z * (50 + z * (85 + z * (57 + z * 25))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod131Powers07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131
def pow13_2 {R : Type*} [CommRing R] (z : R) : R := (81 + z * (28 + z * (47 + z * (86 + z * (54 + z * (97 + z * (97 + z * (122 + z * (104 + z * (127 + z * (118 + z * (123 + z * (55 + z * (33 + z * (7 + z * (128 + z * (80 + z * (117 + z * (1 + z * 39)))))))))))))))))))

def pow13_2_q {R : Type*} [CommRing R] (z : R) : R := (24 + z * (39 + z * (23 + z * (41 + z * (63 + z * (59 + z * (77 + z * (78 + z * (7 + z * (58 + z * (2 + z * (74 + z * (3 + z * (48 + z * (34 + z * (90 + z * (22 + z * (68 + z * 112))))))))))))))))))

def pow13_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (48 + z * (52 + z * (63 + z * (97 + z * (23 + z * (48 + z * (45 + z * (61 + z * (17 + z * (26 + z * (162 + z * ((-1) + z * (89 + z * (64 + z * (8 + z * (105 + z * (72 + z * (133 + z * (44 + z * (166 + z * (141 + z * (79 + z * (6 + z * ((-2) + z * (170 + z * (53 + z * (34 + z * (135 + z * (123 + z * (61 + z * (6 + z * (46 + z * (137 + z * (42 + z * (59 + z * (64 + z * (81 + z * (20 + z * 48))))))))))))))))))))))))))))))))))))))


def pow13_4 {R : Type*} [CommRing R] (z : R) : R := (82 + z * (130 + z * (34 + z * (25 + z * (120 + z * (18 + z * (63 + z * (92 + z * (91 + z * (70 + z * (64 + z * (118 + z * (58 + z * (17 + z * (45 + z * (112 + z * (46 + z * (52 + z * (75 + z * 37)))))))))))))))))))

def pow13_4_q {R : Type*} [CommRing R] (z : R) : R := (106 + z * (109 + z * (68 + z * (55 + z * (123 + z * (90 + z * (23 + z * (42 + z * (106 + z * (111 + z * (104 + z * (38 + z * (112 + z * (96 + z * (14 + z * (83 + z * (65 + z * (38 + z * 80))))))))))))))))))

def pow13_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (9 + z * ((-46) + z * ((-53) + z * (9 + z * ((-57) + z * ((-64) + z * (12 + z * (95 + z * (62 + z * (71 + z * (215 + z * (261 + z * (150 + z * (148 + z * (265 + z * (368 + z * (293 + z * (287 + z * (349 + z * (327 + z * (205 + z * (203 + z * (369 + z * (189 + z * (284 + z * (247 + z * (280 + z * (174 + z * (75 + z * ((-93) + z * (50 + z * ((-25) + z * (153 + z * (32 + z * (44 + z * ((-31) + z * (14 + z * ((-40) + z * 11))))))))))))))))))))))))))))))))))))))


def pow13_8 {R : Type*} [CommRing R] (z : R) : R := (125 + z * (26 + z * (98 + z * (19 + z * (20 + z * (3 + z * (2 + z * (57 + z * (106 + z * (115 + z * (91 + z * (26 + z * (81 + z * (50 + z * (85 + z * (39 + z * (7 + z * (20 + z * (44 + z * 81)))))))))))))))))))

def pow13_8_q {R : Type*} [CommRing R] (z : R) : R := (56 + z * (106 + z * (9 + z * (99 + z * (96 + z * (50 + z * (85 + z * (92 + z * (121 + z * (60 + z * (42 + z * (69 + z * (38 + z * (86 + z * (26 + z * (120 + z * (55 + z * (84 + z * 59))))))))))))))))))

def pow13_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (29 + z * (102 + z * (102 + z * ((-4) + z * (83 + z * (64 + z * ((-31) + z * (95 + z * (78 + z * (25 + z * (104 + z * (121 + z * (99 + z * ((-9) + z * ((-1) + z * (158 + z * (93 + z * ((-9) + z * (129 + z * (137 + z * ((-97) + z * (23 + z * (57 + z * (28 + z * ((-40) + z * (48 + z * (67 + z * (34 + z * ((-23) + z * (30 + z * (48 + z * ((-35) + z * (3 + z * (30 + z * ((-19) + z * ((-3) + z * (3 + z * (12 + z * 10))))))))))))))))))))))))))))))))))))))


def pow13_16 {R : Type*} [CommRing R] (z : R) : R := (13 + z * (23 + z * (5 + z * (108 + z * (16 + z * (61 + z * (37 + z * (112 + z * (92 + z * (91 + z * (47 + z * (22 + z * (34 + z * (106 + z * (96 + z * (126 + z * (19 + z * (1 + z * (17 + z * 3)))))))))))))))))))

def pow13_16_q {R : Type*} [CommRing R] (z : R) : R := (45 + z * (82 + z * (36 + z * (106 + z * (93 + z * (101 + z * (122 + z * (17 + z * (124 + z * (36 + z * (50 + z * (70 + z * (82 + z * (23 + z * (17 + z * (75 + z * (16 + z * (114 + z * 11))))))))))))))))))

def pow13_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (102 + z * (2 + z * (127 + z * ((-27) + z * ((-11) + z * ((-172) + z * ((-201) + z * ((-111) + z * ((-121) + z * (22 + z * (20 + z * ((-91) + z * ((-77) + z * ((-281) + z * ((-80) + z * ((-161) + z * ((-170) + z * ((-187) + z * ((-51) + z * ((-114) + z * ((-132) + z * ((-17) + z * ((-104) + z * ((-74) + z * ((-138) + z * ((-110) + z * (42 + z * (92 + z * (19 + z * (6 + z * ((-66) + z * (39 + z * (40 + z * (7 + z * ((-39) + z * ((-42) + z * ((-23) + z * (48 + z * 50))))))))))))))))))))))))))))))))))))))


def pow13_32 {R : Type*} [CommRing R] (z : R) : R := (64 + z * (110 + z * (86 + z * (19 + z * (107 + z * (103 + z * (101 + z * (85 + z * (37 + z * (116 + z * (38 + z * (48 + z * (56 + z * (15 + z * (62 + z * (62 + z * (28 + z * (12 + z * (119 + z * 108)))))))))))))))))))

def pow13_32_q {R : Type*} [CommRing R] (z : R) : R := (120 + z * (7 + z * (129 + z * (116 + z * (122 + z * (18 + z * (110 + z * (67 + z * (14 + z * (9 + z * (129 + z * (64 + z * (98 + z * (39 + z * (88 + z * (41 + z * (10 + z * (32 + z * 9))))))))))))))))))

def pow13_32_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-45) + z * ((-42) + z * ((-106) + z * ((-92) + z * ((-177) + z * ((-213) + z * ((-88) + z * ((-269) + z * ((-188) + z * ((-168) + z * ((-57) + z * ((-283) + z * ((-139) + z * ((-166) + z * ((-186) + z * ((-250) + z * (18 + z * ((-69) + z * ((-50) + z * ((-248) + z * (12 + z * (2 + z * (37 + z * ((-3) + z * (37 + z * ((-100) + z * ((-68) + z * (29 + z * (74 + z * (6 + z * ((-26) + z * ((-70) + z * ((-57) + z * ((-53) + z * ((-33) + z * ((-22) + z * ((-18) + z * ((-4) + z * 0))))))))))))))))))))))))))))))))))))))


def pow13_64 {R : Type*} [CommRing R] (z : R) : R := (87 + z * (74 + z * (18 + z * (46 + z * (17 + z * (48 + z * (121 + z * (77 + z * (114 + z * (12 + z * (111 + z * (85 + z * (98 + z * (100 + z * (81 + z * (58 + z * (47 + z * (116 + z * (67 + z * 46)))))))))))))))))))

def pow13_64_q {R : Type*} [CommRing R] (z : R) : R := (109 + z * (65 + z * (28 + z * (49 + z * (118 + z * (96 + z * (39 + z * (88 + z * (127 + z * (100 + z * (68 + z * (121 + z * (43 + z * (42 + z * (115 + z * (29 + z * (103 + z * (91 + z * 5))))))))))))))))))

def pow13_64_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-11) + z * (43 + z * (89 + z * (83 + z * (46 + z * (67 + z * (225 + z * (193 + z * (87 + z * (86 + z * (216 + z * (129 + z * ((-60) + z * (12 + z * (65 + z * (8 + z * ((-113) + z * ((-146) + z * ((-47) + z * (23 + z * (118 + z * ((-75) + z * ((-111) + z * (104 + z * (60 + z * (0 + z * ((-55) + z * ((-54) + z * ((-2) + z * ((-66) + z * ((-3) + z * (17 + z * ((-23) + z * (49 + z * (55 + z * ((-27) + z * (79 + z * (193 + z * 89))))))))))))))))))))))))))))))))))))))


def pow13_65 {R : Type*} [CommRing R] (z : R) : R := (11 + z * (28 + z * (110 + z * (128 + z * (119 + z * (129 + z * (120 + z * (77 + z * (5 + z * (49 + z * (3 + z * (18 + z * (70 + z * (55 + z * (130 + z * (88 + z * (34 + z * (56 + z * (113 + z * 115)))))))))))))))))))

def pow13_65_q {R : Type*} [CommRing R] (z : R) : R := (104 + z * (127 + z * (51 + z * (90 + z * (96 + z * (5 + z * (107 + z * (50 + z * (71 + z * (114 + z * (65 + z * (3 + z * (45 + z * (13 + z * (128 + z * (12 + z * (18 + z * (130 + z * 12))))))))))))))))))

def pow13_65_mul_t {R : Type*} [CommRing R] (z : R) : R := (18 + z * (1 + z * ((-36) + z * ((-16) + z * ((-90) + z * ((-131) + z * ((-34) + z * ((-1) + z * ((-107) + z * ((-112) + z * (29 + z * ((-98) + z * ((-95) + z * (28 + z * ((-108) + z * (65 + z * (32 + z * (34 + z * (89 + z * ((-32) + z * (157 + z * (27 + z * (8 + z * (249 + z * (239 + z * (72 + z * (127 + z * (237 + z * (121 + z * (182 + z * (132 + z * (199 + z * (152 + z * (35 + z * (127 + z * (81 + z * (71 + z * (56 + z * 28))))))))))))))))))))))))))))))))))))))


def pow13_130 {R : Type*} [CommRing R] (z : R) : R := (111 + z * (107 + z * (77 + z * (19 + z * (116 + z * (85 + z * (1 + z * (25 + z * (86 + z * (6 + z * (54 + z * (99 + z * (56 + z * (92 + z * (93 + z * (31 + z * (0 + z * (34 + z * (105 + z * 111)))))))))))))))))))

def pow13_130_q {R : Type*} [CommRing R] (z : R) : R := (105 + z * (32 + z * (126 + z * (71 + z * (75 + z * (43 + z * (102 + z * (91 + z * (45 + z * (82 + z * (99 + z * (116 + z * (96 + z * (17 + z * (83 + z * (116 + z * (103 + z * (55 + z * 125))))))))))))))))))

def pow13_130_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-40) + z * ((-46) + z * ((-87) + z * ((-38) + z * ((-12) + z * (78 + z * (199 + z * (203 + z * (286 + z * (274 + z * (165 + z * ((-38) + z * ((-78) + z * ((-207) + z * ((-200) + z * ((-175) + z * ((-26) + z * (72 + z * (69 + z * (70 + z * (211 + z * (346 + z * (104 + z * (19 + z * (152 + z * ((-33) + z * ((-125) + z * ((-167) + z * ((-56) + z * ((-87) + z * (11 + z * (105 + z * (225 + z * (205 + z * (29 + z * (32 + z * (111 + z * (135 + z * 100))))))))))))))))))))))))))))))))))))))


def pow13_131 {R : Type*} [CommRing R] (z : R) : R := (111 + z * (37 + z * (126 + z * (77 + z * (12 + z * (1 + z * (66 + z * (12 + z * (82 + z * (36 + z * (87 + z * (127 + z * (122 + z * (1 + z * (103 + z * (126 + z * (17 + z * (80 + z * (78 + z * 56)))))))))))))))))))

def pow13_131_q {R : Type*} [CommRing R] (z : R) : R := (18 + z * (130 + z * (60 + z * (92 + z * (38 + z * (65 + z * (128 + z * (107 + z * (53 + z * (48 + z * (75 + z * (90 + z * (7 + z * (103 + z * (98 + z * (100 + z * (81 + z * (80 + z * 103))))))))))))))))))

def pow13_131_mul_t {R : Type*} [CommRing R] (z : R) : R := (66 + z * (63 + z * (65 + z * (29 + z * (72 + z * (42 + z * ((-48) + z * (31 + z * ((-84) + z * ((-76) + z * ((-8) + z * ((-11) + z * ((-136) + z * ((-69) + z * ((-61) + z * ((-101) + z * ((-156) + z * ((-80) + z * ((-161) + z * ((-92) + z * ((-61) + z * ((-43) + z * ((-231) + z * ((-118) + z * ((-74) + z * ((-156) + z * ((-193) + z * ((-49) + z * (62 + z * ((-37) + z * ((-32) + z * (14 + z * (21 + z * ((-29) + z * ((-50) + z * (18 + z * (78 + z * (65 + z * 67))))))))))))))))))))))))))))))))))))))


def pow14_2 {R : Type*} [CommRing R] (z : R) : R := (120 + z * (74 + z * (7 + z * (19 + z * (107 + z * (84 + z * (51 + z * (79 + z * (53 + z * (83 + z * (19 + z * (125 + z * (125 + z * (108 + z * (89 + z * (65 + z * (114 + z * (81 + z * (57 + z * 88)))))))))))))))))))

def pow14_2_q {R : Type*} [CommRing R] (z : R) : R := (58 + z * (124 + z * (71 + z * (61 + z * (64 + z * (63 + z * (114 + z * (22 + z * (80 + z * (65 + z * (61 + z * (76 + z * (20 + z * (1 + z * (66 + z * (120 + z * (11 + z * (94 + z * 123))))))))))))))))))

def pow14_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (71 + z * ((-6) + z * (124 + z * (82 + z * (50 + z * ((-51) + z * ((-75) + z * ((-146) + z * ((-30) + z * ((-124) + z * ((-1) + z * (46 + z * (131 + z * ((-45) + z * (210 + z * (48 + z * ((-19) + z * (146 + z * (103 + z * ((-75) + z * (116 + z * (153 + z * ((-44) + z * (67 + z * (94 + z * (159 + z * (192 + z * (151 + z * (121 + z * (298 + z * (142 + z * (69 + z * (164 + z * (71 + z * ((-5) + z * (15 + z * (12 + z * (4 + z * 23))))))))))))))))))))))))))))))))))))))


def pow14_4 {R : Type*} [CommRing R] (z : R) : R := (79 + z * (71 + z * (100 + z * (55 + z * (76 + z * (35 + z * (83 + z * (114 + z * (122 + z * (115 + z * (23 + z * (75 + z * (81 + z * (120 + z * (127 + z * (42 + z * (37 + z * (109 + z * (106 + z * 62)))))))))))))))))))

def pow14_4_q {R : Type*} [CommRing R] (z : R) : R := (48 + z * (65 + z * (126 + z * (5 + z * (114 + z * (105 + z * (84 + z * (63 + z * (37 + z * (44 + z * (70 + z * (118 + z * (120 + z * (51 + z * (128 + z * (1 + z * (47 + z * (3 + z * 15))))))))))))))))))

def pow14_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (91 + z * (93 + z * ((-41) + z * ((-45) + z * (73 + z * (94 + z * ((-50) + z * ((-23) + z * (67 + z * (3 + z * ((-48) + z * (94 + z * (147 + z * (78 + z * (54 + z * (95 + z * (250 + z * (258 + z * (233 + z * (266 + z * (347 + z * (210 + z * (263 + z * (340 + z * (378 + z * (355 + z * (387 + z * (352 + z * (434 + z * (319 + z * (366 + z * (330 + z * (285 + z * (228 + z * (203 + z * (193 + z * (125 + z * (69 + z * 59))))))))))))))))))))))))))))))))))))))


def pow14_8 {R : Type*} [CommRing R] (z : R) : R := (13 + z * (60 + z * (91 + z * (4 + z * (8 + z * (85 + z * (54 + z * (49 + z * (26 + z * (73 + z * (100 + z * (33 + z * (65 + z * (88 + z * (85 + z * (11 + z * (127 + z * (20 + z * (49 + z * 41)))))))))))))))))))

def pow14_8_q {R : Type*} [CommRing R] (z : R) : R := (25 + z * (87 + z * (89 + z * (94 + z * (4 + z * (97 + z * (100 + z * (6 + z * (23 + z * (129 + z * (57 + z * (38 + z * (30 + z * (37 + z * (67 + z * (63 + z * (111 + z * (87 + z * 45))))))))))))))))))

def pow14_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (38 + z * (43 + z * (81 + z * (60 + z * (120 + z * (39 + z * (61 + z * (115 + z * (243 + z * (295 + z * (163 + z * (232 + z * (272 + z * (274 + z * (294 + z * (554 + z * (415 + z * (322 + z * (367 + z * (484 + z * (536 + z * (433 + z * (365 + z * (401 + z * (340 + z * (429 + z * (507 + z * (332 + z * (186 + z * (161 + z * (292 + z * (345 + z * (227 + z * (76 + z * (46 + z * (99 + z * (124 + z * (77 + z * 29))))))))))))))))))))))))))))))))))))))


def pow14_16 {R : Type*} [CommRing R] (z : R) : R := (38 + z * (1 + z * (48 + z * (37 + z * (50 + z * (16 + z * (45 + z * (85 + z * (87 + z * (106 + z * (28 + z * (82 + z * (22 + z * (19 + z * (98 + z * (17 + z * (72 + z * (97 + z * (98 + z * 108)))))))))))))))))))

def pow14_16_q {R : Type*} [CommRing R] (z : R) : R := (0 + z * (60 + z * (41 + z * (52 + z * (73 + z * (48 + z * (97 + z * (116 + z * (3 + z * (64 + z * (82 + z * (34 + z * (122 + z * (127 + z * (129 + z * (21 + z * (115 + z * (99 + z * 109))))))))))))))))))

def pow14_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (1 + z * ((-11) + z * (8 + z * (20 + z * ((-9) + z * ((-80) + z * ((-74) + z * ((-3) + z * ((-86) + z * ((-138) + z * ((-68) + z * ((-49) + z * ((-100) + z * ((-151) + z * ((-198) + z * ((-71) + z * ((-119) + z * ((-244) + z * ((-201) + z * ((-156) + z * ((-189) + z * ((-189) + z * ((-233) + z * ((-151) + z * ((-138) + z * ((-255) + z * ((-55) + z * ((-84) + z * ((-67) + z * ((-160) + z * ((-84) + z * ((-129) + z * (5 + z * ((-114) + z * ((-67) + z * ((-49) + z * ((-69) + z * ((-25) + z * 12))))))))))))))))))))))))))))))))))))))


def pow14_32 {R : Type*} [CommRing R] (z : R) : R := (128 + z * (113 + z * (15 + z * (82 + z * (34 + z * (106 + z * (75 + z * (109 + z * (23 + z * (43 + z * (48 + z * (90 + z * (85 + z * (112 + z * (106 + z * (120 + z * (89 + z * (13 + z * (0 + z * 18)))))))))))))))))))

def pow14_32_q {R : Type*} [CommRing R] (z : R) : R := (63 + z * (92 + z * (68 + z * (100 + z * (38 + z * (129 + z * (88 + z * (64 + z * (121 + z * (74 + z * (104 + z * (7 + z * (58 + z * (42 + z * (113 + z * (25 + z * (61 + z * (9 + z * 5))))))))))))))))))

def pow14_32_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-14) + z * ((-58) + z * ((-62) + z * ((-97) + z * ((-87) + z * ((-192) + z * ((-161) + z * ((-185) + z * ((-228) + z * ((-193) + z * ((-283) + z * ((-153) + z * ((-285) + z * ((-289) + z * ((-279) + z * ((-212) + z * ((-197) + z * ((-215) + z * ((-150) + z * ((-192) + z * ((-59) + z * ((-134) + z * (1 + z * (67 + z * (22 + z * (186 + z * (191 + z * (171 + z * (234 + z * (63 + z * (167 + z * (101 + z * (118 + z * (195 + z * (160 + z * (227 + z * (226 + z * (159 + z * 89))))))))))))))))))))))))))))))))))))))


def pow14_64 {R : Type*} [CommRing R] (z : R) : R := (129 + z * (42 + z * (73 + z * (71 + z * (52 + z * (69 + z * (105 + z * (9 + z * (0 + z * (128 + z * (91 + z * (19 + z * (3 + z * (9 + z * (113 + z * (78 + z * (27 + z * (98 + z * (96 + z * 7)))))))))))))))))))

def pow14_64_q {R : Type*} [CommRing R] (z : R) : R := (50 + z * (122 + z * (42 + z * (113 + z * (41 + z * (113 + z * (96 + z * (123 + z * (40 + z * (72 + z * (80 + z * (70 + z * (74 + z * (113 + z * (13 + z * (78 + z * (35 + z * (100 + z * 62))))))))))))))))))

def pow14_64_mul_t {R : Type*} [CommRing R] (z : R) : R := (105 + z * (156 + z * (42 + z * (59 + z * (84 + z * (54 + z * (141 + z * (139 + z * (41 + z * ((-57) + z * (36 + z * (40 + z * (98 + z * (122 + z * (150 + z * (225 + z * (301 + z * (85 + z * (9 + z * (89 + z * (62 + z * (63 + z * ((-23) + z * ((-33) + z * ((-54) + z * (7 + z * (81 + z * (191 + z * (91 + z * (54 + z * (58 + z * (11 + z * ((-32) + z * ((-92) + z * ((-99) + z * ((-62) + z * ((-75) + z * ((-32) + z * 2))))))))))))))))))))))))))))))))))))))


def pow14_65 {R : Type*} [CommRing R] (z : R) : R := (57 + z * (65 + z * (64 + z * (59 + z * (64 + z * (103 + z * (88 + z * (127 + z * (118 + z * (114 + z * (58 + z * (94 + z * (14 + z * (92 + z * (123 + z * (90 + z * (37 + z * (53 + z * (88 + z * 10)))))))))))))))))))

def pow14_65_q {R : Type*} [CommRing R] (z : R) : R := (18 + z * (29 + z * (16 + z * (72 + z * (52 + z * (56 + z * (32 + z * (27 + z * (22 + z * (111 + z * (49 + z * (57 + z * (91 + z * (5 + z * (112 + z * (125 + z * (121 + z * (93 + z * 130))))))))))))))))))

def pow14_65_mul_t {R : Type*} [CommRing R] (z : R) : R := (102 + z * (54 + z * (172 + z * (146 + z * (102 + z * (79 + z * (167 + z * (52 + z * (106 + z * (105 + z * (98 + z * (173 + z * (218 + z * (36 + z * (96 + z * (186 + z * (35 + z * (218 + z * (137 + z * ((-29) + z * (78 + z * (46 + z * ((-238) + z * ((-172) + z * (66 + z * ((-69) + z * ((-57) + z * ((-123) + z * ((-13) + z * (39 + z * ((-103) + z * ((-92) + z * (79 + z * ((-34) + z * ((-110) + z * ((-23) + z * ((-3) + z * ((-21) + z * 2))))))))))))))))))))))))))))))))))))))


def pow14_130 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (83 + z * (59 + z * (41 + z * (100 + z * (122 + z * (87 + z * (73 + z * (63 + z * (123 + z * (54 + z * (0 + z * (14 + z * (103 + z * (27 + z * (78 + z * (93 + z * (58 + z * (71 + z * 56)))))))))))))))))))

def pow14_130_q {R : Type*} [CommRing R] (z : R) : R := (120 + z * (94 + z * (3 + z * (127 + z * (45 + z * (78 + z * (125 + z * (15 + z * (69 + z * (58 + z * (81 + z * (32 + z * (56 + z * (75 + z * (40 + z * (128 + z * (84 + z * (7 + z * 100))))))))))))))))))

def pow14_130_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-21) + z * ((-23) + z * ((-6) + z * ((-2) + z * ((-1) + z * ((-54) + z * (62 + z * (122 + z * (55 + z * (237 + z * (211 + z * (179 + z * (214 + z * (239 + z * (326 + z * (396 + z * (336 + z * (225 + z * (342 + z * (280 + z * (305 + z * (316 + z * (347 + z * (257 + z * (286 + z * (234 + z * (123 + z * (108 + z * (134 + z * (81 + z * (33 + z * (32 + z * (96 + z * (27 + z * ((-86) + z * ((-7) + z * (18 + z * ((-37) + z * 0))))))))))))))))))))))))))))))))))))))


def pow14_131 {R : Type*} [CommRing R] (z : R) : R := (93 + z * (91 + z * (41 + z * (95 + z * (97 + z * (39 + z * (42 + z * (96 + z * (8 + z * (19 + z * (113 + z * (59 + z * (50 + z * (1 + z * (39 + z * (105 + z * (104 + z * (74 + z * (71 + z * 23)))))))))))))))))))

def pow14_131_q {R : Type*} [CommRing R] (z : R) : R := (6 + z * (72 + z * (35 + z * (15 + z * (91 + z * (7 + z * (128 + z * (75 + z * (93 + z * (14 + z * (74 + z * (126 + z * (25 + z * (43 + z * (88 + z * (81 + z * (1 + z * (95 + z * 123))))))))))))))))))

def pow14_131_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-3) + z * (40 + z * (31 + z * (76 + z * (128 + z * (120 + z * (54 + z * (171 + z * (44 + z * (76 + z * (72 + z * (6 + z * (28 + z * (61 + z * ((-9) + z * (102 + z * (251 + z * (153 + z * (122 + z * (103 + z * (172 + z * (232 + z * ((-128) + z * ((-16) + z * (184 + z * (18 + z * ((-68) + z * (142 + z * (143 + z * ((-39) + z * (36 + z * (85 + z * (106 + z * (56 + z * (29 + z * (35 + z * ((-2) + z * (1 + z * 23))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod131Powers08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131
def pow15_2 {R : Type*} [CommRing R] (z : R) : R := (54 + z * (94 + z * (7 + z * (14 + z * (120 + z * (42 + z * (14 + z * (62 + z * (41 + z * (103 + z * (0 + z * (112 + z * (113 + z * (34 + z * (30 + z * (11 + z * (120 + z * (44 + z * (91 + z * 24)))))))))))))))))))

def pow15_2_q {R : Type*} [CommRing R] (z : R) : R := (54 + z * (92 + z * (110 + z * (52 + z * (65 + z * (77 + z * (27 + z * (22 + z * (68 + z * (86 + z * (20 + z * (124 + z * (92 + z * (71 + z * (125 + z * (5 + z * (1 + z * (54 + z * 5))))))))))))))))))

def pow15_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (45 + z * (74 + z * (20 + z * (78 + z * (139 + z * (55 + z * (24 + z * (138 + z * (66 + z * ((-107) + z * (90 + z * (106 + z * ((-71) + z * ((-160) + z * ((-46) + z * (21 + z * ((-24) + z * (109 + z * (103 + z * (60 + z * (52 + z * (47 + z * (46 + z * ((-13) + z * ((-75) + z * (1 + z * (87 + z * (47 + z * (50 + z * (1 + z * ((-27) + z * (94 + z * (133 + z * (142 + z * (164 + z * (90 + z * (35 + z * (22 + z * 4))))))))))))))))))))))))))))))))))))))


def pow15_4 {R : Type*} [CommRing R] (z : R) : R := (53 + z * (8 + z * (116 + z * (9 + z * (124 + z * (103 + z * (48 + z * (27 + z * (31 + z * (64 + z * (105 + z * (30 + z * (11 + z * (2 + z * (78 + z * (112 + z * (90 + z * (129 + z * (59 + z * 98)))))))))))))))))))

def pow15_4_q {R : Type*} [CommRing R] (z : R) : R := (128 + z * (114 + z * (60 + z * (86 + z * (115 + z * (122 + z * (118 + z * (63 + z * (46 + z * (127 + z * (64 + z * (104 + z * (25 + z * (127 + z * (40 + z * (55 + z * (45 + z * (19 + z * 52))))))))))))))))))

def pow15_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-27) + z * ((-12) + z * ((-54) + z * ((-111) + z * ((-75) + z * ((-106) + z * ((-208) + z * ((-214) + z * ((-173) + z * ((-226) + z * ((-227) + z * ((-317) + z * ((-170) + z * ((-216) + z * ((-402) + z * ((-243) + z * ((-167) + z * ((-265) + z * ((-287) + z * ((-219) + z * ((-87) + z * ((-188) + z * ((-204) + z * ((-18) + z * ((-147) + z * (4 + z * ((-148) + z * (88 + z * (61 + z * (27 + z * (76 + z * ((-37) + z * (31 + z * (17 + z * (96 + z * (54 + z * (46 + z * (7 + z * 4))))))))))))))))))))))))))))))))))))))


def pow15_8 {R : Type*} [CommRing R] (z : R) : R := (25 + z * (0 + z * (74 + z * (40 + z * (121 + z * (10 + z * (58 + z * (66 + z * (39 + z * (35 + z * (123 + z * (43 + z * (44 + z * (117 + z * (10 + z * (78 + z * (81 + z * (15 + z * (8 + z * 12)))))))))))))))))))

def pow15_8_q {R : Type*} [CommRing R] (z : R) : R := (19 + z * (117 + z * (4 + z * (32 + z * (68 + z * (7 + z * (67 + z * (93 + z * (38 + z * (58 + z * (103 + z * (78 + z * (1 + z * (115 + z * (0 + z * (116 + z * (40 + z * (81 + z * 41))))))))))))))))))

def pow15_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (14 + z * ((-45) + z * (41 + z * ((-53) + z * (133 + z * ((-9) + z * (100 + z * (119 + z * (21 + z * (49 + z * (113 + z * ((-24) + z * ((-51) + z * ((-71) + z * (39 + z * ((-62) + z * (34 + z * ((-43) + z * ((-41) + z * (311 + z * (139 + z * (333 + z * (9 + z * (136 + z * (143 + z * (109 + z * ((-13) + z * (93 + z * (5 + z * (60 + z * (69 + z * (157 + z * (203 + z * (262 + z * (242 + z * (178 + z * (160 + z * (67 + z * 73))))))))))))))))))))))))))))))))))))))


def pow15_16 {R : Type*} [CommRing R] (z : R) : R := (59 + z * (34 + z * (100 + z * (43 + z * (14 + z * (12 + z * (116 + z * (123 + z * (64 + z * (98 + z * (111 + z * (41 + z * (45 + z * (123 + z * (48 + z * (98 + z * (12 + z * (116 + z * (15 + z * 105)))))))))))))))))))

def pow15_16_q {R : Type*} [CommRing R] (z : R) : R := (48 + z * (59 + z * (73 + z * (93 + z * (127 + z * (90 + z * (73 + z * (38 + z * (41 + z * (64 + z * (81 + z * (16 + z * (22 + z * (48 + z * (11 + z * (105 + z * (121 + z * (120 + z * 13))))))))))))))))))

def pow15_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-14) + z * ((-40) + z * ((-45) + z * ((-84) + z * ((-66) + z * ((-163) + z * ((-60) + z * ((-138) + z * ((-102) + z * ((-194) + z * ((-98) + z * ((-168) + z * ((-113) + z * ((-126) + z * ((-52) + z * ((-120) + z * ((-127) + z * ((-77) + z * ((-191) + z * ((-46) + z * ((-89) + z * ((-262) + z * ((-164) + z * (0 + z * ((-186) + z * ((-49) + z * (15 + z * ((-139) + z * ((-126) + z * ((-63) + z * ((-60) + z * ((-33) + z * ((-92) + z * ((-151) + z * ((-135) + z * ((-104) + z * ((-64) + z * ((-6) + z * 1))))))))))))))))))))))))))))))))))))))


def pow15_32 {R : Type*} [CommRing R] (z : R) : R := (74 + z * (22 + z * (123 + z * (107 + z * (5 + z * (20 + z * (107 + z * (25 + z * (17 + z * (22 + z * (117 + z * (8 + z * (99 + z * (77 + z * (62 + z * (99 + z * (56 + z * (19 + z * (94 + z * 83)))))))))))))))))))

def pow15_32_q {R : Type*} [CommRing R] (z : R) : R := (76 + z * (66 + z * (79 + z * (115 + z * (33 + z * (78 + z * (83 + z * (68 + z * (112 + z * (121 + z * (8 + z * (115 + z * (68 + z * (33 + z * (29 + z * (96 + z * (63 + z * (61 + z * 21))))))))))))))))))

def pow15_32_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-3) + z * ((-22) + z * (7 + z * ((-28) + z * ((-34) + z * ((-130) + z * ((-52) + z * ((-74) + z * ((-26) + z * (57 + z * ((-31) + z * ((-116) + z * ((-12) + z * ((-29) + z * ((-47) + z * (175 + z * (9 + z * (131 + z * ((-33) + z * (177 + z * (52 + z * (207 + z * (97 + z * (209 + z * (120 + z * (240 + z * (271 + z * (124 + z * (147 + z * (149 + z * (176 + z * (46 + z * (257 + z * ((-7) + z * (149 + z * ((-22) + z * (147 + z * (13 + z * 84))))))))))))))))))))))))))))))))))))))


def pow15_64 {R : Type*} [CommRing R] (z : R) : R := (63 + z * (0 + z * (110 + z * (79 + z * (117 + z * (77 + z * (40 + z * (120 + z * (34 + z * (24 + z * (9 + z * (8 + z * (104 + z * (28 + z * (32 + z * (8 + z * (112 + z * (91 + z * (44 + z * 97)))))))))))))))))))

def pow15_64_q {R : Type*} [CommRing R] (z : R) : R := (48 + z * (20 + z * (66 + z * (70 + z * (82 + z * (120 + z * (78 + z * (117 + z * (6 + z * (128 + z * (94 + z * (123 + z * (47 + z * (19 + z * (91 + z * (22 + z * (90 + z * (42 + z * 77))))))))))))))))))

def pow15_64_mul_t {R : Type*} [CommRing R] (z : R) : R := (23 + z * (0 + z * (86 + z * (93 + z * (38 + z * (51 + z * (45 + z * ((-158) + z * (4 + z * ((-76) + z * ((-132) + z * ((-295) + z * (16 + z * ((-79) + z * ((-207) + z * ((-3) + z * ((-47) + z * ((-116) + z * ((-65) + z * ((-107) + z * ((-34) + z * ((-5) + z * ((-125) + z * ((-276) + z * (11 + z * (50 + z * ((-73) + z * ((-60) + z * (116 + z * (39 + z * (66 + z * (184 + z * (105 + z * (98 + z * (90 + z * (5 + z * (35 + z * (80 + z * 52))))))))))))))))))))))))))))))))))))))


def pow15_65 {R : Type*} [CommRing R] (z : R) : R := (110 + z * (124 + z * (57 + z * (108 + z * (92 + z * (113 + z * (12 + z * (129 + z * (59 + z * (114 + z * (122 + z * (76 + z * (49 + z * (7 + z * (91 + z * (53 + z * (47 + z * (46 + z * (37 + z * 32)))))))))))))))))))

def pow15_65_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (86 + z * (51 + z * (11 + z * (32 + z * (89 + z * (23 + z * (38 + z * (57 + z * (55 + z * (86 + z * (123 + z * (32 + z * (108 + z * (107 + z * (13 + z * (23 + z * (37 + z * 4))))))))))))))))))

def pow15_65_mul_t {R : Type*} [CommRing R] (z : R) : R := (29 + z * ((-4) + z * (28 + z * (106 + z * (141 + z * (118 + z * (116 + z * (214 + z * (159 + z * (64 + z * (66 + z * (55 + z * (10 + z * ((-90) + z * (17 + z * ((-39) + z * ((-29) + z * (99 + z * ((-2) + z * (180 + z * (170 + z * (18 + z * (82 + z * (138 + z * ((-23) + z * ((-105) + z * ((-27) + z * ((-13) + z * (38 + z * (0 + z * ((-17) + z * (87 + z * (69 + z * (115 + z * (192 + z * (141 + z * (74 + z * (58 + z * 17))))))))))))))))))))))))))))))))))))))


def pow15_130 {R : Type*} [CommRing R] (z : R) : R := (64 + z * (34 + z * (107 + z * (80 + z * (119 + z * (48 + z * (82 + z * (57 + z * (80 + z * (123 + z * (17 + z * (15 + z * (57 + z * (105 + z * (76 + z * (88 + z * (32 + z * (87 + z * (115 + z * 56)))))))))))))))))))

def pow15_130_q {R : Type*} [CommRing R] (z : R) : R := (94 + z * (95 + z * (116 + z * (58 + z * (112 + z * (1 + z * (103 + z * (99 + z * (12 + z * (29 + z * (55 + z * (63 + z * (17 + z * (74 + z * (32 + z * (25 + z * (85 + z * (22 + z * 107))))))))))))))))))

def pow15_130_mul_t {R : Type*} [CommRing R] (z : R) : R := (56 + z * (138 + z * (88 + z * (162 + z * (195 + z * (235 + z * (151 + z * (210 + z * (278 + z * (239 + z * (515 + z * (306 + z * (401 + z * (225 + z * (392 + z * (298 + z * (327 + z * (340 + z * (187 + z * (322 + z * (143 + z * (226 + z * (92 + z * (51 + z * (173 + z * (74 + z * (84 + z * (35 + z * (82 + z * ((-65) + z * ((-26) + z * ((-29) + z * ((-20) + z * (3 + z * ((-61) + z * ((-44) + z * ((-27) + z * ((-36) + z * 7))))))))))))))))))))))))))))))))))))))


def pow15_131 {R : Type*} [CommRing R] (z : R) : R := (116 + z * (61 + z * (96 + z * (109 + z * (106 + z * (28 + z * (97 + z * (18 + z * (30 + z * (26 + z * (21 + z * (64 + z * (44 + z * (127 + z * (31 + z * (62 + z * (41 + z * (68 + z * (30 + z * 76)))))))))))))))))))

def pow15_131_q {R : Type*} [CommRing R] (z : R) : R := (101 + z * (115 + z * (116 + z * (65 + z * (128 + z * (37 + z * (129 + z * (78 + z * (102 + z * (11 + z * (52 + z * (97 + z * (28 + z * (112 + z * (2 + z * (75 + z * (109 + z * (82 + z * 109))))))))))))))))))

def pow15_131_mul_t {R : Type*} [CommRing R] (z : R) : R := (6 + z * ((-12) + z * ((-16) + z * (47 + z * (41 + z * (1 + z * ((-5) + z * (39 + z * ((-71) + z * ((-19) + z * (27 + z * ((-138) + z * ((-91) + z * ((-126) + z * ((-6) + z * ((-111) + z * (6 + z * ((-70) + z * (6 + z * (66 + z * ((-16) + z * (7 + z * ((-17) + z * ((-51) + z * (5 + z * (37 + z * ((-95) + z * ((-33) + z * (33 + z * ((-25) + z * (52 + z * (39 + z * (53 + z * (96 + z * (29 + z * (29 + z * (18 + z * ((-5) + z * 9))))))))))))))))))))))))))))))))))))))


def pow16_2 {R : Type*} [CommRing R] (z : R) : R := (123 + z * (1 + z * (57 + z * (42 + z * (48 + z * (64 + z * (62 + z * (42 + z * (5 + z * (27 + z * (52 + z * (57 + z * (119 + z * (76 + z * (37 + z * (96 + z * (62 + z * (100 + z * (24 + z * 72)))))))))))))))))))

def pow16_2_q {R : Type*} [CommRing R] (z : R) : R := (23 + z * (78 + z * (2 + z * (95 + z * (0 + z * (59 + z * (61 + z * (5 + z * (93 + z * (128 + z * (86 + z * (52 + z * (13 + z * (87 + z * (70 + z * (26 + z * (129 + z * (100 + z * 12))))))))))))))))))

def pow16_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (93 + z * (70 + z * (158 + z * (203 + z * (298 + z * (176 + z * (313 + z * (220 + z * (125 + z * (108 + z * (1 + z * (1 + z * (40 + z * (91 + z * ((-3) + z * (212 + z * (74 + z * (128 + z * ((-45) + z * (196 + z * ((-28) + z * ((-114) + z * ((-102) + z * (49 + z * ((-161) + z * ((-141) + z * ((-72) + z * ((-159) + z * ((-88) + z * ((-94) + z * (83 + z * (42 + z * (40 + z * ((-58) + z * (9 + z * ((-36) + z * (29 + z * (28 + z * 44))))))))))))))))))))))))))))))))))))))


def pow16_4 {R : Type*} [CommRing R] (z : R) : R := (116 + z * (12 + z * (122 + z * (50 + z * (23 + z * (98 + z * (127 + z * (10 + z * (67 + z * (61 + z * (68 + z * (120 + z * (59 + z * (53 + z * (34 + z * (7 + z * (110 + z * (83 + z * (64 + z * 32)))))))))))))))))))

def pow16_4_q {R : Type*} [CommRing R] (z : R) : R := (109 + z * (83 + z * (50 + z * (91 + z * (83 + z * (73 + z * (13 + z * (89 + z * (38 + z * (102 + z * (112 + z * (5 + z * (74 + z * (74 + z * (67 + z * (64 + z * (32 + z * (78 + z * 75))))))))))))))))))

def pow16_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (73 + z * ((-69) + z * (4 + z * ((-33) + z * ((-47) + z * ((-94) + z * ((-17) + z * ((-75) + z * ((-196) + z * ((-173) + z * ((-115) + z * ((-176) + z * ((-131) + z * ((-146) + z * ((-212) + z * ((-55) + z * ((-111) + z * ((-19) + z * ((-172) + z * ((-22) + z * ((-217) + z * ((-123) + z * ((-83) + z * ((-62) + z * (50 + z * ((-69) + z * ((-83) + z * (80 + z * (56 + z * (92 + z * (105 + z * (111 + z * (134 + z * (23 + z * (79 + z * (25 + z * (41 + z * ((-12) + z * 39))))))))))))))))))))))))))))))))))))))


def pow16_8 {R : Type*} [CommRing R] (z : R) : R := (76 + z * (82 + z * (96 + z * (27 + z * (29 + z * (7 + z * (108 + z * (70 + z * (120 + z * (44 + z * (103 + z * (81 + z * (86 + z * (38 + z * (36 + z * (116 + z * (74 + z * (110 + z * (96 + z * 58)))))))))))))))))))

def pow16_8_q {R : Type*} [CommRing R] (z : R) : R := (58 + z * (10 + z * (38 + z * (55 + z * (120 + z * (35 + z * (123 + z * (32 + z * (79 + z * (82 + z * (59 + z * (87 + z * (116 + z * (119 + z * (30 + z * (23 + z * (124 + z * (47 + z * 107))))))))))))))))))

def pow16_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (80 + z * ((-4) + z * (170 + z * (61 + z * (46 + z * (125 + z * (146 + z * (52 + z * (164 + z * ((-3) + z * (116 + z * (175 + z * (85 + z * (44 + z * (63 + z * ((-67) + z * (127 + z * ((-3) + z * (75 + z * (88 + z * ((-106) + z * ((-64) + z * (88 + z * ((-83) + z * ((-68) + z * ((-124) + z * ((-53) + z * (26 + z * (0 + z * ((-81) + z * ((-30) + z * ((-104) + z * ((-23) + z * (29 + z * (8 + z * (11 + z * ((-1) + z * ((-23) + z * 7))))))))))))))))))))))))))))))))))))))


def pow16_16 {R : Type*} [CommRing R] (z : R) : R := (75 + z * (4 + z * (114 + z * (95 + z * (48 + z * (95 + z * (20 + z * (45 + z * (5 + z * (5 + z * (120 + z * (111 + z * (96 + z * (91 + z * (38 + z * (61 + z * (87 + z * (15 + z * (89 + z * 65)))))))))))))))))))

def pow16_16_q {R : Type*} [CommRing R] (z : R) : R := (59 + z * (123 + z * (115 + z * (105 + z * (76 + z * (114 + z * (95 + z * (99 + z * (22 + z * (124 + z * (94 + z * (13 + z * (110 + z * (70 + z * (43 + z * (99 + z * (77 + z * (22 + z * 89))))))))))))))))))

def pow16_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (21 + z * (27 + z * (45 + z * ((-1) + z * ((-39) + z * ((-177) + z * ((-121) + z * ((-93) + z * (39 + z * ((-78) + z * ((-36) + z * ((-99) + z * ((-19) + z * ((-116) + z * ((-148) + z * ((-47) + z * (74 + z * (19 + z * (143 + z * (170 + z * ((-41) + z * (28 + z * (36 + z * (113 + z * (204 + z * (259 + z * (208 + z * (265 + z * (157 + z * (164 + z * (191 + z * (80 + z * (169 + z * (191 + z * (152 + z * (144 + z * (116 + z * (40 + z * 25))))))))))))))))))))))))))))))))))))))


def pow16_32 {R : Type*} [CommRing R] (z : R) : R := (127 + z * (98 + z * (25 + z * (87 + z * (17 + z * (5 + z * (43 + z * (44 + z * (12 + z * (19 + z * (116 + z * (12 + z * (26 + z * (109 + z * (38 + z * (122 + z * (73 + z * (11 + z * (75 + z * 68)))))))))))))))))))

def pow16_32_q {R : Type*} [CommRing R] (z : R) : R := (89 + z * (60 + z * (106 + z * (16 + z * (25 + z * (41 + z * (8 + z * (104 + z * (8 + z * (22 + z * (58 + z * (93 + z * (52 + z * (103 + z * (52 + z * (9 + z * (84 + z * (91 + z * 33))))))))))))))))))

def pow16_32_mul_t {R : Type*} [CommRing R] (z : R) : R := (8 + z * ((-51) + z * (25 + z * (26 + z * (34 + z * (116 + z * (37 + z * (71 + z * (18 + z * ((-64) + z * (76 + z * ((-76) + z * (52 + z * (134 + z * (135 + z * (231 + z * (179 + z * (109 + z * (47 + z * ((-16) + z * (107 + z * (198 + z * (134 + z * (215 + z * (56 + z * (42 + z * (127 + z * (75 + z * (134 + z * (137 + z * (115 + z * (162 + z * (52 + z * (9 + z * (82 + z * (11 + z * (14 + z * (71 + z * 32))))))))))))))))))))))))))))))))))))))


def pow16_64 {R : Type*} [CommRing R] (z : R) : R := (53 + z * (103 + z * (69 + z * (106 + z * (23 + z * (57 + z * (8 + z * (43 + z * (86 + z * (22 + z * (11 + z * (2 + z * (129 + z * (44 + z * (45 + z * (4 + z * (74 + z * (21 + z * (102 + z * 42)))))))))))))))))))

def pow16_64_q {R : Type*} [CommRing R] (z : R) : R := (70 + z * (92 + z * (8 + z * (45 + z * (12 + z * (64 + z * (18 + z * (10 + z * (49 + z * (42 + z * (105 + z * (73 + z * (19 + z * (96 + z * (18 + z * (110 + z * (90 + z * (28 + z * 39))))))))))))))))))

def pow16_64_mul_t {R : Type*} [CommRing R] (z : R) : R := (96 + z * (129 + z * (51 + z * (128 + z * (89 + z * ((-95) + z * (26 + z * (60 + z * ((-77) + z * ((-61) + z * (104 + z * (0 + z * ((-160) + z * (103 + z * (9 + z * (53 + z * (176 + z * ((-88) + z * ((-49) + z * (93 + z * ((-65) + z * ((-140) + z * ((-62) + z * ((-66) + z * ((-163) + z * (108 + z * ((-32) + z * ((-144) + z * (108 + z * (58 + z * (45 + z * (112 + z * (51 + z * (69 + z * (79 + z * (15 + z * (22 + z * (58 + z * 35))))))))))))))))))))))))))))))))))))))


def pow16_65 {R : Type*} [CommRing R] (z : R) : R := (124 + z * (12 + z * (82 + z * (12 + z * (13 + z * (106 + z * (129 + z * (64 + z * (117 + z * (97 + z * (105 + z * (41 + z * (73 + z * (24 + z * (85 + z * (5 + z * (3 + z * (98 + z * (115 + z * 100)))))))))))))))))))

def pow16_65_q {R : Type*} [CommRing R] (z : R) : R := (110 + z * (124 + z * (63 + z * (110 + z * (3 + z * (124 + z * (99 + z * (101 + z * (27 + z * (93 + z * (10 + z * (81 + z * (9 + z * (81 + z * (91 + z * (18 + z * (55 + z * (80 + z * 48))))))))))))))))))

def pow16_65_mul_t {R : Type*} [CommRing R] (z : R) : R := (4 + z * (29 + z * (25 + z * (101 + z * (96 + z * (14 + z * (8 + z * ((-24) + z * ((-98) + z * ((-87) + z * ((-189) + z * ((-196) + z * ((-122) + z * ((-182) + z * ((-124) + z * ((-52) + z * ((-71) + z * ((-194) + z * ((-144) + z * ((-159) + z * ((-12) + z * ((-110) + z * ((-159) + z * ((-112) + z * ((-143) + z * ((-126) + z * ((-132) + z * ((-17) + z * ((-87) + z * ((-7) + z * ((-59) + z * (127 + z * ((-14) + z * ((-11) + z * ((-14) + z * (32 + z * ((-5) + z * (44 + z * 24))))))))))))))))))))))))))))))))))))))


def pow16_130 {R : Type*} [CommRing R] (z : R) : R := (59 + z * (94 + z * (58 + z * (28 + z * (6 + z * (72 + z * (77 + z * (115 + z * (65 + z * (54 + z * (94 + z * (53 + z * (18 + z * (94 + z * (130 + z * (9 + z * (11 + z * (50 + z * (83 + z * 76)))))))))))))))))))

def pow16_130_q {R : Type*} [CommRing R] (z : R) : R := (26 + z * (7 + z * (83 + z * (2 + z * (38 + z * (26 + z * (49 + z * (91 + z * (88 + z * (32 + z * (38 + z * (91 + z * (88 + z * (76 + z * (60 + z * (103 + z * (7 + z * (53 + z * 44))))))))))))))))))

def pow16_130_mul_t {R : Type*} [CommRing R] (z : R) : R := (107 + z * (10 + z * (109 + z * ((-1) + z * (7 + z * (152 + z * (182 + z * (120 + z * (273 + z * (125 + z * (280 + z * (209 + z * (253 + z * (101 + z * (381 + z * (124 + z * (194 + z * (271 + z * (280 + z * (304 + z * (164 + z * (99 + z * (99 + z * (170 + z * (288 + z * (207 + z * (171 + z * (249 + z * (186 + z * (106 + z * ((-12) + z * (81 + z * (67 + z * (16 + z * ((-18) + z * (132 + z * (204 + z * (153 + z * 76))))))))))))))))))))))))))))))))))))))


def pow16_131 {R : Type*} [CommRing R] (z : R) : R := (33 + z * (76 + z * (6 + z * (87 + z * (54 + z * (118 + z * (49 + z * (49 + z * (77 + z * (5 + z * (57 + z * (71 + z * (113 + z * (81 + z * (28 + z * (62 + z * (53 + z * (117 + z * (28 + z * 15)))))))))))))))))))

def pow16_131_q {R : Type*} [CommRing R] (z : R) : R := (55 + z * (22 + z * (46 + z * (87 + z * (118 + z * (22 + z * (76 + z * (66 + z * (6 + z * (3 + z * (16 + z * (44 + z * (10 + z * (53 + z * (32 + z * (116 + z * (40 + z * (67 + z * 12))))))))))))))))))

def pow16_131_mul_t {R : Type*} [CommRing R] (z : R) : R := (31 + z * (82 + z * (86 + z * (99 + z * (54 + z * (62 + z * (85 + z * (107 + z * (46 + z * (119 + z * (197 + z * (82 + z * (91 + z * (240 + z * (243 + z * (22 + z * (120 + z * (135 + z * (163 + z * (137 + z * (189 + z * (174 + z * (60 + z * (86 + z * (126 + z * (137 + z * (91 + z * (134 + z * (23 + z * (90 + z * (95 + z * (86 + z * (79 + z * (25 + z * ((-14) + z * (29 + z * (48 + z * (59 + z * 44))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod131Powers09
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131
def pow17_2 {R : Type*} [CommRing R] (z : R) : R := (48 + z * (53 + z * (19 + z * (102 + z * (43 + z * (109 + z * (104 + z * (86 + z * (104 + z * (44 + z * (60 + z * (113 + z * (32 + z * (124 + z * (53 + z * (7 + z * (11 + z * (117 + z * (33 + z * 61)))))))))))))))))))

def pow17_2_q {R : Type*} [CommRing R] (z : R) : R := (123 + z * (57 + z * (64 + z * (54 + z * (99 + z * (45 + z * (56 + z * (98 + z * (47 + z * (42 + z * (106 + z * (82 + z * (35 + z * (19 + z * (103 + z * (50 + z * (120 + z * (7 + z * 94))))))))))))))))))

def pow17_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-39) + z * ((-28) + z * ((-58) + z * ((-43) + z * ((-37) + z * ((-99) + z * (42 + z * ((-85) + z * ((-36) + z * ((-72) + z * ((-31) + z * ((-105) + z * ((-153) + z * (11 + z * ((-84) + z * ((-92) + z * ((-30) + z * (42 + z * ((-5) + z * ((-166) + z * (49 + z * ((-50) + z * (17 + z * ((-89) + z * (60 + z * (10 + z * ((-129) + z * ((-66) + z * (67 + z * (31 + z * (43 + z * ((-27) + z * (2 + z * ((-23) + z * ((-3) + z * ((-37) + z * ((-14) + z * ((-41) + z * 1))))))))))))))))))))))))))))))))))))))


def pow17_4 {R : Type*} [CommRing R] (z : R) : R := (31 + z * (13 + z * (110 + z * (93 + z * (0 + z * (111 + z * (55 + z * (19 + z * (50 + z * (29 + z * (18 + z * (102 + z * (70 + z * (90 + z * (117 + z * (56 + z * (21 + z * (54 + z * (125 + z * 119)))))))))))))))))))

def pow17_4_q {R : Type*} [CommRing R] (z : R) : R := (90 + z * (30 + z * (44 + z * (100 + z * (1 + z * (115 + z * (19 + z * (22 + z * (16 + z * (67 + z * (48 + z * (19 + z * (110 + z * (77 + z * (113 + z * (114 + z * (51 + z * (4 + z * 53))))))))))))))))))

def pow17_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-17) + z * ((-5) + z * ((-37) + z * (5 + z * (5 + z * ((-52) + z * (138 + z * (33 + z * (143 + z * (181 + z * (127 + z * (266 + z * (188 + z * (221 + z * (232 + z * (153 + z * (170 + z * (159 + z * (201 + z * (193 + z * (177 + z * (97 + z * (205 + z * (73 + z * (239 + z * (125 + z * (22 + z * (37 + z * (40 + z * ((-46) + z * (118 + z * ((-65) + z * ((-15) + z * ((-73) + z * ((-1) + z * (21 + z * (91 + z * (4 + z * 28))))))))))))))))))))))))))))))))))))))


def pow17_8 {R : Type*} [CommRing R] (z : R) : R := (6 + z * (28 + z * (71 + z * (90 + z * (100 + z * (48 + z * (52 + z * (26 + z * (90 + z * (23 + z * (5 + z * (54 + z * (59 + z * (128 + z * (57 + z * (79 + z * (44 + z * (130 + z * (97 + z * 44)))))))))))))))))))

def pow17_8_q {R : Type*} [CommRing R] (z : R) : R := (6 + z * (99 + z * (35 + z * (121 + z * (81 + z * (79 + z * (103 + z * (33 + z * (127 + z * (120 + z * (67 + z * (43 + z * (74 + z * (72 + z * (79 + z * (38 + z * (33 + z * (72 + z * 13))))))))))))))))))

def pow17_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (5 + z * ((-34) + z * (1 + z * ((-43) + z * ((-2) + z * (25 + z * ((-120) + z * (3 + z * ((-55) + z * ((-204) + z * ((-176) + z * ((-134) + z * ((-267) + z * ((-173) + z * ((-141) + z * ((-129) + z * ((-11) + z * ((-113) + z * ((-99) + z * ((-32) + z * (38 + z * (20 + z * ((-31) + z * (78 + z * (126 + z * (25 + z * (83 + z * (103 + z * (85 + z * (183 + z * (257 + z * (268 + z * (307 + z * (216 + z * (94 + z * (87 + z * (175 + z * (220 + z * 108))))))))))))))))))))))))))))))))))))))


def pow17_16 {R : Type*} [CommRing R] (z : R) : R := (10 + z * (13 + z * (58 + z * (85 + z * (110 + z * (130 + z * (55 + z * (56 + z * (9 + z * (74 + z * (83 + z * (114 + z * (48 + z * (103 + z * (32 + z * (92 + z * (32 + z * (52 + z * (104 + z * 60)))))))))))))))))))

def pow17_16_q {R : Type*} [CommRing R] (z : R) : R := (11 + z * (59 + z * (38 + z * (46 + z * (39 + z * (97 + z * (8 + z * (91 + z * (28 + z * (102 + z * (110 + z * (130 + z * (88 + z * (105 + z * (32 + z * (101 + z * (43 + z * (101 + z * 102))))))))))))))))))

def pow17_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-4) + z * ((-24) + z * ((-29) + z * ((-24) + z * (19 + z * (22 + z * (58 + z * (57 + z * (52 + z * ((-39) + z * ((-37) + z * ((-58) + z * ((-169) + z * ((-191) + z * ((-166) + z * ((-87) + z * ((-48) + z * ((-44) + z * ((-153) + z * (46 + z * ((-26) + z * (130 + z * ((-113) + z * ((-138) + z * ((-115) + z * ((-36) + z * ((-66) + z * ((-72) + z * ((-80) + z * ((-57) + z * (141 + z * (147 + z * (174 + z * (69 + z * (72 + z * (116 + z * (62 + z * (13 + z * 14))))))))))))))))))))))))))))))))))))))


def pow17_32 {R : Type*} [CommRing R] (z : R) : R := (117 + z * (25 + z * (26 + z * (42 + z * (111 + z * (3 + z * (52 + z * (49 + z * (7 + z * (52 + z * (69 + z * (13 + z * (101 + z * (105 + z * (124 + z * (86 + z * (24 + z * (1 + z * (36 + z * 5)))))))))))))))))))

def pow17_32_q {R : Type*} [CommRing R] (z : R) : R := (18 + z * (69 + z * (22 + z * (98 + z * (70 + z * (76 + z * (85 + z * (16 + z * (64 + z * (10 + z * (89 + z * (24 + z * (53 + z * (49 + z * (46 + z * (27 + z * (8 + z * (69 + z * 63))))))))))))))))))

def pow17_32_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-7) + z * ((-31) + z * ((-32) + z * ((-58) + z * ((-36) + z * ((-42) + z * (3 + z * (108 + z * (63 + z * (127 + z * (44 + z * (27 + z * (14 + z * (76 + z * (153 + z * (210 + z * (256 + z * (146 + z * (210 + z * (121 + z * (338 + z * (234 + z * (313 + z * (289 + z * (311 + z * (126 + z * (160 + z * (175 + z * (270 + z * (163 + z * (168 + z * (151 + z * (142 + z * (99 + z * (71 + z * (53 + z * (67 + z * (63 + z * 27))))))))))))))))))))))))))))))))))))))


def pow17_64 {R : Type*} [CommRing R] (z : R) : R := (2 + z * (53 + z * (57 + z * (30 + z * (79 + z * (57 + z * (109 + z * (91 + z * (65 + z * (18 + z * (88 + z * (88 + z * (106 + z * (9 + z * (87 + z * (80 + z * (66 + z * (53 + z * (47 + z * 41)))))))))))))))))))

def pow17_64_q {R : Type*} [CommRing R] (z : R) : R := (72 + z * (119 + z * (5 + z * (3 + z * (64 + z * (38 + z * (102 + z * (1 + z * (25 + z * (98 + z * (37 + z * (95 + z * (122 + z * (34 + z * (116 + z * (27 + z * (83 + z * (20 + z * 25))))))))))))))))))

def pow17_64_mul_t {R : Type*} [CommRing R] (z : R) : R := (77 + z * ((-27) + z * ((-29) + z * (11 + z * (131 + z * ((-103) + z * ((-41) + z * (66 + z * ((-75) + z * ((-111) + z * (50 + z * ((-150) + z * ((-75) + z * ((-16) + z * (32 + z * (54 + z * ((-39) + z * ((-187) + z * (9 + z * ((-107) + z * ((-171) + z * ((-138) + z * ((-92) + z * ((-164) + z * ((-48) + z * ((-77) + z * (62 + z * (25 + z * (46 + z * ((-33) + z * ((-72) + z * ((-79) + z * ((-60) + z * ((-65) + z * ((-56) + z * ((-58) + z * ((-12) + z * ((-10) + z * 0))))))))))))))))))))))))))))))))))))))


def pow17_65 {R : Type*} [CommRing R] (z : R) : R := (121 + z * (18 + z * (22 + z * (51 + z * (75 + z * (34 + z * (43 + z * (71 + z * (71 + z * (89 + z * (48 + z * (104 + z * (79 + z * (114 + z * (38 + z * (100 + z * (42 + z * (42 + z * (25 + z * 86)))))))))))))))))))

def pow17_65_q {R : Type*} [CommRing R] (z : R) : R := (12 + z * (29 + z * (2 + z * (0 + z * (44 + z * (114 + z * (86 + z * (16 + z * (105 + z * (91 + z * (10 + z * (72 + z * (57 + z * (17 + z * (25 + z * (39 + z * (13 + z * (39 + z * 91))))))))))))))))))

def pow17_65_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-5) + z * ((-1) + z * (28 + z * (27 + z * (46 + z * (37 + z * (34 + z * (116 + z * (57 + z * (53 + z * (17 + z * (129 + z * (98 + z * (10 + z * (112 + z * (231 + z * (60 + z * (121 + z * (231 + z * (215 + z * (134 + z * (150 + z * (163 + z * (153 + z * (126 + z * (67 + z * (70 + z * (129 + z * (123 + z * (122 + z * (45 + z * (100 + z * (119 + z * (52 + z * (9 + z * (19 + z * ((-8) + z * ((-32) + z * 4))))))))))))))))))))))))))))))))))))))


def pow17_130 {R : Type*} [CommRing R] (z : R) : R := (60 + z * (90 + z * (29 + z * (14 + z * (34 + z * (125 + z * (5 + z * (4 + z * (79 + z * (86 + z * (4 + z * (86 + z * (39 + z * (124 + z * (14 + z * (7 + z * (1 + z * (57 + z * (55 + z * 84)))))))))))))))))))

def pow17_130_q {R : Type*} [CommRing R] (z : R) : R := (27 + z * (94 + z * (34 + z * (6 + z * (71 + z * (23 + z * (79 + z * (21 + z * (104 + z * (28 + z * (119 + z * (104 + z * (122 + z * (23 + z * (124 + z * (40 + z * (78 + z * (78 + z * 60))))))))))))))))))

def pow17_130_mul_t {R : Type*} [CommRing R] (z : R) : R := (101 + z * ((-13) + z * ((-17) + z * (35 + z * (79 + z * ((-18) + z * ((-41) + z * (104 + z * (29 + z * (32 + z * (5 + z * (106 + z * ((-5) + z * (62 + z * ((-3) + z * (115 + z * (21 + z * ((-18) + z * (14 + z * (38 + z * (45 + z * ((-7) + z * (54 + z * (8 + z * (111 + z * ((-14) + z * (112 + z * ((-5) + z * (86 + z * ((-70) + z * (42 + z * (29 + z * (82 + z * ((-63) + z * (36 + z * ((-26) + z * ((-7) + z * (2 + z * 56))))))))))))))))))))))))))))))))))))))


def pow17_131 {R : Type*} [CommRing R] (z : R) : R := (55 + z * (130 + z * (125 + z * (16 + z * (93 + z * (10 + z * (91 + z * (22 + z * (124 + z * (28 + z * (123 + z * (45 + z * (123 + z * (79 + z * (93 + z * (97 + z * (110 + z * (80 + z * (89 + z * 105)))))))))))))))))))

def pow17_131_q {R : Type*} [CommRing R] (z : R) : R := (104 + z * (45 + z * (35 + z * (22 + z * (101 + z * (24 + z * (18 + z * (17 + z * (13 + z * (26 + z * (29 + z * (102 + z * (129 + z * (4 + z * (51 + z * (24 + z * (79 + z * (58 + z * 81))))))))))))))))))

def pow17_131_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-25) + z * (2 + z * ((-19) + z * (3 + z * ((-26) + z * ((-15) + z * (71 + z * ((-21) + z * (9 + z * (1 + z * (103 + z * ((-46) + z * ((-3) + z * (59 + z * (107 + z * ((-25) + z * (2 + z * (37 + z * (102 + z * ((-84) + z * ((-28) + z * (51 + z * (34 + z * ((-81) + z * (70 + z * (55 + z * (72 + z * ((-87) + z * ((-52) + z * ((-55) + z * (24 + z * ((-10) + z * (7 + z * ((-56) + z * ((-9) + z * ((-1) + z * (27 + z * ((-17) + z * 9))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod131

end

end OAI
end


