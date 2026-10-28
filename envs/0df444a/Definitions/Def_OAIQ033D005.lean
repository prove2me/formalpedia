-- Prove2me | Definitions.Def_OAIQ033D005
-- name    : OAIQ033D005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T01:46:40.509577+00:00
-- url     : https://prove2.me/theorems/45c367c3-0931-4b93-bd6b-7dd4ff590b50
-- title:
--   Definitions bundle OAIQ033D005 of the split of OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DimensionTen.main_pair`, carved from OpenAI's openai/math development (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 173 declarations of OpenAI's Lean: 173 definitions. The definitions and types are `OAI.DimensionTen.Mod131.pow2_4`, `OAI.DimensionTen.Mod131.pow2_4_mul_t`, `OAI.DimensionTen.Mod131.pow2_4_q`, `OAI.DimensionTen.Mod131.pow2_64`, `OAI.DimensionTen.Mod131.pow2_64_mul_t`, `OAI.DimensionTen.Mod131.pow2_64_q`, `OAI.DimensionTen.Mod131.pow2_65`, `OAI.DimensionTen.Mod131.pow2_65_mul_t`, `OAI.DimensionTen.Mod131.pow2_65_q`, `OAI.DimensionTen.Mod131.pow2_8`, `OAI.DimensionTen.Mod131.pow2_8_mul_t`, `OAI.DimensionTen.Mod131.pow2_8_q`, `OAI.DimensionTen.Mod131.pow3_130`, `OAI.DimensionTen.Mod131.pow3_130_mul_t`, `OAI.DimensionTen.Mod131.pow3_130_q`, `OAI.DimensionTen.Mod131.pow3_131`, `OAI.DimensionTen.Mod131.pow3_131_mul_t`, `OAI.DimensionTen.Mod131.pow3_131_q`, `OAI.DimensionTen.Mod131.pow3_16`, `OAI.DimensionTen.Mod131.pow3_16_mul_t`, `OAI.DimensionTen.Mod131.pow3_16_q`, `OAI.DimensionTen.Mod131.pow3_2`, `OAI.DimensionTen.Mod131.pow3_2_mul_t`, `OAI.DimensionTen.Mod131.pow3_2_q`, `OAI.DimensionTen.Mod131.pow3_32`, `OAI.DimensionTen.Mod131.pow3_32_mul_t`, `OAI.DimensionTen.Mod131.pow3_32_q`, `OAI.DimensionTen.Mod131.pow3_4`, `OAI.DimensionTen.Mod131.pow3_4_mul_t`, `OAI.DimensionTen.Mod131.pow3_4_q`, `OAI.DimensionTen.Mod131.pow3_64`, `OAI.DimensionTen.Mod131.pow3_64_mul_t`, `OAI.DimensionTen.Mod131.pow3_64_q`, `OAI.DimensionTen.Mod131.pow3_65`, `OAI.DimensionTen.Mod131.pow3_65_mul_t`, `OAI.DimensionTen.Mod131.pow3_65_q`, `OAI.DimensionTen.Mod131.pow3_8`, `OAI.DimensionTen.Mod131.pow3_8_mul_t`, `OAI.DimensionTen.Mod131.pow3_8_q`, `OAI.DimensionTen.Mod131.pow4_130` and 133 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Quantum/DimensionTen, in whole or in part: [`Quantum_DimensionTen_Mod131Powers01`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod131Powers01.lean), [`Quantum_DimensionTen_Mod131Powers02`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod131Powers02.lean), [`Quantum_DimensionTen_Mod131Powers03`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod131Powers03.lean), [`Quantum_DimensionTen_Mod131Powers04`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod131Powers04.lean), [`Quantum_DimensionTen_Mod139Powers01`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod139Powers01.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ033D013`; the statement `OAI_DimensionTen_veronese_family_general_position`; the proofs of `OAI_DimensionTen_Mod139_iterate11`, `OAI_DimensionTen_exists_nineteen_cycle_of_mod139` and `OAI_DimensionTen_veronese_family_general_position`.
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


def pow2_4 {R : Type*} [CommRing R] (z : R) : R := (112 + z * (128 + z * (91 + z * (123 + z * (130 + z * (26 + z * (98 + z * (77 + z * (26 + z * (11 + z * (32 + z * (27 + z * (49 + z * (108 + z * (110 + z * (70 + z * (91 + z * (3 + z * (110 + z * 119)))))))))))))))))))

def pow2_4_q {R : Type*} [CommRing R] (z : R) : R := (32 + z * (11 + z * (40 + z * (101 + z * (60 + z * (27 + z * (72 + z * (97 + z * (15 + z * (84 + z * (39 + z * (116 + z * (10 + z * (97 + z * (54 + z * (125 + z * (13 + z * (45 + z * 102))))))))))))))))))

def pow2_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-13) + z * ((-14) + z * ((-4) + z * (53 + z * (114 + z * (95 + z * (90 + z * (44 + z * ((-36) + z * ((-75) + z * (66 + z * (33 + z * (199 + z * (217 + z * (243 + z * (103 + z * (155 + z * (202 + z * (187 + z * (54 + z * (79 + z * (271 + z * (3 + z * (33 + z * (220 + z * (180 + z * (39 + z * (137 + z * (144 + z * (47 + z * ((-3) + z * (3 + z * (42 + z * ((-67) + z * ((-77) + z * (10 + z * ((-56) + z * ((-43) + z * 14))))))))))))))))))))))))))))))))))))))


def pow2_8 {R : Type*} [CommRing R] (z : R) : R := (52 + z * (4 + z * (69 + z * (70 + z * (31 + z * (129 + z * (80 + z * (125 + z * (93 + z * (61 + z * (94 + z * (68 + z * (83 + z * (55 + z * (3 + z * (56 + z * (72 + z * (6 + z * (76 + z * 45)))))))))))))))))))

def pow2_8_q {R : Type*} [CommRing R] (z : R) : R := (35 + z * (61 + z * (24 + z * (84 + z * (126 + z * (64 + z * (34 + z * (31 + z * (100 + z * (69 + z * (39 + z * (58 + z * (55 + z * (115 + z * (110 + z * (37 + z * (41 + z * (39 + z * 13))))))))))))))))))

def pow2_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (82 + z * (183 + z * (232 + z * (311 + z * (406 + z * (290 + z * (335 + z * (439 + z * (230 + z * (109 + z * (193 + z * (49 + z * ((-43) + z * (90 + z * (254 + z * (211 + z * (278 + z * (296 + z * (351 + z * (487 + z * (401 + z * (187 + z * (276 + z * (121 + z * ((-21) + z * (93 + z * (94 + z * (47 + z * (117 + z * (137 + z * (113 + z * (206 + z * (287 + z * (204 + z * (219 + z * (127 + z * (72 + z * (193 + z * 108))))))))))))))))))))))))))))))))))))))


def pow2_64 {R : Type*} [CommRing R] (z : R) : R := (66 + z * (16 + z * (38 + z * (15 + z * (112 + z * (38 + z * (117 + z * (66 + z * (51 + z * (81 + z * (91 + z * (83 + z * (92 + z * (110 + z * (75 + z * (50 + z * (109 + z * (9 + z * (52 + z * 77)))))))))))))))))))

def pow2_64_q {R : Type*} [CommRing R] (z : R) : R := (77 + z * (2 + z * (5 + z * (58 + z * (8 + z * (39 + z * (114 + z * (6 + z * (7 + z * (48 + z * (60 + z * (43 + z * (98 + z * (18 + z * (5 + z * (122 + z * (122 + z * (112 + z * 61))))))))))))))))))

def pow2_64_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * (27 + z * (89 + z * (113 + z * (31 + z * ((-41) + z * (79 + z * (112 + z * (40 + z * ((-25) + z * ((-43) + z * ((-12) + z * (271 + z * (33 + z * ((-49) + z * (33 + z * (139 + z * ((-49) + z * ((-48) + z * ((-182) + z * (90 + z * ((-29) + z * ((-72) + z * ((-203) + z * ((-107) + z * (67 + z * ((-81) + z * ((-107) + z * ((-140) + z * ((-88) + z * (65 + z * ((-49) + z * ((-102) + z * (17 + z * ((-151) + z * ((-45) + z * ((-27) + z * ((-18) + z * 60))))))))))))))))))))))))))))))))))))))


def pow2_65 {R : Type*} [CommRing R] (z : R) : R := (71 + z * (21 + z * (125 + z * (11 + z * (70 + z * (118 + z * (103 + z * (44 + z * (71 + z * (111 + z * (34 + z * (94 + z * (39 + z * (95 + z * (72 + z * (67 + z * (108 + z * (24 + z * (112 + z * 57)))))))))))))))))))

def pow2_65_q {R : Type*} [CommRing R] (z : R) : R := (58 + z * (26 + z * (109 + z * (46 + z * (112 + z * (68 + z * (76 + z * (87 + z * (94 + z * (128 + z * (72 + z * (10 + z * (27 + z * (2 + z * (75 + z * (89 + z * (75 + z * (33 + z * 91))))))))))))))))))

def pow2_65_mul_t {R : Type*} [CommRing R] (z : R) : R := (1 + z * ((-5) + z * ((-35) + z * ((-33) + z * ((-46) + z * ((-40) + z * ((-41) + z * ((-56) + z * ((-71) + z * ((-64) + z * ((-78) + z * ((-10) + z * ((-39) + z * ((-9) + z * (0 + z * (3 + z * (93 + z * (6 + z * (72 + z * ((-1) + z * ((-3) + z * (62 + z * (28 + z * (91 + z * (105 + z * (53 + z * ((-8) + z * ((-8) + z * (98 + z * (35 + z * (101 + z * (18 + z * (26 + z * ((-20) + z * ((-89) + z * (9 + z * ((-11) + z * ((-35) + z * 14))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod131Powers02
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131
def pow3_2 {R : Type*} [CommRing R] (z : R) : R := (75 + z * (39 + z * (20 + z * (18 + z * (122 + z * (2 + z * (109 + z * (115 + z * (82 + z * (19 + z * (87 + z * (123 + z * (29 + z * (90 + z * (0 + z * (85 + z * (93 + z * (124 + z * (88 + z * 67)))))))))))))))))))

def pow3_2_q {R : Type*} [CommRing R] (z : R) : R := (121 + z * (17 + z * (55 + z * (80 + z * (85 + z * (48 + z * (79 + z * (2 + z * (8 + z * (99 + z * (72 + z * (38 + z * (62 + z * (87 + z * (25 + z * (19 + z * (60 + z * (6 + z * 4))))))))))))))))))

def pow3_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-44) + z * ((-18) + z * (28 + z * (70 + z * (78 + z * ((-1) + z * (66 + z * (77 + z * (75 + z * (186 + z * (246 + z * (22 + z * (149 + z * (65 + z * (30 + z * (213 + z * (120 + z * (113 + z * (242 + z * (371 + z * (480 + z * (348 + z * (319 + z * (323 + z * (306 + z * (390 + z * (431 + z * (318 + z * (253 + z * (141 + z * (223 + z * (224 + z * (209 + z * (300 + z * (225 + z * (251 + z * (299 + z * (252 + z * 127))))))))))))))))))))))))))))))))))))))


def pow3_4 {R : Type*} [CommRing R] (z : R) : R := (125 + z * (52 + z * (70 + z * (36 + z * (14 + z * (21 + z * (64 + z * (101 + z * (75 + z * (130 + z * (49 + z * (113 + z * (97 + z * (63 + z * (96 + z * (56 + z * (117 + z * (120 + z * (94 + z * 90)))))))))))))))))))

def pow3_4_q {R : Type*} [CommRing R] (z : R) : R := (110 + z * (44 + z * (30 + z * (7 + z * (52 + z * (90 + z * (50 + z * (46 + z * (82 + z * (54 + z * (127 + z * (18 + z * (27 + z * (102 + z * (4 + z * (15 + z * (0 + z * (50 + z * 35))))))))))))))))))

def pow3_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * ((-12) + z * ((-47) + z * ((-22) + z * (49 + z * ((-101) + z * (31 + z * (52 + z * (79 + z * ((-132) + z * (89 + z * (126 + z * (6 + z * ((-8) + z * (160 + z * (144 + z * (90 + z * (305 + z * (123 + z * (350 + z * (197 + z * (268 + z * (310 + z * (468 + z * (369 + z * (307 + z * (315 + z * (315 + z * (331 + z * (222 + z * (271 + z * (177 + z * (244 + z * (238 + z * (280 + z * (226 + z * (145 + z * (72 + z * 34))))))))))))))))))))))))))))))))))))))


def pow3_8 {R : Type*} [CommRing R] (z : R) : R := (16 + z * (129 + z * (2 + z * (4 + z * (35 + z * (125 + z * (121 + z * (23 + z * (32 + z * (70 + z * (78 + z * (85 + z * (127 + z * (32 + z * (96 + z * (58 + z * (64 + z * (24 + z * (71 + z * 4)))))))))))))))))))

def pow3_8_q {R : Type*} [CommRing R] (z : R) : R := (79 + z * (5 + z * (86 + z * (105 + z * (8 + z * (110 + z * (2 + z * (130 + z * (67 + z * (61 + z * (77 + z * (54 + z * (24 + z * (101 + z * (89 + z * (96 + z * (16 + z * (32 + z * 109))))))))))))))))))

def pow3_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (89 + z * (68 + z * (81 + z * (37 + z * ((-34) + z * ((-94) + z * (48 + z * ((-6) + z * (52 + z * (193 + z * (11 + z * (122 + z * (76 + z * (87 + z * (141 + z * (68 + z * (230 + z * (384 + z * (284 + z * (341 + z * (277 + z * (249 + z * (189 + z * (325 + z * (414 + z * (493 + z * (355 + z * (440 + z * (509 + z * (306 + z * (353 + z * (275 + z * (279 + z * (280 + z * (215 + z * (269 + z * (167 + z * (74 + z * 61))))))))))))))))))))))))))))))))))))))


def pow3_16 {R : Type*} [CommRing R] (z : R) : R := (19 + z * (50 + z * (108 + z * (129 + z * (49 + z * (2 + z * (71 + z * (28 + z * (33 + z * (54 + z * (24 + z * (4 + z * (65 + z * (128 + z * (120 + z * (22 + z * (51 + z * (64 + z * (35 + z * 67)))))))))))))))))))

def pow3_16_q {R : Type*} [CommRing R] (z : R) : R := (65 + z * (65 + z * (130 + z * (37 + z * (117 + z * (60 + z * (66 + z * (108 + z * (29 + z * (84 + z * (78 + z * (27 + z * (73 + z * (11 + z * (105 + z * (121 + z * (79 + z * (36 + z * 16))))))))))))))))))

def pow3_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-23) + z * ((-17) + z * (22 + z * ((-100) + z * ((-152) + z * ((-98) + z * (38 + z * ((-34) + z * ((-201) + z * ((-233) + z * (6 + z * (10 + z * ((-77) + z * ((-54) + z * ((-174) + z * (2 + z * (11 + z * (24 + z * ((-66) + z * ((-15) + z * ((-62) + z * (11 + z * (16 + z * (22 + z * (155 + z * ((-31) + z * (26 + z * (6 + z * (42 + z * (53 + z * (84 + z * ((-60) + z * ((-3) + z * ((-73) + z * ((-44) + z * ((-33) + z * (14 + z * ((-4) + z * 0))))))))))))))))))))))))))))))))))))))


def pow3_32 {R : Type*} [CommRing R] (z : R) : R := (36 + z * (71 + z * (12 + z * (111 + z * (75 + z * (102 + z * (33 + z * (31 + z * (18 + z * (56 + z * (12 + z * (22 + z * (54 + z * (125 + z * (57 + z * (130 + z * (65 + z * (55 + z * (62 + z * 94)))))))))))))))))))

def pow3_32_q {R : Type*} [CommRing R] (z : R) : R := (72 + z * (113 + z * (109 + z * (84 + z * (60 + z * (27 + z * (9 + z * (90 + z * (126 + z * (128 + z * (87 + z * (42 + z * (18 + z * (101 + z * (56 + z * (50 + z * (127 + z * (22 + z * 35))))))))))))))))))

def pow3_32_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-25) + z * ((-55) + z * ((-67) + z * ((-20) + z * (36 + z * (34 + z * (14 + z * ((-80) + z * ((-142) + z * ((-154) + z * ((-159) + z * ((-212) + z * ((-258) + z * ((-323) + z * ((-215) + z * ((-21) + z * (28 + z * ((-95) + z * ((-257) + z * ((-134) + z * ((-165) + z * ((-201) + z * ((-26) + z * ((-112) + z * ((-243) + z * ((-119) + z * ((-49) + z * ((-42) + z * ((-24) + z * ((-45) + z * (100 + z * (103 + z * (50 + z * (61 + z * ((-33) + z * ((-1) + z * (47 + z * (18 + z * 34))))))))))))))))))))))))))))))))))))))


def pow3_64 {R : Type*} [CommRing R] (z : R) : R := (123 + z * (70 + z * (87 + z * (100 + z * (13 + z * (65 + z * (19 + z * (78 + z * (25 + z * (23 + z * (80 + z * (126 + z * (44 + z * (99 + z * (84 + z * (99 + z * (25 + z * (116 + z * (119 + z * 129)))))))))))))))))))

def pow3_64_q {R : Type*} [CommRing R] (z : R) : R := (68 + z * (126 + z * (110 + z * (6 + z * (7 + z * (34 + z * (56 + z * (31 + z * (2 + z * (32 + z * (107 + z * (113 + z * (121 + z * (110 + z * (120 + z * (49 + z * (10 + z * (33 + z * 59))))))))))))))))))

def pow3_64_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-17) + z * ((-34) + z * ((-76) + z * ((-42) + z * (45 + z * ((-8) + z * (28 + z * (11 + z * (90 + z * ((-17) + z * ((-27) + z * ((-142) + z * ((-142) + z * ((-199) + z * ((-148) + z * ((-117) + z * (102 + z * ((-50) + z * (48 + z * (15 + z * (129 + z * ((-5) + z * (53 + z * ((-76) + z * (33 + z * ((-123) + z * ((-53) + z * (17 + z * (141 + z * ((-18) + z * (69 + z * (145 + z * (227 + z * (134 + z * (190 + z * (103 + z * (65 + z * (59 + z * 67))))))))))))))))))))))))))))))))))))))


def pow3_65 {R : Type*} [CommRing R] (z : R) : R := (60 + z * (32 + z * (98 + z * (58 + z * (82 + z * (34 + z * (4 + z * (116 + z * (28 + z * (129 + z * (127 + z * (111 + z * (52 + z * (39 + z * (71 + z * (17 + z * (86 + z * (44 + z * (83 + z * 18)))))))))))))))))))

def pow3_65_q {R : Type*} [CommRing R] (z : R) : R := (1 + z * (78 + z * (9 + z * (105 + z * (125 + z * (7 + z * (42 + z * (37 + z * (91 + z * (110 + z * (88 + z * (62 + z * (43 + z * (106 + z * (41 + z * (64 + z * (18 + z * (26 + z * 4))))))))))))))))))

def pow3_65_mul_t {R : Type*} [CommRing R] (z : R) : R := (17 + z * (84 + z * (105 + z * (145 + z * (135 + z * (54 + z * (114 + z * (146 + z * (70 + z * (106 + z * (99 + z * (53 + z * (59 + z * (34 + z * (126 + z * (21 + z * (128 + z * (167 + z * (314 + z * (413 + z * (333 + z * (318 + z * (229 + z * (205 + z * (248 + z * (273 + z * (240 + z * (240 + z * (254 + z * (303 + z * (290 + z * (277 + z * (291 + z * (304 + z * (247 + z * (252 + z * (305 + z * (242 + z * 127))))))))))))))))))))))))))))))))))))))


def pow3_130 {R : Type*} [CommRing R] (z : R) : R := (43 + z * (11 + z * (68 + z * (21 + z * (104 + z * (15 + z * (46 + z * (106 + z * (40 + z * (16 + z * (6 + z * (76 + z * (92 + z * (16 + z * (39 + z * (23 + z * (41 + z * (3 + z * (106 + z * 48)))))))))))))))))))

def pow3_130_q {R : Type*} [CommRing R] (z : R) : R := (79 + z * (39 + z * (72 + z * (126 + z * (26 + z * (106 + z * (40 + z * (64 + z * (69 + z * (80 + z * (100 + z * (61 + z * (36 + z * (3 + z * (99 + z * (57 + z * (127 + z * (75 + z * 62))))))))))))))))))

def pow3_130_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-3) + z * ((-14) + z * (17 + z * ((-6) + z * (36 + z * ((-56) + z * (6 + z * ((-38) + z * ((-124) + z * (75 + z * ((-37) + z * (132 + z * (85 + z * (92 + z * (101 + z * ((-57) + z * (22 + z * (27 + z * (121 + z * (27 + z * (193 + z * (52 + z * ((-62) + z * (51 + z * ((-18) + z * (100 + z * (28 + z * (56 + z * (59 + z * ((-23) + z * ((-3) + z * ((-37) + z * ((-7) + z * ((-91) + z * ((-27) + z * ((-42) + z * ((-2) + z * ((-9) + z * 2))))))))))))))))))))))))))))))))))))))


def pow3_131 {R : Type*} [CommRing R] (z : R) : R := (109 + z * (34 + z * (52 + z * (118 + z * (34 + z * (65 + z * (52 + z * (30 + z * (23 + z * (129 + z * (57 + z * (124 + z * (76 + z * (44 + z * (15 + z * (50 + z * (60 + z * (93 + z * (44 + z * 52)))))))))))))))))))

def pow3_131_q {R : Type*} [CommRing R] (z : R) : R := (98 + z * (54 + z * (114 + z * (109 + z * (104 + z * (128 + z * (50 + z * (76 + z * (99 + z * (58 + z * (89 + z * (101 + z * (62 + z * (110 + z * (9 + z * (71 + z * (71 + z * (2 + z * 35))))))))))))))))))

def pow3_131_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-32) + z * ((-18) + z * ((-69) + z * ((-25) + z * ((-102) + z * ((-104) + z * ((-93) + z * ((-131) + z * ((-109) + z * ((-146) + z * ((-143) + z * ((-205) + z * ((-259) + z * ((-239) + z * ((-165) + z * ((-263) + z * ((-297) + z * ((-271) + z * ((-230) + z * ((-110) + z * ((-171) + z * ((-76) + z * ((-73) + z * ((-116) + z * ((-121) + z * (86 + z * (21 + z * ((-45) + z * ((-36) + z * ((-30) + z * (123 + z * (30 + z * (34 + z * (88 + z * (36 + z * (86 + z * (123 + z * (134 + z * 47))))))))))))))))))))))))))))))))))))))


abbrev u3 {R : Type*} [CommRing R] (z : R) : R := pow3_131 z


def pow4_2 {R : Type*} [CommRing R] (z : R) : R := (77 + z * (94 + z * (126 + z * (63 + z * (100 + z * (23 + z * (63 + z * (7 + z * (112 + z * (76 + z * (8 + z * (23 + z * (14 + z * (127 + z * (25 + z * (16 + z * (32 + z * (56 + z * (129 + z * 73)))))))))))))))))))

def pow4_2_q {R : Type*} [CommRing R] (z : R) : R := (16 + z * (37 + z * (27 + z * (27 + z * (62 + z * (100 + z * (126 + z * (4 + z * (79 + z * (21 + z * (52 + z * (10 + z * (6 + z * (42 + z * (42 + z * (55 + z * (62 + z * (80 + z * 84))))))))))))))))))

def pow4_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (84 + z * (36 + z * (63 + z * (182 + z * (76 + z * (107 + z * (87 + z * (36 + z * (20 + z * (159 + z * (18 + z * (203 + z * (289 + z * (84 + z * (219 + z * (183 + z * (147 + z * (76 + z * (156 + z * (153 + z * (274 + z * (120 + z * (137 + z * (37 + z * (53 + z * (4 + z * (112 + z * (128 + z * (211 + z * (50 + z * (73 + z * (12 + z * (15 + z * ((-15) + z * (5 + z * (11 + z * (10 + z * ((-8) + z * 20))))))))))))))))))))))))))))))))))))))


def pow4_4 {R : Type*} [CommRing R] (z : R) : R := (71 + z * (75 + z * (88 + z * (2 + z * (94 + z * (58 + z * (61 + z * (1 + z * (83 + z * (27 + z * (62 + z * (83 + z * (130 + z * (51 + z * (121 + z * (112 + z * (103 + z * (6 + z * (117 + z * 46)))))))))))))))))))

def pow4_4_q {R : Type*} [CommRing R] (z : R) : R := (70 + z * (10 + z * (92 + z * (28 + z * (57 + z * (83 + z * (126 + z * (38 + z * (59 + z * (4 + z * (28 + z * (125 + z * (115 + z * (23 + z * (20 + z * (101 + z * (117 + z * (122 + z * 89))))))))))))))))))

def pow4_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (18 + z * (81 + z * (142 + z * (194 + z * (212 + z * (143 + z * (159 + z * ((-4) + z * (133 + z * (115 + z * (153 + z * ((-30) + z * (5 + z * ((-74) + z * (41 + z * ((-1) + z * ((-155) + z * ((-44) + z * ((-89) + z * ((-3) + z * ((-11) + z * (104 + z * ((-34) + z * ((-294) + z * ((-245) + z * ((-168) + z * (74 + z * ((-47) + z * ((-237) + z * ((-232) + z * ((-125) + z * (60 + z * (37 + z * ((-118) + z * ((-103) + z * ((-2) + z * (87 + z * (98 + z * 40))))))))))))))))))))))))))))))))))))))


def pow4_8 {R : Type*} [CommRing R] (z : R) : R := (120 + z * (20 + z * (92 + z * (36 + z * (99 + z * (72 + z * (51 + z * (73 + z * (123 + z * (49 + z * (18 + z * (23 + z * (115 + z * (64 + z * (12 + z * (103 + z * (88 + z * (25 + z * (125 + z * 104)))))))))))))))))))

def pow4_8_q {R : Type*} [CommRing R] (z : R) : R := (122 + z * (56 + z * (102 + z * (61 + z * (18 + z * (68 + z * (28 + z * (18 + z * (86 + z * (10 + z * (110 + z * (5 + z * (98 + z * (87 + z * (19 + z * (110 + z * (86 + z * (12 + z * 20))))))))))))))))))

def pow4_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-9) + z * (16 + z * (19 + z * ((-6) + z * (8 + z * ((-44) + z * (98 + z * ((-90) + z * ((-11) + z * ((-39) + z * (8 + z * ((-55) + z * (93 + z * ((-21) + z * (179 + z * (92 + z * (327 + z * (56 + z * (202 + z * (156 + z * (301 + z * ((-30) + z * (303 + z * (173 + z * (252 + z * (162 + z * (328 + z * (266 + z * (260 + z * (252 + z * (433 + z * (165 + z * (188 + z * (189 + z * (151 + z * (26 + z * (93 + z * (72 + z * 16))))))))))))))))))))))))))))))))))))))


def pow4_16 {R : Type*} [CommRing R] (z : R) : R := (122 + z * (26 + z * (31 + z * (76 + z * (68 + z * (95 + z * (29 + z * (108 + z * (99 + z * (121 + z * (66 + z * (103 + z * (89 + z * (31 + z * (97 + z * (117 + z * (52 + z * (87 + z * (2 + z * 60)))))))))))))))))))

def pow4_16_q {R : Type*} [CommRing R] (z : R) : R := (55 + z * (125 + z * (41 + z * (42 + z * (109 + z * (25 + z * (125 + z * (126 + z * (87 + z * (42 + z * (125 + z * (30 + z * (2 + z * (70 + z * (50 + z * (62 + z * (6 + z * (25 + z * 74))))))))))))))))))

def pow4_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (88 + z * ((-31) + z * (84 + z * ((-8) + z * (128 + z * (20 + z * (15 + z * (90 + z * (84 + z * ((-14) + z * (46 + z * ((-92) + z * (51 + z * (10 + z * ((-51) + z * (5 + z * (189 + z * (27 + z * (70 + z * (125 + z * (267 + z * (209 + z * (66 + z * (210 + z * (284 + z * (101 + z * (76 + z * (276 + z * (192 + z * ((-5) + z * (221 + z * (309 + z * (127 + z * (156 + z * (244 + z * (145 + z * (113 + z * (161 + z * 82))))))))))))))))))))))))))))))))))))))


def pow4_32 {R : Type*} [CommRing R] (z : R) : R := (46 + z * (1 + z * (119 + z * (45 + z * (77 + z * (113 + z * (50 + z * (95 + z * (45 + z * (20 + z * (98 + z * (19 + z * (128 + z * (83 + z * (21 + z * (104 + z * (35 + z * (120 + z * (94 + z * 65)))))))))))))))))))

def pow4_32_q {R : Type*} [CommRing R] (z : R) : R := (40 + z * (29 + z * (63 + z * (15 + z * (96 + z * (28 + z * (63 + z * (60 + z * (94 + z * (67 + z * (117 + z * (69 + z * (92 + z * (86 + z * (78 + z * (22 + z * (40 + z * (12 + z * 63))))))))))))))))))

def pow4_32_mul_t {R : Type*} [CommRing R] (z : R) : R := (98 + z * (23 + z * (8 + z * (104 + z * (64 + z * (125 + z * (24 + z * (175 + z * (181 + z * (177 + z * (183 + z * (211 + z * (256 + z * (101 + z * (313 + z * (288 + z * (308 + z * (334 + z * (238 + z * (384 + z * (288 + z * (200 + z * (323 + z * (231 + z * (347 + z * (154 + z * (260 + z * (148 + z * (188 + z * (88 + z * (103 + z * (126 + z * (87 + z * (71 + z * (91 + z * (1 + z * (45 + z * ((-30) + z * 27))))))))))))))))))))))))))))))))))))))


def pow4_64 {R : Type*} [CommRing R] (z : R) : R := (19 + z * (29 + z * (2 + z * (2 + z * (17 + z * (109 + z * (79 + z * (110 + z * (82 + z * (8 + z * (115 + z * (90 + z * (48 + z * (73 + z * (72 + z * (117 + z * (51 + z * (23 + z * (10 + z * 92)))))))))))))))))))

def pow4_64_q {R : Type*} [CommRing R] (z : R) : R := (76 + z * (32 + z * (68 + z * (42 + z * (20 + z * (14 + z * (46 + z * (123 + z * (46 + z * (84 + z * (93 + z * (15 + z * (125 + z * (41 + z * (21 + z * (26 + z * (45 + z * (86 + z * 33))))))))))))))))))

def pow4_64_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-13) + z * ((-39) + z * (9 + z * ((-36) + z * (60 + z * (33 + z * (86 + z * (128 + z * (36 + z * (120 + z * (127 + z * ((-58) + z * (145 + z * ((-11) + z * (90 + z * (186 + z * (48 + z * (299 + z * (77 + z * (257 + z * (305 + z * (177 + z * (391 + z * (225 + z * (241 + z * (201 + z * (58 + z * (255 + z * (89 + z * (190 + z * (273 + z * (197 + z * (216 + z * (129 + z * (176 + z * (133 + z * (128 + z * (76 + z * 32))))))))))))))))))))))))))))))))))))))


def pow4_65 {R : Type*} [CommRing R] (z : R) : R := (3 + z * (114 + z * (127 + z * (120 + z * (129 + z * (89 + z * (83 + z * (113 + z * (27 + z * (110 + z * (64 + z * (1 + z * (38 + z * (84 + z * (107 + z * (26 + z * (33 + z * (123 + z * (100 + z * 33)))))))))))))))))))

def pow4_65_q {R : Type*} [CommRing R] (z : R) : R := (99 + z * (7 + z * (39 + z * (71 + z * (92 + z * (17 + z * (58 + z * (64 + z * (30 + z * (58 + z * (71 + z * (126 + z * (90 + z * (42 + z * (70 + z * (40 + z * (114 + z * (80 + z * 68))))))))))))))))))

def pow4_65_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-22) + z * ((-10) + z * ((-50) + z * ((-32) + z * ((-89) + z * ((-57) + z * (10 + z * ((-8) + z * ((-15) + z * ((-28) + z * (143 + z * ((-71) + z * ((-89) + z * (9 + z * (21 + z * ((-14) + z * (30 + z * (67 + z * ((-30) + z * ((-12) + z * ((-46) + z * ((-27) + z * (30 + z * ((-28) + z * (114 + z * (29 + z * (54 + z * ((-24) + z * ((-11) + z * ((-91) + z * (13 + z * (33 + z * (31 + z * ((-39) + z * ((-27) + z * ((-42) + z * (6 + z * (0 + z * 36))))))))))))))))))))))))))))))))))))))


def pow4_130 {R : Type*} [CommRing R] (z : R) : R := (91 + z * (121 + z * (12 + z * (4 + z * (26 + z * (113 + z * (43 + z * (23 + z * (3 + z * (37 + z * (121 + z * (41 + z * (63 + z * (124 + z * (35 + z * (31 + z * (119 + z * (44 + z * (57 + z * 43)))))))))))))))))))

def pow4_130_q {R : Type*} [CommRing R] (z : R) : R := (56 + z * (87 + z * (35 + z * (54 + z * (88 + z * (119 + z * (70 + z * (83 + z * (67 + z * (32 + z * (9 + z * (27 + z * (7 + z * (62 + z * (127 + z * (105 + z * (128 + z * (95 + z * 41))))))))))))))))))

def pow4_130_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-22) + z * ((-49) + z * (33 + z * (141 + z * (222 + z * (255 + z * (301 + z * (337 + z * (354 + z * (259 + z * (373 + z * (397 + z * (185 + z * (175 + z * (238 + z * (257 + z * (204 + z * (138 + z * (237 + z * (365 + z * (360 + z * (312 + z * (214 + z * (212 + z * (97 + z * ((-45) + z * (56 + z * (94 + z * (1 + z * ((-85) + z * (33 + z * (148 + z * (22 + z * ((-78) + z * (5 + z * (81 + z * (71 + z * (29 + z * 8))))))))))))))))))))))))))))))))))))))


def pow4_131 {R : Type*} [CommRing R] (z : R) : R := (53 + z * (64 + z * (118 + z * (110 + z * (94 + z * (110 + z * (101 + z * (49 + z * (27 + z * (29 + z * (42 + z * (109 + z * (72 + z * (115 + z * (113 + z * (23 + z * (53 + z * (52 + z * (32 + z * 22)))))))))))))))))))

def pow4_131_q {R : Type*} [CommRing R] (z : R) : R := (103 + z * (128 + z * (111 + z * (24 + z * (66 + z * (110 + z * (17 + z * (118 + z * (89 + z * (24 + z * (112 + z * (56 + z * (108 + z * (0 + z * (8 + z * (49 + z * (107 + z * (70 + z * 9))))))))))))))))))

def pow4_131_mul_t {R : Type*} [CommRing R] (z : R) : R := (36 + z * (38 + z * ((-62) + z * (6 + z * ((-7) + z * ((-67) + z * ((-78) + z * ((-109) + z * ((-125) + z * ((-182) + z * ((-14) + z * ((-65) + z * ((-205) + z * ((-110) + z * ((-82) + z * ((-101) + z * (13 + z * ((-118) + z * ((-81) + z * ((-49) + z * ((-160) + z * ((-39) + z * (143 + z * ((-101) + z * ((-29) + z * (64 + z * (19 + z * (72 + z * (36 + z * (75 + z * (106 + z * (71 + z * (62 + z * (41 + z * (21 + z * (33 + z * (27 + z * (32 + z * 17))))))))))))))))))))))))))))))))))))))


abbrev u4 {R : Type*} [CommRing R] (z : R) : R := pow4_131 z

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod131Powers03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131
def pow5_2 {R : Type*} [CommRing R] (z : R) : R := (36 + z * (86 + z * (104 + z * (127 + z * (85 + z * (123 + z * (112 + z * (80 + z * (0 + z * (74 + z * (115 + z * (65 + z * (13 + z * (25 + z * (125 + z * (71 + z * (52 + z * (44 + z * (127 + z * 63)))))))))))))))))))

def pow5_2_q {R : Type*} [CommRing R] (z : R) : R := (100 + z * (19 + z * (61 + z * (54 + z * (127 + z * (16 + z * (7 + z * (8 + z * (59 + z * (22 + z * (83 + z * (51 + z * (120 + z * (40 + z * (110 + z * (13 + z * (111 + z * (118 + z * 91))))))))))))))))))

def pow5_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-17) + z * (8 + z * (47 + z * (134 + z * (134 + z * (192 + z * (319 + z * (322 + z * (269 + z * (222 + z * (244 + z * (160 + z * (123 + z * (231 + z * (359 + z * (308 + z * (358 + z * (337 + z * (309 + z * (180 + z * (141 + z * ((-34) + z * (14 + z * ((-28) + z * (84 + z * ((-18) + z * ((-3) + z * (4 + z * ((-47) + z * ((-133) + z * ((-47) + z * ((-31) + z * ((-53) + z * ((-115) + z * ((-107) + z * ((-100) + z * ((-76) + z * ((-36) + z * 3))))))))))))))))))))))))))))))))))))))


def pow5_4 {R : Type*} [CommRing R] (z : R) : R := (114 + z * (55 + z * (94 + z * (128 + z * (73 + z * (110 + z * (64 + z * (50 + z * (77 + z * (127 + z * (80 + z * (51 + z * (18 + z * (64 + z * (21 + z * (73 + z * (29 + z * (99 + z * (80 + z * 6)))))))))))))))))))

def pow5_4_q {R : Type*} [CommRing R] (z : R) : R := (97 + z * (63 + z * (5 + z * (78 + z * (43 + z * (63 + z * (124 + z * (114 + z * (43 + z * (16 + z * (11 + z * (14 + z * (99 + z * (28 + z * (42 + z * (92 + z * (82 + z * (66 + z * 39))))))))))))))))))

def pow5_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-28) + z * ((-12) + z * (41 + z * (126 + z * (185 + z * (183 + z * (317 + z * (325 + z * (248 + z * (281 + z * (318 + z * (244 + z * (271 + z * (242 + z * (186 + z * (304 + z * (323 + z * (237 + z * (215 + z * (339 + z * (510 + z * (520 + z * (216 + z * (199 + z * (312 + z * (200 + z * (25 + z * (80 + z * (230 + z * (191 + z * (58 + z * (13 + z * (192 + z * (145 + z * (50 + z * (49 + z * (114 + z * (102 + z * 30))))))))))))))))))))))))))))))))))))))


def pow5_8 {R : Type*} [CommRing R] (z : R) : R := (130 + z * (115 + z * (125 + z * (69 + z * (87 + z * (40 + z * (120 + z * (107 + z * (108 + z * (115 + z * (3 + z * (34 + z * (57 + z * (57 + z * (128 + z * (126 + z * (97 + z * (78 + z * (21 + z * 1)))))))))))))))))))

def pow5_8_q {R : Type*} [CommRing R] (z : R) : R := (32 + z * (111 + z * (61 + z * (30 + z * (26 + z * (9 + z * (124 + z * (94 + z * (5 + z * (40 + z * (4 + z * (126 + z * (121 + z * (12 + z * (5 + z * (38 + z * (15 + z * (25 + z * 36))))))))))))))))))

def pow5_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (86 + z * (41 + z * (107 + z * (208 + z * (214 + z * (310 + z * (234 + z * (263 + z * (300 + z * (361 + z * (395 + z * (318 + z * (287 + z * (305 + z * (202 + z * (309 + z * (215 + z * (274 + z * (397 + z * (209 + z * (277 + z * (339 + z * (179 + z * (86 + z * (102 + z * (89 + z * (226 + z * (147 + z * (58 + z * ((-24) + z * ((-2) + z * (23 + z * (106 + z * (83 + z * (58 + z * (91 + z * (29 + z * ((-11) + z * 0))))))))))))))))))))))))))))))))))))))


def pow5_16 {R : Type*} [CommRing R] (z : R) : R := (83 + z * (96 + z * (50 + z * (88 + z * (93 + z * (27 + z * (50 + z * (124 + z * (106 + z * (121 + z * (125 + z * (108 + z * (3 + z * (24 + z * (47 + z * (21 + z * (25 + z * (106 + z * (26 + z * 105)))))))))))))))))))

def pow5_16_q {R : Type*} [CommRing R] (z : R) : R := (56 + z * (119 + z * (54 + z * (22 + z * (73 + z * (13 + z * (59 + z * (71 + z * (94 + z * (108 + z * (93 + z * (10 + z * (103 + z * (18 + z * (87 + z * (108 + z * (26 + z * (107 + z * 1))))))))))))))))))

def pow5_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (107 + z * (162 + z * (258 + z * (260 + z * (299 + z * (199 + z * (310 + z * (432 + z * (472 + z * (467 + z * (411 + z * (281 + z * (177 + z * (257 + z * (395 + z * (627 + z * (625 + z * (450 + z * (475 + z * (185 + z * (232 + z * (334 + z * (298 + z * (347 + z * (229 + z * (6 + z * ((-20) + z * ((-13) + z * (9 + z * (191 + z * (186 + z * (181 + z * (127 + z * ((-15) + z * ((-28) + z * ((-36) + z * ((-50) + z * ((-1) + z * 0))))))))))))))))))))))))))))))))))))))


def pow5_32 {R : Type*} [CommRing R] (z : R) : R := (91 + z * (125 + z * (56 + z * (51 + z * (96 + z * (112 + z * (11 + z * (91 + z * (73 + z * (111 + z * (91 + z * (122 + z * (110 + z * (6 + z * (68 + z * (1 + z * (110 + z * (118 + z * (104 + z * 64)))))))))))))))))))

def pow5_32_q {R : Type*} [CommRing R] (z : R) : R := (115 + z * (9 + z * (18 + z * (35 + z * (81 + z * (122 + z * (37 + z * (68 + z * (52 + z * (33 + z * (22 + z * (71 + z * (75 + z * (106 + z * (66 + z * (53 + z * (10 + z * (13 + z * 21))))))))))))))))))

def pow5_32_mul_t {R : Type*} [CommRing R] (z : R) : R := (8 + z * (76 + z * (67 + z * (140 + z * (149 + z * (36 + z * (110 + z * (166 + z * (205 + z * (236 + z * (423 + z * (439 + z * (255 + z * (185 + z * (334 + z * (200 + z * (62 + z * (347 + z * (364 + z * (320 + z * (335 + z * (234 + z * (98 + z * (58 + z * (94 + z * (161 + z * (242 + z * (264 + z * (256 + z * (77 + z * (45 + z * ((-63) + z * ((-19) + z * (48 + z * (79 + z * (63 + z * (159 + z * (31 + z * 84))))))))))))))))))))))))))))))))))))))


def pow5_64 {R : Type*} [CommRing R] (z : R) : R := (23 + z * (25 + z * (101 + z * (98 + z * (2 + z * (95 + z * (98 + z * (43 + z * (71 + z * (95 + z * (20 + z * (80 + z * (13 + z * (92 + z * (118 + z * (50 + z * (50 + z * (4 + z * (66 + z * 21)))))))))))))))))))

def pow5_64_q {R : Type*} [CommRing R] (z : R) : R := (118 + z * (58 + z * (52 + z * (40 + z * (91 + z * (74 + z * (70 + z * (72 + z * (17 + z * (3 + z * (32 + z * (73 + z * (107 + z * (28 + z * (12 + z * (78 + z * (14 + z * (129 + z * 35))))))))))))))))))

def pow5_64_mul_t {R : Type*} [CommRing R] (z : R) : R := (18 + z * (109 + z * (98 + z * (94 + z * (106 + z * (158 + z * (145 + z * (82 + z * (156 + z * (248 + z * (345 + z * (289 + z * (397 + z * (298 + z * (349 + z * (266 + z * (333 + z * (393 + z * (500 + z * (514 + z * (423 + z * (592 + z * (325 + z * (347 + z * (252 + z * (297 + z * (406 + z * (421 + z * (397 + z * (254 + z * (194 + z * (87 + z * (111 + z * (125 + z * (165 + z * (216 + z * (117 + z * (83 + z * 31))))))))))))))))))))))))))))))))))))))


def pow5_65 {R : Type*} [CommRing R] (z : R) : R := (64 + z * (50 + z * (102 + z * (11 + z * (97 + z * (61 + z * (88 + z * (18 + z * (38 + z * (71 + z * (46 + z * (8 + z * (28 + z * (81 + z * (58 + z * (7 + z * (56 + z * (105 + z * (77 + z * 103)))))))))))))))))))

def pow5_65_q {R : Type*} [CommRing R] (z : R) : R := (10 + z * (1 + z * (78 + z * (114 + z * (10 + z * (84 + z * (14 + z * (46 + z * (71 + z * (126 + z * (19 + z * (56 + z * (2 + z * (114 + z * (45 + z * (3 + z * (43 + z * (59 + z * 69))))))))))))))))))

def pow5_65_mul_t {R : Type*} [CommRing R] (z : R) : R := (5 + z * (17 + z * (38 + z * (57 + z * (88 + z * (135 + z * (177 + z * (135 + z * (214 + z * (186 + z * (78 + z * (170 + z * (180 + z * (127 + z * (143 + z * (233 + z * (267 + z * (263 + z * (127 + z * (299 + z * (176 + z * (18 + z * (70 + z * (130 + z * (46 + z * (34 + z * (9 + z * (104 + z * (56 + z * ((-12) + z * (26 + z * (46 + z * (33 + z * ((-16) + z * ((-36) + z * ((-30) + z * ((-36) + z * ((-19) + z * 3))))))))))))))))))))))))))))))))))))))


def pow5_130 {R : Type*} [CommRing R] (z : R) : R := (122 + z * (100 + z * (1 + z * (30 + z * (108 + z * (50 + z * (56 + z * (120 + z * (21 + z * (52 + z * (86 + z * (35 + z * (0 + z * (120 + z * (56 + z * (0 + z * (73 + z * (66 + z * (79 + z * 74)))))))))))))))))))

def pow5_130_q {R : Type*} [CommRing R] (z : R) : R := (69 + z * (69 + z * (116 + z * (47 + z * (15 + z * (74 + z * (0 + z * (0 + z * (72 + z * (48 + z * (124 + z * (112 + z * (7 + z * (21 + z * (59 + z * (95 + z * (30 + z * (12 + z * 129))))))))))))))))))

def pow5_130_mul_t {R : Type*} [CommRing R] (z : R) : R := (4 + z * ((-3) + z * (16 + z * ((-17) + z * (53 + z * ((-24) + z * (118 + z * ((-8) + z * (89 + z * ((-10) + z * (4 + z * ((-18) + z * ((-93) + z * ((-148) + z * ((-6) + z * ((-79) + z * ((-131) + z * ((-11) + z * (0 + z * (48 + z * ((-22) + z * (50 + z * ((-9) + z * (64 + z * (53 + z * (55 + z * ((-104) + z * ((-60) + z * ((-2) + z * ((-89) + z * ((-1) + z * (55 + z * (128 + z * (61 + z * (10 + z * (142 + z * (146 + z * (56 + z * 80))))))))))))))))))))))))))))))))))))))


def pow5_131 {R : Type*} [CommRing R] (z : R) : R := (100 + z * (89 + z * (102 + z * (35 + z * (36 + z * (105 + z * (54 + z * (56 + z * (65 + z * (52 + z * (11 + z * (41 + z * (74 + z * (91 + z * (104 + z * (46 + z * (29 + z * (36 + z * (95 + z * 75)))))))))))))))))))

def pow5_131_q {R : Type*} [CommRing R] (z : R) : R := (33 + z * (25 + z * (61 + z * (110 + z * (123 + z * (98 + z * (76 + z * (52 + z * (11 + z * (115 + z * (73 + z * (13 + z * (115 + z * (12 + z * (81 + z * (12 + z * (127 + z * (17 + z * 56))))))))))))))))))

def pow5_131_mul_t {R : Type*} [CommRing R] (z : R) : R := (36 + z * (78 + z * (110 + z * (123 + z * (92 + z * (86 + z * (149 + z * (109 + z * (46 + z * (70 + z * (86 + z * (80 + z * (95 + z * (119 + z * (23 + z * (100 + z * (6 + z * (20 + z * (148 + z * (128 + z * (75 + z * (9 + z * (29 + z * (0 + z * (110 + z * ((-65) + z * (36 + z * (12 + z * ((-41) + z * (18 + z * (129 + z * (60 + z * (69 + z * (22 + z * ((-18) + z * ((-3) + z * (25 + z * (3 + z * 12))))))))))))))))))))))))))))))))))))))


def pow6_2 {R : Type*} [CommRing R] (z : R) : R := (72 + z * (22 + z * (30 + z * (4 + z * (71 + z * (62 + z * (85 + z * (43 + z * (123 + z * (9 + z * (87 + z * (105 + z * (8 + z * (62 + z * (54 + z * (19 + z * (26 + z * (25 + z * (39 + z * 93)))))))))))))))))))

def pow6_2_q {R : Type*} [CommRing R] (z : R) : R := (99 + z * (66 + z * (81 + z * (103 + z * (75 + z * (94 + z * (12 + z * (7 + z * (74 + z * (105 + z * (14 + z * (17 + z * (43 + z * (39 + z * (99 + z * (2 + z * (41 + z * (106 + z * 123))))))))))))))))))

def pow6_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (38 + z * (75 + z * (113 + z * (74 + z * (11 + z * (14 + z * (94 + z * (95 + z * (29 + z * (17 + z * (5 + z * ((-30) + z * ((-16) + z * (30 + z * (161 + z * (171 + z * (2 + z * (9 + z * (103 + z * (167 + z * (132 + z * ((-6) + z * ((-65) + z * (86 + z * (100 + z * ((-36) + z * (77 + z * (95 + z * (29 + z * ((-61) + z * (14 + z * (127 + z * (158 + z * (31 + z * ((-36) + z * ((-29) + z * (1 + z * (46 + z * 42))))))))))))))))))))))))))))))))))))))


def pow6_4 {R : Type*} [CommRing R] (z : R) : R := (2 + z * (82 + z * (8 + z * (44 + z * (82 + z * (53 + z * (128 + z * (71 + z * (103 + z * (22 + z * (72 + z * (33 + z * (9 + z * (54 + z * (127 + z * (14 + z * (97 + z * (83 + z * (33 + z * 8)))))))))))))))))))

def pow6_4_q {R : Type*} [CommRing R] (z : R) : R := (46 + z * (8 + z * (40 + z * (120 + z * (49 + z * (31 + z * (30 + z * (123 + z * (52 + z * (22 + z * (112 + z * (36 + z * (107 + z * (76 + z * (87 + z * (49 + z * (108 + z * (113 + z * 3))))))))))))))))))

def pow6_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (22 + z * (4 + z * ((-4) + z * ((-58) + z * ((-22) + z * ((-46) + z * (49 + z * ((-98) + z * ((-25) + z * ((-57) + z * (33 + z * ((-60) + z * ((-80) + z * ((-1) + z * ((-81) + z * ((-163) + z * ((-71) + z * ((-153) + z * ((-147) + z * ((-97) + z * ((-216) + z * ((-168) + z * ((-186) + z * ((-151) + z * ((-76) + z * ((-150) + z * ((-152) + z * ((-23) + z * ((-223) + z * ((-100) + z * ((-39) + z * ((-115) + z * ((-67) + z * ((-84) + z * ((-71) + z * ((-55) + z * ((-12) + z * (53 + z * 66))))))))))))))))))))))))))))))))))))))


def pow6_8 {R : Type*} [CommRing R] (z : R) : R := (2 + z * (49 + z * (75 + z * (84 + z * (106 + z * (117 + z * (17 + z * (56 + z * (77 + z * (126 + z * (36 + z * (16 + z * (73 + z * (100 + z * (70 + z * (101 + z * (36 + z * (47 + z * (78 + z * 48)))))))))))))))))))

def pow6_8_q {R : Type*} [CommRing R] (z : R) : R := (21 + z * (33 + z * (60 + z * (1 + z * (119 + z * (94 + z * (124 + z * (57 + z * (4 + z * (121 + z * (122 + z * (67 + z * (98 + z * (128 + z * (53 + z * (127 + z * (96 + z * (103 + z * 64))))))))))))))))))

def pow6_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-8) + z * ((-18) + z * (6 + z * ((-31) + z * ((-35) + z * ((-17) + z * ((-106) + z * (26 + z * ((-5) + z * ((-28) + z * ((-44) + z * ((-26) + z * ((-12) + z * ((-168) + z * ((-95) + z * ((-124) + z * ((-183) + z * ((-292) + z * ((-207) + z * ((-149) + z * ((-124) + z * ((-197) + z * ((-142) + z * ((-207) + z * ((-88) + z * ((-263) + z * ((-265) + z * ((-149) + z * ((-252) + z * ((-271) + z * ((-38) + z * ((-71) + z * ((-72) + z * ((-61) + z * ((-85) + z * ((-66) + z * ((-63) + z * ((-29) + z * 0))))))))))))))))))))))))))))))))))))))


def pow6_16 {R : Type*} [CommRing R] (z : R) : R := (62 + z * (113 + z * (23 + z * (105 + z * (26 + z * (88 + z * (123 + z * (86 + z * (40 + z * (13 + z * (51 + z * (47 + z * (114 + z * (78 + z * (49 + z * (121 + z * (68 + z * (2 + z * (101 + z * 26)))))))))))))))))))

def pow6_16_q {R : Type*} [CommRing R] (z : R) : R := (46 + z * (113 + z * (64 + z * (75 + z * (18 + z * (78 + z * (7 + z * (19 + z * (44 + z * (10 + z * (92 + z * (53 + z * (53 + z * (21 + z * (24 + z * (55 + z * (3 + z * (48 + z * 77))))))))))))))))))

def pow6_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-18) + z * ((-59) + z * ((-67) + z * ((-57) + z * ((-1) + z * ((-7) + z * (76 + z * (110 + z * (87 + z * (108 + z * (110 + z * (159 + z * (92 + z * (127 + z * (170 + z * (121 + z * (243 + z * (342 + z * (303 + z * (202 + z * (276 + z * (306 + z * (337 + z * (254 + z * (261 + z * (171 + z * (155 + z * (258 + z * (183 + z * (46 + z * (118 + z * (148 + z * (177 + z * (106 + z * (36 + z * (30 + z * (22 + z * (18 + z * 17))))))))))))))))))))))))))))))))))))))


def pow6_32 {R : Type*} [CommRing R] (z : R) : R := (95 + z * (18 + z * (96 + z * (113 + z * (123 + z * (25 + z * (123 + z * (91 + z * (118 + z * (40 + z * (85 + z * (28 + z * (69 + z * (87 + z * (58 + z * (114 + z * (27 + z * (43 + z * (57 + z * 123)))))))))))))))))))

def pow6_32_q {R : Type*} [CommRing R] (z : R) : R := (130 + z * (121 + z * (88 + z * (104 + z * (52 + z * (87 + z * (36 + z * (83 + z * (121 + z * (84 + z * (122 + z * (56 + z * (90 + z * (5 + z * (44 + z * (42 + z * (59 + z * (67 + z * 21))))))))))))))))))

def pow6_32_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-21) + z * (14 + z * ((-22) + z * ((-15) + z * (17 + z * ((-132) + z * (117 + z * (65 + z * ((-18) + z * ((-66) + z * ((-106) + z * ((-79) + z * ((-125) + z * (0 + z * ((-90) + z * (22 + z * (17 + z * ((-37) + z * (136 + z * (70 + z * ((-38) + z * (81 + z * (41 + z * (3 + z * (85 + z * (80 + z * (19 + z * (25 + z * (59 + z * (32 + z * (191 + z * (168 + z * (48 + z * (95 + z * (66 + z * ((-38) + z * (35 + z * (29 + z * 5))))))))))))))))))))))))))))))))))))))


def pow6_64 {R : Type*} [CommRing R] (z : R) : R := (52 + z * (96 + z * (108 + z * (119 + z * (38 + z * (64 + z * (31 + z * (106 + z * (2 + z * (0 + z * (9 + z * (76 + z * (113 + z * (70 + z * (100 + z * (84 + z * (74 + z * (27 + z * (89 + z * 90)))))))))))))))))))

def pow6_64_q {R : Type*} [CommRing R] (z : R) : R := (93 + z * (76 + z * (121 + z * (93 + z * (61 + z * (38 + z * (94 + z * (95 + z * (5 + z * (3 + z * (6 + z * (56 + z * (77 + z * (6 + z * (74 + z * (89 + z * (43 + z * (104 + z * 64))))))))))))))))))

def pow6_64_mul_t {R : Type*} [CommRing R] (z : R) : R := (33 + z * ((-37) + z * (22 + z * (57 + z * (100 + z * (10 + z * (234 + z * (108 + z * (219 + z * (181 + z * (407 + z * (138 + z * (284 + z * (230 + z * (276 + z * (304 + z * (317 + z * (299 + z * (278 + z * (292 + z * (229 + z * (517 + z * (322 + z * (319 + z * (155 + z * (312 + z * (199 + z * (276 + z * (111 + z * (130 + z * (49 + z * (107 + z * (163 + z * (46 + z * (106 + z * ((-5) + z * (24 + z * (74 + z * 115))))))))))))))))))))))))))))))))))))))


def pow6_65 {R : Type*} [CommRing R] (z : R) : R := (38 + z * (38 + z * (58 + z * (75 + z * (107 + z * (91 + z * (121 + z * (125 + z * (102 + z * (99 + z * (8 + z * (121 + z * (104 + z * (56 + z * (43 + z * (111 + z * (68 + z * (101 + z * (49 + z * 109)))))))))))))))))))

def pow6_65_q {R : Type*} [CommRing R] (z : R) : R := (98 + z * (24 + z * (108 + z * (109 + z * (18 + z * (88 + z * (74 + z * (12 + z * (1 + z * (82 + z * (86 + z * (97 + z * (106 + z * (99 + z * (115 + z * (37 + z * (56 + z * (60 + z * 69))))))))))))))))))

def pow6_65_mul_t {R : Type*} [CommRing R] (z : R) : R := (2 + z * (64 + z * (90 + z * (143 + z * (77 + z * (53 + z * (87 + z * (59 + z * (81 + z * (71 + z * ((-86) + z * ((-121) + z * (56 + z * ((-50) + z * ((-23) + z * (82 + z * (65 + z * ((-4) + z * ((-61) + z * (96 + z * (163 + z * ((-11) + z * ((-180) + z * ((-65) + z * (3 + z * ((-33) + z * (34 + z * ((-8) + z * ((-32) + z * ((-49) + z * (49 + z * (96 + z * (121 + z * (92 + z * (48 + z * (25 + z * (43 + z * (81 + z * 51))))))))))))))))))))))))))))))))))))))


def pow6_130 {R : Type*} [CommRing R] (z : R) : R := (70 + z * (81 + z * (34 + z * (78 + z * (109 + z * (51 + z * (97 + z * (129 + z * (32 + z * (3 + z * (114 + z * (85 + z * (1 + z * (117 + z * (120 + z * (71 + z * (124 + z * (82 + z * (71 + z * 63)))))))))))))))))))

def pow6_130_q {R : Type*} [CommRing R] (z : R) : R := (17 + z * (124 + z * (130 + z * (35 + z * (1 + z * (54 + z * (27 + z * (114 + z * (22 + z * (90 + z * (12 + z * (15 + z * (28 + z * (116 + z * (124 + z * (119 + z * (75 + z * (91 + z * 91))))))))))))))))))

def pow6_130_mul_t {R : Type*} [CommRing R] (z : R) : R := (4 + z * ((-32) + z * ((-58) + z * ((-47) + z * (23 + z * (38 + z * (45 + z * (122 + z * (246 + z * (210 + z * (255 + z * (395 + z * (372 + z * (343 + z * (262 + z * (444 + z * (408 + z * (360 + z * (282 + z * (446 + z * (409 + z * (444 + z * (455 + z * (559 + z * (475 + z * (234 + z * (257 + z * (248 + z * (249 + z * (70 + z * (209 + z * (126 + z * (93 + z * (29 + z * (125 + z * (75 + z * (99 + z * (35 + z * 90))))))))))))))))))))))))))))))))))))))


def pow6_131 {R : Type*} [CommRing R] (z : R) : R := (72 + z * (119 + z * (100 + z * (65 + z * (61 + z * (44 + z * (98 + z * (122 + z * (121 + z * (89 + z * (124 + z * (95 + z * (115 + z * (125 + z * (87 + z * (16 + z * (127 + z * (125 + z * (103 + z * 39)))))))))))))))))))

def pow6_131_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (17 + z * (67 + z * (15 + z * (52 + z * (102 + z * (85 + z * (61 + z * (125 + z * (122 + z * (120 + z * (9 + z * (113 + z * (79 + z * (130 + z * (113 + z * (104 + z * (105 + z * 9))))))))))))))))))

def pow6_131_mul_t {R : Type*} [CommRing R] (z : R) : R := (38 + z * (88 + z * (84 + z * (119 + z * (121 + z * (141 + z * (168 + z * (144 + z * (166 + z * (64 + z * ((-20) + z * (74 + z * (76 + z * ((-25) + z * (6 + z * (126 + z * (69 + z * ((-110) + z * (114 + z * (136 + z * (10 + z * ((-92) + z * (1 + z * ((-28) + z * ((-39) + z * ((-85) + z * ((-85) + z * ((-72) + z * ((-31) + z * (72 + z * (72 + z * (72 + z * (90 + z * (20 + z * (41 + z * (60 + z * (58 + z * (81 + z * 36))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod131Powers04
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131
def pow7_2 {R : Type*} [CommRing R] (z : R) : R := (66 + z * (22 + z * (112 + z * (71 + z * (126 + z * (110 + z * (67 + z * (24 + z * (63 + z * (59 + z * (23 + z * (80 + z * (106 + z * (120 + z * (29 + z * (83 + z * (101 + z * (24 + z * (80 + z * 55)))))))))))))))))))

def pow7_2_q {R : Type*} [CommRing R] (z : R) : R := (29 + z * (129 + z * (70 + z * (35 + z * (22 + z * (79 + z * (117 + z * (115 + z * (8 + z * (23 + z * (112 + z * (12 + z * (13 + z * (7 + z * (38 + z * (62 + z * (114 + z * (3 + z * 80))))))))))))))))))

def pow7_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (28 + z * (71 + z * (130 + z * (146 + z * (167 + z * (95 + z * (72 + z * (214 + z * (326 + z * (343 + z * (373 + z * (432 + z * (454 + z * (607 + z * (616 + z * (614 + z * (709 + z * (735 + z * (783 + z * (900 + z * (868 + z * (698 + z * (677 + z * (631 + z * (821 + z * (722 + z * (659 + z * (561 + z * (538 + z * (481 + z * (529 + z * (318 + z * (241 + z * (205 + z * (192 + z * (183 + z * (117 + z * (21 + z * 11))))))))))))))))))))))))))))))))))))))


def pow7_4 {R : Type*} [CommRing R] (z : R) : R := (20 + z * (124 + z * (65 + z * (50 + z * (19 + z * (35 + z * (82 + z * (107 + z * (19 + z * (69 + z * (107 + z * (94 + z * (24 + z * (35 + z * (95 + z * (82 + z * (54 + z * (0 + z * (70 + z * 89)))))))))))))))))))

def pow7_4_q {R : Type*} [CommRing R] (z : R) : R := (71 + z * (112 + z * (121 + z * (121 + z * (112 + z * (40 + z * (48 + z * (88 + z * (30 + z * (57 + z * (7 + z * (61 + z * (13 + z * (121 + z * (96 + z * (60 + z * (5 + z * (17 + z * 12))))))))))))))))))

def pow7_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (6 + z * ((-47) + z * ((-5) + z * ((-48) + z * (43 + z * (16 + z * (85 + z * (70 + z * (71 + z * (21 + z * (69 + z * ((-13) + z * ((-19) + z * (82 + z * (28 + z * (147 + z * (211 + z * (309 + z * (222 + z * (148 + z * (235 + z * (294 + z * (154 + z * (247 + z * (284 + z * (140 + z * (107 + z * (243 + z * (271 + z * (207 + z * (158 + z * (228 + z * (109 + z * (70 + z * (150 + z * (99 + z * (55 + z * (61 + z * 23))))))))))))))))))))))))))))))))))))))


def pow7_8 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (82 + z * (32 + z * (95 + z * (95 + z * (98 + z * (14 + z * (105 + z * (2 + z * (5 + z * (50 + z * (94 + z * (115 + z * (75 + z * (48 + z * (33 + z * (82 + z * (72 + z * (19 + z * 31)))))))))))))))))))

def pow7_8_q {R : Type*} [CommRing R] (z : R) : R := (21 + z * (49 + z * (58 + z * (24 + z * (8 + z * (81 + z * (101 + z * (83 + z * (80 + z * (62 + z * (103 + z * (59 + z * (123 + z * (22 + z * (80 + z * (22 + z * (97 + z * (50 + z * 61))))))))))))))))))

def pow7_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-5) + z * (11 + z * (87 + z * (80 + z * (72 + z * ((-5) + z * ((-21) + z * (52 + z * (127 + z * ((-3) + z * ((-24) + z * (79 + z * (87 + z * ((-27) + z * ((-95) + z * (44 + z * (128 + z * (42 + z * ((-128) + z * ((-69) + z * (163 + z * (69 + z * ((-11) + z * ((-158) + z * ((-1) + z * (103 + z * (59 + z * ((-103) + z * (21 + z * (87 + z * (56 + z * ((-45) + z * (34 + z * (80 + z * (55 + z * ((-21) + z * ((-16) + z * (64 + z * 60))))))))))))))))))))))))))))))))))))))


def pow7_16 {R : Type*} [CommRing R] (z : R) : R := (82 + z * (114 + z * (125 + z * (112 + z * (78 + z * (70 + z * (19 + z * (46 + z * (48 + z * (124 + z * (42 + z * (122 + z * (29 + z * (38 + z * (91 + z * (18 + z * (65 + z * (48 + z * (71 + z * 68)))))))))))))))))))

def pow7_16_q {R : Type*} [CommRing R] (z : R) : R := (122 + z * (130 + z * (67 + z * (17 + z * (75 + z * (28 + z * (47 + z * (30 + z * (98 + z * (12 + z * (46 + z * (28 + z * (117 + z * (46 + z * (94 + z * (104 + z * (79 + z * (108 + z * 44))))))))))))))))))

def pow7_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-47) + z * ((-88) + z * ((-79) + z * ((-69) + z * ((-23) + z * ((-62) + z * (20 + z * (21 + z * (54 + z * ((-113) + z * (1 + z * ((-66) + z * ((-122) + z * ((-168) + z * (88 + z * (53 + z * ((-8) + z * ((-22) + z * (35 + z * ((-132) + z * ((-80) + z * ((-47) + z * ((-27) + z * ((-24) + z * ((-8) + z * ((-159) + z * ((-84) + z * ((-63) + z * ((-27) + z * ((-2) + z * ((-43) + z * ((-67) + z * ((-53) + z * ((-85) + z * ((-79) + z * ((-46) + z * ((-38) + z * ((-14) + z * 7))))))))))))))))))))))))))))))))))))))


def pow7_32 {R : Type*} [CommRing R] (z : R) : R := (58 + z * (49 + z * (70 + z * (95 + z * (57 + z * (114 + z * (12 + z * (8 + z * (75 + z * (101 + z * (106 + z * (12 + z * (34 + z * (93 + z * (106 + z * (26 + z * (36 + z * (130 + z * (66 + z * 130)))))))))))))))))))

def pow7_32_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (90 + z * (10 + z * (96 + z * (79 + z * (25 + z * (1 + z * (100 + z * (52 + z * (29 + z * (81 + z * (60 + z * (104 + z * (37 + z * (42 + z * (126 + z * (94 + z * (8 + z * 39))))))))))))))))))

def pow7_32_mul_t {R : Type*} [CommRing R] (z : R) : R := (36 + z * (94 + z * (200 + z * (266 + z * (305 + z * (267 + z * (241 + z * (210 + z * (77 + z * (189 + z * (289 + z * (323 + z * (209 + z * (302 + z * (274 + z * (98 + z * (137 + z * (132 + z * (270 + z * (189 + z * (172 + z * (190 + z * (149 + z * ((-35) + z * ((-23) + z * (111 + z * ((-49) + z * (49 + z * (64 + z * (15 + z * (89 + z * ((-62) + z * (32 + z * (32 + z * ((-28) + z * (53 + z * (66 + z * (54 + z * 35))))))))))))))))))))))))))))))))))))))


def pow7_64 {R : Type*} [CommRing R] (z : R) : R := (21 + z * (128 + z * (25 + z * (113 + z * (24 + z * (69 + z * (31 + z * (8 + z * (112 + z * (25 + z * (51 + z * (72 + z * (59 + z * (81 + z * (23 + z * (93 + z * (1 + z * (95 + z * (69 + z * 29)))))))))))))))))))

def pow7_64_q {R : Type*} [CommRing R] (z : R) : R := (59 + z * (74 + z * (112 + z * (102 + z * (72 + z * (65 + z * (105 + z * (42 + z * (117 + z * (72 + z * (69 + z * (110 + z * (53 + z * (2 + z * (37 + z * (60 + z * (75 + z * (64 + z * 1))))))))))))))))))

def pow7_64_mul_t {R : Type*} [CommRing R] (z : R) : R := (3 + z * ((-7) + z * ((-18) + z * (10 + z * ((-5) + z * (33 + z * ((-17) + z * ((-63) + z * ((-62) + z * ((-78) + z * ((-39) + z * ((-128) + z * ((-79) + z * ((-64) + z * ((-11) + z * ((-57) + z * ((-158) + z * (27 + z * (139 + z * (113 + z * (44 + z * (67 + z * (297 + z * (174 + z * (114 + z * (4 + z * (180 + z * (291 + z * (185 + z * (177 + z * (142 + z * (279 + z * (245 + z * (192 + z * (128 + z * (135 + z * (258 + z * (130 + z * 129))))))))))))))))))))))))))))))))))))))


def pow7_65 {R : Type*} [CommRing R] (z : R) : R := (24 + z * (51 + z * (61 + z * (125 + z * (7 + z * (47 + z * (129 + z * (113 + z * (120 + z * (125 + z * (114 + z * (92 + z * (128 + z * (99 + z * (72 + z * (60 + z * (2 + z * (92 + z * (17 + z * 90)))))))))))))))))))

def pow7_65_q {R : Type*} [CommRing R] (z : R) : R := (35 + z * (72 + z * (41 + z * (13 + z * (128 + z * (91 + z * (88 + z * (67 + z * (91 + z * (72 + z * (125 + z * (18 + z * (15 + z * (1 + z * (34 + z * (104 + z * (8 + z * (69 + z * 83))))))))))))))))))

def pow7_65_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-2) + z * (49 + z * (87 + z * (131 + z * (103 + z * (61 + z * (7 + z * (86 + z * (68 + z * (56 + z * (99 + z * (153 + z * (86 + z * (169 + z * (233 + z * (176 + z * (179 + z * (176 + z * (287 + z * (325 + z * (224 + z * (274 + z * (134 + z * (89 + z * (302 + z * (261 + z * (135 + z * (221 + z * (192 + z * (217 + z * (188 + z * (204 + z * (133 + z * (65 + z * (53 + z * (102 + z * (38 + z * (1 + z * 8))))))))))))))))))))))))))))))))))))))


def pow7_130 {R : Type*} [CommRing R] (z : R) : R := (63 + z * (41 + z * (42 + z * (79 + z * (92 + z * (126 + z * (75 + z * (18 + z * (41 + z * (122 + z * (76 + z * (44 + z * (80 + z * (75 + z * (117 + z * (101 + z * (117 + z * (76 + z * (120 + z * 75)))))))))))))))))))

def pow7_130_q {R : Type*} [CommRing R] (z : R) : R := (81 + z * (103 + z * (35 + z * (33 + z * (7 + z * (42 + z * (13 + z * (53 + z * (66 + z * (10 + z * (43 + z * (100 + z * (79 + z * (33 + z * (2 + z * (76 + z * (40 + z * (58 + z * 109))))))))))))))))))

def pow7_130_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-27) + z * ((-50) + z * ((-48) + z * (3 + z * (34 + z * ((-29) + z * (70 + z * (59 + z * (134 + z * (279 + z * (294 + z * (333 + z * (323 + z * (408 + z * (558 + z * (644 + z * (528 + z * (558 + z * (598 + z * (513 + z * (670 + z * (644 + z * (594 + z * (384 + z * (435 + z * (500 + z * (344 + z * (304 + z * (205 + z * (149 + z * (100 + z * (120 + z * (144 + z * ((-2) + z * ((-2) + z * ((-61) + z * (50 + z * ((-32) + z * 61))))))))))))))))))))))))))))))))))))))


def pow7_131 {R : Type*} [CommRing R] (z : R) : R := (57 + z * (78 + z * (44 + z * (26 + z * (25 + z * (86 + z * (38 + z * (57 + z * (89 + z * (114 + z * (98 + z * (112 + z * (97 + z * (61 + z * (26 + z * (38 + z * (48 + z * (1 + z * (43 + z * 86)))))))))))))))))))

def pow7_131_q {R : Type*} [CommRing R] (z : R) : R := (66 + z * (17 + z * (36 + z * (37 + z * (95 + z * (9 + z * (86 + z * (10 + z * (95 + z * (129 + z * (31 + z * (20 + z * (45 + z * (95 + z * (95 + z * (44 + z * (21 + z * (4 + z * 43))))))))))))))))))

def pow7_131_mul_t {R : Type*} [CommRing R] (z : R) : R := (9 + z * (49 + z * (56 + z * (97 + z * (98 + z * (145 + z * (221 + z * (217 + z * (128 + z * (172 + z * (313 + z * (272 + z * (385 + z * (320 + z * (373 + z * (443 + z * (540 + z * (537 + z * (630 + z * (625 + z * (575 + z * (607 + z * (657 + z * (626 + z * (536 + z * (482 + z * (558 + z * (521 + z * (524 + z * (437 + z * (411 + z * (376 + z * (360 + z * (273 + z * (258 + z * (253 + z * (167 + z * (73 + z * 22))))))))))))))))))))))))))))))))))))))


def pow8_2 {R : Type*} [CommRing R] (z : R) : R := (16 + z * (33 + z * (49 + z * (37 + z * (114 + z * (52 + z * (110 + z * (4 + z * (15 + z * (105 + z * (112 + z * (112 + z * (100 + z * (121 + z * (74 + z * (18 + z * (105 + z * (55 + z * (48 + z * 96)))))))))))))))))))

def pow8_2_q {R : Type*} [CommRing R] (z : R) : R := (83 + z * (52 + z * (79 + z * (119 + z * (108 + z * (114 + z * (49 + z * (115 + z * (55 + z * (35 + z * (64 + z * (50 + z * (77 + z * (70 + z * (52 + z * (76 + z * (38 + z * (30 + z * 60))))))))))))))))))

def pow8_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-7) + z * (18 + z * ((-5) + z * ((-39) + z * ((-110) + z * ((-133) + z * ((-66) + z * ((-152) + z * ((-151) + z * ((-81) + z * (6 + z * ((-40) + z * ((-70) + z * ((-9) + z * ((-41) + z * ((-118) + z * ((-66) + z * ((-1) + z * ((-40) + z * (34 + z * (74 + z * (81 + z * ((-9) + z * ((-32) + z * (87 + z * (5 + z * ((-23) + z * (87 + z * (85 + z * (20 + z * (41 + z * (8 + z * ((-9) + z * ((-52) + z * ((-25) + z * (8 + z * ((-27) + z * (26 + z * 56))))))))))))))))))))))))))))))))))))))


def pow8_4 {R : Type*} [CommRing R] (z : R) : R := (41 + z * (0 + z * (46 + z * (1 + z * (66 + z * (31 + z * (23 + z * (83 + z * (73 + z * (95 + z * (125 + z * (126 + z * (23 + z * (75 + z * (40 + z * (105 + z * (42 + z * (51 + z * (29 + z * 35)))))))))))))))))))

def pow8_4_q {R : Type*} [CommRing R] (z : R) : R := (96 + z * (130 + z * (77 + z * (15 + z * (106 + z * (49 + z * (82 + z * (7 + z * (77 + z * (28 + z * (85 + z * (31 + z * (16 + z * (18 + z * (76 + z * (90 + z * (117 + z * (23 + z * 46))))))))))))))))))

def pow8_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-35) + z * ((-76) + z * ((-103) + z * ((-80) + z * ((-94) + z * ((-134) + z * ((-111) + z * ((-44) + z * ((-79) + z * ((-167) + z * (2 + z * ((-83) + z * ((-68) + z * ((-33) + z * (155 + z * (215 + z * (151 + z * (88 + z * (138 + z * (119 + z * (254 + z * (223 + z * (441 + z * (381 + z * (301 + z * (379 + z * (226 + z * (199 + z * (326 + z * (319 + z * (305 + z * (161 + z * (168 + z * (59 + z * ((-11) + z * (107 + z * (65 + z * (47 + z * 70))))))))))))))))))))))))))))))))))))))


def pow8_16 {R : Type*} [CommRing R] (z : R) : R := (44 + z * (129 + z * (56 + z * (84 + z * (100 + z * (124 + z * (66 + z * (74 + z * (73 + z * (124 + z * (9 + z * (43 + z * (100 + z * (65 + z * (96 + z * (107 + z * (33 + z * (30 + z * (123 + z * 86)))))))))))))))))))

def pow8_16_q {R : Type*} [CommRing R] (z : R) : R := (50 + z * (5 + z * (51 + z * (102 + z * (74 + z * (100 + z * (80 + z * (56 + z * (87 + z * (61 + z * (23 + z * (28 + z * (57 + z * (102 + z * (88 + z * (123 + z * (78 + z * (57 + z * 58))))))))))))))))))

def pow8_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (60 + z * (29 + z * (133 + z * (103 + z * (11 + z * (94 + z * (19 + z * ((-2) + z * (109 + z * (53 + z * (110 + z * (36 + z * ((-14) + z * ((-97) + z * ((-51) + z * ((-50) + z * ((-50) + z * ((-1) + z * ((-22) + z * ((-48) + z * ((-197) + z * ((-124) + z * ((-95) + z * ((-139) + z * ((-46) + z * ((-66) + z * ((-122) + z * ((-95) + z * ((-100) + z * ((-94) + z * ((-88) + z * ((-63) + z * ((-28) + z * ((-15) + z * ((-32) + z * (18 + z * (8 + z * ((-7) + z * 21))))))))))))))))))))))))))))))))))))))


def pow8_32 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (37 + z * (47 + z * (101 + z * (26 + z * (13 + z * (120 + z * (11 + z * (4 + z * (85 + z * (49 + z * (101 + z * (62 + z * (65 + z * (49 + z * (100 + z * (5 + z * (125 + z * (113 + z * 110)))))))))))))))))))

def pow8_32_q {R : Type*} [CommRing R] (z : R) : R := (62 + z * (113 + z * (106 + z * (86 + z * (40 + z * (99 + z * (71 + z * (82 + z * (11 + z * (102 + z * (53 + z * (33 + z * (26 + z * (52 + z * (113 + z * (111 + z * (29 + z * (35 + z * 60))))))))))))))))))

def pow8_32_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-9) + z * (21 + z * (53 + z * (29 + z * (105 + z * (124 + z * (173 + z * (128 + z * (195 + z * (210 + z * (242 + z * (92 + z * (186 + z * (225 + z * (140 + z * (268 + z * (315 + z * (226 + z * (232 + z * (379 + z * (371 + z * (335 + z * (240 + z * (371 + z * (356 + z * (103 + z * (148 + z * (316 + z * (178 + z * (111 + z * (195 + z * (154 + z * (172 + z * (184 + z * (87 + z * (46 + z * (110 + z * (131 + z * 56))))))))))))))))))))))))))))))))))))))


def pow8_64 {R : Type*} [CommRing R] (z : R) : R := (40 + z * (9 + z * (64 + z * (50 + z * (45 + z * (95 + z * (117 + z * (2 + z * (47 + z * (30 + z * (77 + z * (95 + z * (47 + z * (9 + z * (127 + z * (86 + z * (126 + z * (121 + z * (96 + z * 9)))))))))))))))))))

def pow8_64_q {R : Type*} [CommRing R] (z : R) : R := (43 + z * (34 + z * (59 + z * (89 + z * (93 + z * (35 + z * (130 + z * (122 + z * (5 + z * (60 + z * (17 + z * (5 + z * (116 + z * (113 + z * (94 + z * (55 + z * (129 + z * (77 + z * 48))))))))))))))))))

def pow8_64_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * ((-20) + z * ((-35) + z * ((-30) + z * ((-46) + z * ((-67) + z * ((-55) + z * ((-130) + z * ((-177) + z * ((-64) + z * ((-139) + z * ((-257) + z * ((-17) + z * ((-122) + z * ((-234) + z * ((-93) + z * ((-149) + z * ((-192) + z * ((-150) + z * ((-142) + z * (19 + z * (79 + z * ((-52) + z * ((-10) + z * (49 + z * ((-90) + z * (57 + z * (84 + z * (199 + z * (128 + z * (223 + z * (68 + z * (155 + z * (79 + z * (149 + z * (106 + z * (246 + z * (165 + z * 92))))))))))))))))))))))))))))))))))))))


def pow8_65 {R : Type*} [CommRing R] (z : R) : R := (78 + z * (11 + z * (55 + z * (1 + z * (99 + z * (92 + z * (65 + z * (59 + z * (52 + z * (62 + z * (115 + z * (61 + z * (77 + z * (117 + z * (58 + z * (79 + z * (109 + z * (52 + z * (76 + z * 35)))))))))))))))))))

def pow8_65_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-8) + z * ((-43) + z * ((-43) + z * ((-42) + z * ((-42) + z * ((-99) + z * ((-90) + z * ((-39) + z * ((-147) + z * ((-121) + z * ((-76) + z * (3 + z * ((-44) + z * ((-62) + z * ((-54) + z * (120 + z * (12 + z * ((-49) + z * (1 + z * ((-11) + z * ((-52) + z * (45 + z * (66 + z * (17 + z * (173 + z * (129 + z * (159 + z * (129 + z * (140 + z * (86 + z * (70 + z * ((-79) + z * ((-31) + z * (11 + z * ((-40) + z * (20 + z * (55 + z * (6 + z * 5))))))))))))))))))))))))))))))))))))))


def pow8_130 {R : Type*} [CommRing R] (z : R) : R := (39 + z * (101 + z * (30 + z * (51 + z * (34 + z * (94 + z * (59 + z * (129 + z * (80 + z * (21 + z * (107 + z * (42 + z * (30 + z * (117 + z * (115 + z * (58 + z * (77 + z * (100 + z * 75))))))))))))))))))

def pow8_130_q {R : Type*} [CommRing R] (z : R) : R := (3 + z * (19 + z * (5 + z * (9 + z * (95 + z * (118 + z * (26 + z * (45 + z * (130 + z * (75 + z * (122 + z * (126 + z * (74 + z * (31 + z * (124 + z * (63 + z * (58 + z * (57 + z * 46))))))))))))))))))

def pow8_130_mul_t {R : Type*} [CommRing R] (z : R) : R := (45 + z * (4 + z * (56 + z * ((-5) + z * (94 + z * (29 + z * (56 + z * (47 + z * (31 + z * (5 + z * (74 + z * (60 + z * ((-22) + z * ((-9) + z * (115 + z * (68 + z * ((-17) + z * (114 + z * (169 + z * (40 + z * (178 + z * (76 + z * (99 + z * (129 + z * (120 + z * (131 + z * (129 + z * (47 + z * (174 + z * (141 + z * (84 + z * (168 + z * (131 + z * (46 + z * (79 + z * (46 + z * (22 + z * (17 + z * 9))))))))))))))))))))))))))))))))))))))


def pow8_131 {R : Type*} [CommRing R] (z : R) : R := (35 + z * (43 + z * (109 + z * (0 + z * (108 + z * (101 + z * (85 + z * (95 + z * (92 + z * (72 + z * (7 + z * (15 + z * (129 + z * (44 + z * (70 + z * (59 + z * (9 + z * (99 + z * (55 + z * 77)))))))))))))))))))

def pow8_131_q {R : Type*} [CommRing R] (z : R) : R := (49 + z * (95 + z * (9 + z * (127 + z * (49 + z * (0 + z * (14 + z * (75 + z * (56 + z * (75 + z * (102 + z * (43 + z * (87 + z * (111 + z * (18 + z * (21 + z * (85 + z * 31)))))))))))))))))

def pow8_131_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-2) + z * (13 + z * (24 + z * ((-25) + z * ((-30) + z * ((-47) + z * (46 + z * (58 + z * ((-12) + z * (52 + z * (119 + z * (45 + z * (26 + z * (128 + z * (67 + z * (139 + z * (157 + z * (136 + z * (169 + z * (197 + z * (78 + z * (59 + z * (197 + z * (225 + z * (164 + z * (196 + z * (259 + z * (147 + z * (58 + z * (93 + z * (71 + z * (17 + z * (50 + z * (82 + z * (31 + z * (27 + z * (74 + z * 49)))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod131

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

def pow1_139_q {R : Type*} [CommRing R] (_ : R) : R := 106

end DimensionTen.Mod139

end

end OAI
end


