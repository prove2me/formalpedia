-- Prove2me | Definitions.Def_OAIQ033D003
-- name    : OAIQ033D003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T01:45:55.450029+00:00
-- url     : https://prove2.me/theorems/e383e383-e9b4-4064-bed3-a81bc57dcc5d
-- title:
--   Definitions bundle OAIQ033D003 of the split of OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DimensionTen.main_pair`, carved from OpenAI's openai/math development (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 110 declarations of OpenAI's Lean: 107 definitions and 3 theorems. The definitions and types are `OAI.DimensionTen.Border.W14`, `OAI.DimensionTen.Border.W15`, `OAI.DimensionTen.Border.W16`, `OAI.DimensionTen.Border.W17`, `OAI.DimensionTen.Border.W18`, `OAI.DimensionTen.Border.W19`, `OAI.DimensionTen.Border.W5`, `OAI.DimensionTen.Border.W6`, `OAI.DimensionTen.Border.W7`, `OAI.DimensionTen.Border.W8`, `OAI.DimensionTen.Border.W9`, `OAI.DimensionTen.Border.cofactorCoeffs`, `OAI.DimensionTen.Border.firstTen`, `OAI.DimensionTen.Border.high`, `OAI.DimensionTen.Border.homogeneousLow`, `OAI.DimensionTen.Border.low`, `OAI.DimensionTen.Border.mon`, `OAI.DimensionTen.Border.monExps`, `OAI.DimensionTen.Border.pencilExplicit`, `OAI.DimensionTen.Border.quadraticPairs`, `OAI.DimensionTen.ExactDimensionTenPair`, `OAI.DimensionTen.Mod131.a17`, `OAI.DimensionTen.Mod131.b17`, `OAI.DimensionTen.Mod131.bezout17_t`, `OAI.DimensionTen.Mod131.da`, `OAI.DimensionTen.Mod131.db`, `OAI.DimensionTen.Mod131.derivative_extra`, `OAI.DimensionTen.Mod131.df`, `OAI.DimensionTen.Mod131.div17_f`, `OAI.DimensionTen.Mod131.div17_u17`, `OAI.DimensionTen.Mod131.f`, `OAI.DimensionTen.Mod131.factor17_f_t`, `OAI.DimensionTen.Mod131.factor17_u17_t`, `OAI.DimensionTen.Mod131.g17`, `OAI.DimensionTen.Mod131.pow10_130`, `OAI.DimensionTen.Mod131.pow10_130_mul_t`, `OAI.DimensionTen.Mod131.pow10_130_q`, `OAI.DimensionTen.Mod131.pow10_131`, `OAI.DimensionTen.Mod131.pow10_131_mul_t`, `OAI.DimensionTen.Mod131.pow10_131_q` and 67 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Quantum/DimensionTen, in whole or in part: `Quantum_DimensionTen_BorderData`, `Quantum_DimensionTen_Cofactors`, `Quantum_DimensionTen_EvaluationMinors`, `Quantum_DimensionTen_GaloisCertificate`, `Quantum_DimensionTen_MinorData`, `Quantum_DimensionTen_Mod131Model`, `Quantum_DimensionTen_Mod131Powers01`, `Quantum_DimensionTen_Mod131Powers05`, `Quantum_DimensionTen_Mod131Powers06`, `Quantum_DimensionTen_Mod131Result`, `Quantum_DimensionTen_PencilModel`, `Quantum_DimensionTen_PolynomialData`, `Quantum_DimensionTen_QuadraticBounds`, `Quantum_DimensionTen_RootReduction`, `Quantum_PPTSquare_GaloisAction`.
--
--   **Imports.** It imports the published bundle `Def_DimensionTenPair`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ033D011`, `OAIQ033D012` and `OAIQ033D013`; the statements `OAI_DimensionTen_exists_nineteen_cycle_of_mod139` and `OAI.DimensionTen.exists_swap_of_mod131`.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Quantum/DimensionTen at commit adc7f12

import Mathlib
import Definitions.Def_DimensionTenPair

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_BorderData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

def monExps : Fin 35 → Fin 3 → ℕ :=
  ![![0, 0, 0], ![0, 0, 1], ![0, 1, 0], ![1, 0, 0], ![0, 0, 2], ![0, 1, 1], ![0, 2, 0], ![1, 0, 1], ![1, 1, 0], ![2, 0, 0], ![0, 0, 3], ![0, 1, 2], ![0, 2, 1], ![0, 3, 0], ![1, 0, 2], ![1, 1, 1], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0], ![3, 0, 0], ![0, 0, 4], ![0, 1, 3], ![0, 2, 2], ![0, 3, 1], ![0, 4, 0], ![1, 0, 3], ![1, 1, 2], ![1, 2, 1], ![1, 3, 0], ![2, 0, 2], ![2, 1, 1], ![2, 2, 0], ![3, 0, 1], ![3, 1, 0], ![4, 0, 0]]

def mon {R : Type*} [CommRing R] (t : Fin 3 → R) (i : Fin 35) : R :=
  ∏ j : Fin 3, t j ^ monExps i j

def low {R : Type*} [CommRing R] (t : Fin 3 → R) : Fin 20 → R :=
  fun i => mon t (Fin.castLE (by decide) i)

def high {R : Type*} [CommRing R] (t : Fin 3 → R) : Fin 15 → R :=
  fun i => mon t (i.natAdd 20)

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod131Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131
def f {R : Type*} [CommRing R] (z : R) : R := (50 + z * (47 + z * (64 + z * (23 + z * (71 + z * (114 + z * (2 + z * (70 + z * (100 + z * (54 + z * (17 + z * (116 + z * (85 + z * (77 + z * (7 + z * (37 + z * (86 + z * (49 + z * (59 + z * (66 + z * 1))))))))))))))))))))

end DimensionTen.Mod131

end

end OAI
end

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

def pow1_131_q {R : Type*} [CommRing R] (_ : R) : R := 96

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod131Powers05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131


def pow10_2 {R : Type*} [CommRing R] (z : R) : R := (89 + z * (7 + z * (14 + z * (38 + z * (98 + z * (61 + z * (43 + z * (42 + z * (52 + z * (99 + z * (82 + z * (100 + z * (4 + z * (129 + z * (122 + z * (76 + z * (94 + z * (50 + z * (20 + z * 104)))))))))))))))))))

def pow10_2_q {R : Type*} [CommRing R] (z : R) : R := (115 + z * (69 + z * (19 + z * (59 + z * (129 + z * (98 + z * (127 + z * (41 + z * (44 + z * (45 + z * (5 + z * (38 + z * (109 + z * (90 + z * (28 + z * (81 + z * (89 + z * (17 + z * 15))))))))))))))))))

def pow10_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-18) + z * ((-10) + z * ((-21) + z * (6 + z * ((-33) + z * ((-60) + z * (51 + z * (61 + z * ((-13) + z * ((-14) + z * (71 + z * ((-21) + z * (16 + z * ((-17) + z * ((-54) + z * ((-77) + z * ((-206) + z * ((-266) + z * (47 + z * ((-31) + z * ((-65) + z * ((-118) + z * ((-58) + z * ((-88) + z * (25 + z * ((-16) + z * (32 + z * ((-82) + z * ((-104) + z * ((-143) + z * (105 + z * ((-23) + z * ((-76) + z * (21 + z * ((-27) + z * ((-41) + z * (113 + z * (77 + z * 14))))))))))))))))))))))))))))))))))))))


def pow10_4 {R : Type*} [CommRing R] (z : R) : R := (25 + z * (31 + z * (112 + z * (20 + z * (105 + z * (13 + z * (64 + z * (82 + z * (14 + z * (28 + z * (122 + z * (80 + z * (59 + z * (108 + z * (42 + z * (32 + z * (32 + z * (4 + z * (76 + z * 74)))))))))))))))))))

def pow10_4_q {R : Type*} [CommRing R] (z : R) : R := (116 + z * (117 + z * (115 + z * (66 + z * (96 + z * (3 + z * (123 + z * (73 + z * (31 + z * (81 + z * (66 + z * (81 + z * (63 + z * (92 + z * (53 + z * (128 + z * (115 + z * (62 + z * 74))))))))))))))))))

def pow10_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (16 + z * ((-77) + z * ((-124) + z * ((-91) + z * ((-62) + z * ((-151) + z * ((-176) + z * ((-159) + z * ((-168) + z * ((-119) + z * ((-90) + z * ((-215) + z * ((-256) + z * ((-75) + z * ((-59) + z * ((-114) + z * ((-96) + z * ((-127) + z * ((-106) + z * (27 + z * ((-78) + z * ((-20) + z * (26 + z * (117 + z * (198 + z * (75 + z * (76 + z * (156 + z * (142 + z * (141 + z * (212 + z * ((-9) + z * (152 + z * (99 + z * ((-20) + z * (50 + z * (17 + z * ((-6) + z * 82))))))))))))))))))))))))))))))))))))))


def pow10_8 {R : Type*} [CommRing R] (z : R) : R := (97 + z * (93 + z * (10 + z * (98 + z * (56 + z * (4 + z * (57 + z * (3 + z * (109 + z * (4 + z * (25 + z * (73 + z * (85 + z * (61 + z * (81 + z * (7 + z * (2 + z * (88 + z * (25 + z * 66)))))))))))))))))))

def pow10_8_q {R : Type*} [CommRing R] (z : R) : R := (42 + z * (8 + z * (130 + z * (89 + z * (95 + z * (101 + z * (98 + z * (36 + z * (71 + z * (68 + z * (50 + z * (25 + z * (128 + z * (129 + z * (82 + z * (46 + z * (110 + z * (126 + z * 105))))))))))))))))))

def pow10_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-12) + z * ((-7) + z * ((-23) + z * ((-32) + z * ((-11) + z * ((-91) + z * ((-1) + z * ((-183) + z * ((-32) + z * ((-120) + z * ((-170) + z * ((-106) + z * ((-33) + z * ((-170) + z * ((-92) + z * ((-108) + z * ((-173) + z * ((-184) + z * ((-313) + z * ((-253) + z * ((-117) + z * ((-305) + z * ((-194) + z * ((-99) + z * ((-221) + z * ((-198) + z * ((-103) + z * ((-187) + z * ((-142) + z * ((-127) + z * ((-140) + z * ((-73) + z * ((-53) + z * ((-130) + z * ((-116) + z * ((-111) + z * ((-63) + z * (32 + z * 41))))))))))))))))))))))))))))))))))))))


def pow10_16 {R : Type*} [CommRing R] (z : R) : R := (2 + z * (75 + z * (11 + z * (126 + z * (115 + z * (72 + z * (75 + z * (37 + z * (12 + z * (97 + z * (74 + z * (26 + z * (92 + z * (87 + z * (27 + z * (42 + z * (114 + z * (39 + z * (23 + z * 67)))))))))))))))))))

def pow10_16_q {R : Type*} [CommRing R] (z : R) : R := (65 + z * (31 + z * (18 + z * (90 + z * (87 + z * (58 + z * (25 + z * (95 + z * (120 + z * (117 + z * (85 + z * (71 + z * (49 + z * (83 + z * (50 + z * (37 + z * (39 + z * (74 + z * 33))))))))))))))))))

def pow10_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (47 + z * (102 + z * (31 + z * (91 + z * (107 + z * ((-74) + z * (45 + z * ((-19) + z * ((-90) + z * ((-58) + z * ((-186) + z * ((-81) + z * ((-104) + z * ((-176) + z * ((-8) + z * ((-182) + z * ((-261) + z * ((-136) + z * ((-184) + z * ((-233) + z * ((-120) + z * ((-287) + z * ((-185) + z * ((-163) + z * ((-244) + z * ((-50) + z * ((-207) + z * ((-90) + z * ((-129) + z * ((-87) + z * ((-9) + z * (78 + z * ((-25) + z * ((-28) + z * ((-19) + z * ((-30) + z * (41 + z * (8 + z * 33))))))))))))))))))))))))))))))))))))))


def pow10_32 {R : Type*} [CommRing R] (z : R) : R := (83 + z * (71 + z * (91 + z * (87 + z * (12 + z * (113 + z * (98 + z * (9 + z * (16 + z * (2 + z * (37 + z * (82 + z * (57 + z * (7 + z * (130 + z * (86 + z * (96 + z * (22 + z * (11 + z * 15)))))))))))))))))))

def pow10_32_q {R : Type*} [CommRing R] (z : R) : R := (22 + z * (128 + z * (5 + z * (88 + z * (87 + z * (67 + z * (84 + z * (90 + z * (67 + z * (21 + z * (120 + z * (39 + z * (18 + z * (24 + z * (111 + z * (119 + z * (29 + z * (117 + z * 35))))))))))))))))))

def pow10_32_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-9) + z * ((-55) + z * ((-16) + z * ((-86) + z * (47 + z * ((-35) + z * ((-4) + z * (142 + z * ((-25) + z * ((-20) + z * (44 + z * ((-83) + z * ((-130) + z * (110 + z * ((-34) + z * ((-56) + z * (67 + z * ((-15) + z * ((-72) + z * ((-28) + z * (67 + z * (0 + z * (10 + z * ((-50) + z * ((-32) + z * (28 + z * ((-104) + z * ((-88) + z * (61 + z * (46 + z * ((-66) + z * (39 + z * (62 + z * ((-97) + z * ((-46) + z * (49 + z * ((-31) + z * (5 + z * 34))))))))))))))))))))))))))))))))))))))


def pow10_64 {R : Type*} [CommRing R] (z : R) : R := (24 + z * (37 + z * (9 + z * (128 + z * (96 + z * (57 + z * (44 + z * (88 + z * (100 + z * (107 + z * (28 + z * (87 + z * (111 + z * (71 + z * (129 + z * (91 + z * (54 + z * (12 + z * (3 + z * 85)))))))))))))))))))

def pow10_64_q {R : Type*} [CommRing R] (z : R) : R := (98 + z * (4 + z * (43 + z * (48 + z * (123 + z * (8 + z * (92 + z * (59 + z * (8 + z * (8 + z * (78 + z * (19 + z * (97 + z * (100 + z * (95 + z * (5 + z * (6 + z * (21 + z * 94))))))))))))))))))

def pow10_64_mul_t {R : Type*} [CommRing R] (z : R) : R := (15 + z * (53 + z * (88 + z * (155 + z * (33 + z * (111 + z * (186 + z * (93 + z * (60 + z * ((-47) + z * (20 + z * ((-22) + z * ((-25) + z * ((-44) + z * (23 + z * ((-43) + z * (246 + z * (212 + z * ((-45) + z * (3 + z * (70 + z * ((-4) + z * ((-100) + z * ((-259) + z * ((-96) + z * ((-130) + z * ((-24) + z * (37 + z * (75 + z * ((-55) + z * (49 + z * ((-7) + z * (12 + z * ((-17) + z * ((-36) + z * ((-22) + z * ((-47) + z * ((-45) + z * 1))))))))))))))))))))))))))))))))))))))


def pow10_65 {R : Type*} [CommRing R] (z : R) : R := (123 + z * (101 + z * (0 + z * (21 + z * (122 + z * (2 + z * (53 + z * (35 + z * (79 + z * (30 + z * (66 + z * (55 + z * (59 + z * (85 + z * (97 + z * (70 + z * (115 + z * (103 + z * (127 + z * 99)))))))))))))))))))

def pow10_65_q {R : Type*} [CommRing R] (z : R) : R := (18 + z * (24 + z * (8 + z * (28 + z * (117 + z * (48 + z * (67 + z * (113 + z * (82 + z * (59 + z * (85 + z * (50 + z * (25 + z * (60 + z * (63 + z * (20 + z * (10 + z * (31 + z * 118))))))))))))))))))

def pow10_65_mul_t {R : Type*} [CommRing R] (z : R) : R := (3 + z * (12 + z * (9 + z * (55 + z * (62 + z * (49 + z * (59 + z * (91 + z * (95 + z * (123 + z * (149 + z * (88 + z * (48 + z * (155 + z * (138 + z * (146 + z * (163 + z * (138 + z * (55 + z * (162 + z * (120 + z * (193 + z * (49 + z * ((-48) + z * (104 + z * ((-18) + z * (12 + z * (136 + z * (28 + z * ((-33) + z * (9 + z * (76 + z * (102 + z * (53 + z * (14 + z * ((-22) + z * ((-60) + z * (25 + z * 27))))))))))))))))))))))))))))))))))))))


def pow10_130 {R : Type*} [CommRing R] (z : R) : R := (28 + z * (128 + z * (125 + z * (48 + z * (50 + z * (77 + z * (78 + z * (86 + z * (116 + z * (125 + z * (98 + z * (67 + z * (19 + z * (79 + z * (58 + z * (107 + z * (107 + z * (76 + z * (104 + z * 95)))))))))))))))))))

def pow10_130_q {R : Type*} [CommRing R] (z : R) : R := (116 + z * (29 + z * (107 + z * (3 + z * (99 + z * (128 + z * (122 + z * (8 + z * (120 + z * (31 + z * (68 + z * (31 + z * (63 + z * (94 + z * (12 + z * (1 + z * (77 + z * (6 + z * 107))))))))))))))))))

def pow10_130_mul_t {R : Type*} [CommRing R] (z : R) : R := (71 + z * (136 + z * ((-31) + z * ((-35) + z * (102 + z * ((-30) + z * ((-121) + z * ((-98) + z * (23 + z * ((-165) + z * ((-107) + z * ((-94) + z * ((-33) + z * ((-235) + z * (129 + z * (8 + z * (68 + z * (86 + z * (198 + z * (260 + z * (157 + z * ((-30) + z * (246 + z * (135 + z * (105 + z * (199 + z * (285 + z * (303 + z * (329 + z * (271 + z * (374 + z * (365 + z * (416 + z * (393 + z * (302 + z * (292 + z * (227 + z * (138 + z * 74))))))))))))))))))))))))))))))))))))))


def pow10_131 {R : Type*} [CommRing R] (z : R) : R := (30 + z * (7 + z * (120 + z * (55 + z * (19 + z * (59 + z * (37 + z * (77 + z * (0 + z * (130 + z * (127 + z * (41 + z * (111 + z * (126 + z * (13 + z * (111 + z * (36 + z * (116 + z * (125 + z * 1)))))))))))))))))))

def pow10_131_q {R : Type*} [CommRing R] (z : R) : R := (1 + z * (81 + z * (81 + z * (114 + z * (114 + z * (17 + z * (55 + z * (62 + z * (72 + z * (84 + z * (14 + z * (29 + z * (29 + z * (126 + z * (100 + z * (10 + z * (56 + z * (78 + z * 24))))))))))))))))))

def pow10_131_mul_t {R : Type*} [CommRing R] (z : R) : R := (12 + z * (40 + z * (66 + z * (21 + z * (13 + z * (48 + z * (84 + z * (179 + z * (134 + z * (133 + z * (161 + z * (104 + z * (105 + z * (169 + z * (153 + z * (129 + z * (167 + z * (105 + z * (64 + z * (200 + z * (219 + z * (169 + z * (144 + z * (304 + z * (159 + z * (68 + z * (104 + z * (154 + z * (119 + z * (39 + z * (26 + z * (127 + z * (5 + z * (62 + z * (119 + z * (53 + z * (79 + z * (115 + z * 31))))))))))))))))))))))))))))))))))))))

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
def pow11_2 {R : Type*} [CommRing R] (z : R) : R := (44 + z * (50 + z * (62 + z * (14 + z * (102 + z * (58 + z * (95 + z * (51 + z * (111 + z * (81 + z * (25 + z * (59 + z * (41 + z * (128 + z * (55 + z * (121 + z * (53 + z * (15 + z * (61 + z * 66)))))))))))))))))))

def pow11_2_q {R : Type*} [CommRing R] (z : R) : R := (80 + z * (37 + z * (38 + z * (79 + z * (13 + z * (78 + z * (87 + z * (105 + z * (1 + z * (26 + z * (93 + z * (37 + z * (95 + z * (121 + z * (75 + z * (96 + z * (117 + z * (53 + z * 1))))))))))))))))))

def pow11_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-24) + z * ((-40) + z * ((-12) + z * ((-38) + z * (22 + z * ((-40) + z * ((-55) + z * ((-68) + z * ((-124) + z * (35 + z * ((-102) + z * ((-27) + z * (110 + z * ((-26) + z * ((-19) + z * (98 + z * ((-29) + z * (21 + z * ((-50) + z * (216 + z * (288 + z * (1 + z * (281 + z * (68 + z * (138 + z * (216 + z * (131 + z * (386 + z * (244 + z * (59 + z * (315 + z * (96 + z * (10 + z * (115 + z * (51 + z * (138 + z * (93 + z * (1 + z * 0))))))))))))))))))))))))))))))))))))))


def pow11_4 {R : Type*} [CommRing R] (z : R) : R := (42 + z * (92 + z * (74 + z * (47 + z * (7 + z * (34 + z * (45 + z * (105 + z * (45 + z * (113 + z * (31 + z * (129 + z * (61 + z * (95 + z * (109 + z * (89 + z * (13 + z * (81 + z * (116 + z * 14)))))))))))))))))))

def pow11_4_q {R : Type*} [CommRing R] (z : R) : R := (106 + z * (128 + z * (106 + z * (11 + z * (107 + z * (86 + z * (116 + z * (106 + z * (33 + z * (19 + z * (78 + z * (24 + z * (0 + z * (49 + z * (104 + z * (114 + z * (31 + z * (110 + z * 33))))))))))))))))))

def pow11_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-26) + z * ((-54) + z * ((-78) + z * ((-67) + z * ((-68) + z * ((-127) + z * ((-94) + z * ((-117) + z * ((-46) + z * ((-132) + z * (4 + z * ((-110) + z * ((-90) + z * ((-21) + z * (2 + z * (26 + z * (25 + z * (41 + z * ((-140) + z * (66 + z * (110 + z * (169 + z * (35 + z * (118 + z * (179 + z * (2 + z * (56 + z * (160 + z * (149 + z * (58 + z * (64 + z * (101 + z * (62 + z * ((-17) + z * (38 + z * ((-11) + z * ((-27) + z * (44 + z * 33))))))))))))))))))))))))))))))))))))))


def pow11_8 {R : Type*} [CommRing R] (z : R) : R := (69 + z * (100 + z * (45 + z * (55 + z * (82 + z * (117 + z * (28 + z * (55 + z * (67 + z * (44 + z * (25 + z * (0 + z * (47 + z * (102 + z * (127 + z * (43 + z * (36 + z * (117 + z * (22 + z * 41)))))))))))))))))))

def pow11_8_q {R : Type*} [CommRing R] (z : R) : R := (47 + z * (111 + z * (102 + z * (12 + z * (12 + z * (49 + z * (97 + z * (75 + z * (107 + z * (97 + z * (30 + z * (98 + z * (26 + z * (35 + z * (7 + z * (111 + z * (96 + z * (6 + z * 65))))))))))))))))))

def pow11_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-5) + z * ((-1) + z * (10 + z * (30 + z * (8 + z * ((-64) + z * ((-114) + z * ((-38) + z * (14 + z * ((-35) + z * ((-25) + z * ((-33) + z * (27 + z * ((-87) + z * (113 + z * (135 + z * (127 + z * ((-18) + z * (146 + z * (94 + z * (158 + z * (150 + z * (202 + z * (99 + z * (221 + z * (281 + z * (234 + z * (143 + z * (202 + z * (259 + z * (174 + z * (163 + z * (194 + z * (85 + z * ((-52) + z * (70 + z * (87 + z * ((-8) + z * 1))))))))))))))))))))))))))))))))))))))


def pow11_16 {R : Type*} [CommRing R] (z : R) : R := (83 + z * (51 + z * (31 + z * (69 + z * (91 + z * (86 + z * (13 + z * (67 + z * (11 + z * (32 + z * (76 + z * (25 + z * (103 + z * (57 + z * (27 + z * (68 + z * (98 + z * (8 + z * (63 + z * 88)))))))))))))))))))

def pow11_16_q {R : Type*} [CommRing R] (z : R) : R := (125 + z * (16 + z * (104 + z * (118 + z * (43 + z * (99 + z * (76 + z * (91 + z * (122 + z * (98 + z * (104 + z * (29 + z * (26 + z * (85 + z * (69 + z * (54 + z * (54 + z * (112 + z * 109))))))))))))))))))

def pow11_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-12) + z * (54 + z * (17 + z * (14 + z * (5 + z * (39 + z * (109 + z * ((-90) + z * ((-42) + z * (5 + z * ((-119) + z * ((-260) + z * ((-187) + z * ((-162) + z * ((-76) + z * ((-122) + z * ((-183) + z * ((-20) + z * ((-71) + z * ((-134) + z * ((-130) + z * ((-166) + z * ((-88) + z * ((-165) + z * ((-163) + z * ((-256) + z * ((-175) + z * ((-29) + z * ((-81) + z * ((-116) + z * (23 + z * (116 + z * (26 + z * ((-26) + z * ((-22) + z * ((-57) + z * ((-29) + z * ((-42) + z * 12))))))))))))))))))))))))))))))))))))))


def pow11_32 {R : Type*} [CommRing R] (z : R) : R := (66 + z * (83 + z * (34 + z * (122 + z * (113 + z * (7 + z * (61 + z * (44 + z * (112 + z * (59 + z * (103 + z * (125 + z * (66 + z * (31 + z * (10 + z * (117 + z * (30 + z * (79 + z * (58 + z * 114)))))))))))))))))))

def pow11_32_q {R : Type*} [CommRing R] (z : R) : R := (50 + z * (8 + z * (12 + z * (41 + z * (9 + z * (108 + z * (65 + z * (50 + z * (56 + z * (93 + z * (42 + z * (78 + z * (30 + z * (15 + z * (39 + z * (55 + z * (98 + z * (11 + z * 15))))))))))))))))))

def pow11_32_mul_t {R : Type*} [CommRing R] (z : R) : R := (33 + z * (43 + z * (27 + z * (78 + z * (123 + z * (98 + z * (73 + z * (75 + z * (52 + z * (22 + z * (15 + z * ((-45) + z * (50 + z * ((-17) + z * (11 + z * (101 + z * (28 + z * (55 + z * ((-34) + z * (169 + z * (77 + z * ((-22) + z * (72 + z * (78 + z * ((-35) + z * (30 + z * (63 + z * ((-77) + z * (109 + z * (82 + z * (94 + z * (188 + z * (70 + z * (21 + z * (100 + z * (79 + z * (28 + z * (77 + z * 59))))))))))))))))))))))))))))))))))))))


def pow11_64 {R : Type*} [CommRing R] (z : R) : R := (17 + z * (125 + z * (130 + z * (60 + z * (128 + z * (105 + z * (73 + z * (51 + z * (84 + z * (4 + z * (104 + z * (72 + z * (40 + z * (116 + z * (35 + z * (61 + z * (53 + z * (46 + z * (66 + z * 105)))))))))))))))))))

def pow11_64_q {R : Type*} [CommRing R] (z : R) : R := (37 + z * (98 + z * (130 + z * (25 + z * (122 + z * (41 + z * (63 + z * (90 + z * (98 + z * (77 + z * (7 + z * (83 + z * (100 + z * (106 + z * (59 + z * (17 + z * (45 + z * (45 + z * 27))))))))))))))))))

def pow11_64_mul_t {R : Type*} [CommRing R] (z : R) : R := (19 + z * (32 + z * ((-17) + z * (55 + z * (120 + z * (33 + z * ((-17) + z * (89 + z * (32 + z * ((-58) + z * (100 + z * (201 + z * (144 + z * ((-40) + z * (128 + z * (108 + z * (52 + z * ((-39) + z * (192 + z * (289 + z * (96 + z * (212 + z * (251 + z * (240 + z * ((-67) + z * (126 + z * (222 + z * (273 + z * (176 + z * (156 + z * (206 + z * (45 + z * (80 + z * (65 + z * (214 + z * (69 + z * (128 + z * (87 + z * 99))))))))))))))))))))))))))))))))))))))


def pow11_65 {R : Type*} [CommRing R] (z : R) : R := (35 + z * (42 + z * (81 + z * (123 + z * (74 + z * (7 + z * (119 + z * (79 + z * (87 + z * (40 + z * (55 + z * (96 + z * (115 + z * (66 + z * (109 + z * (28 + z * (3 + z * (72 + z * (13 + z * 12)))))))))))))))))))

def pow11_65_q {R : Type*} [CommRing R] (z : R) : R := (75 + z * (27 + z * (105 + z * (35 + z * (36 + z * (65 + z * (32 + z * (84 + z * (33 + z * (90 + z * (106 + z * (54 + z * (77 + z * (54 + z * (30 + z * (88 + z * (81 + z * (104 + z * 105))))))))))))))))))

def pow11_65_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-25) + z * ((-8) + z * ((-35) + z * (64 + z * (83 + z * (13 + z * (103 + z * (45 + z * (95 + z * ((-2) + z * (94 + z * (119 + z * (95 + z * (169 + z * (196 + z * (214 + z * (157 + z * (200 + z * (87 + z * (246 + z * (219 + z * (133 + z * (155 + z * (144 + z * (59 + z * (102 + z * (54 + z * (13 + z * (171 + z * (21 + z * (80 + z * (138 + z * (87 + z * (1 + z * (10 + z * (4 + z * (56 + z * (47 + z * 0))))))))))))))))))))))))))))))))))))))


def pow11_130 {R : Type*} [CommRing R] (z : R) : R := (21 + z * (42 + z * (14 + z * (87 + z * (128 + z * (116 + z * (35 + z * (36 + z * (45 + z * (78 + z * (49 + z * (112 + z * (109 + z * (11 + z * (111 + z * (110 + z * (110 + z * (117 + z * (55 + z * 106)))))))))))))))))))

def pow11_130_q {R : Type*} [CommRing R] (z : R) : R := (66 + z * (85 + z * (60 + z * (35 + z * (68 + z * (94 + z * (108 + z * (38 + z * (34 + z * (71 + z * (121 + z * (45 + z * (86 + z * (126 + z * (12 + z * (4 + z * (93 + z * (109 + z * 13))))))))))))))))))

def pow11_130_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-16) + z * ((-34) + z * ((-29) + z * (29 + z * (49 + z * (11 + z * (53 + z * (47 + z * (39 + z * (94 + z * (101 + z * (26 + z * (64 + z * (29 + z * (193 + z * (215 + z * (159 + z * (3 + z * (18 + z * (84 + z * (163 + z * ((-84) + z * ((-69) + z * (58 + z * ((-64) + z * ((-6) + z * (33 + z * ((-19) + z * ((-113) + z * ((-132) + z * ((-72) + z * (8 + z * ((-99) + z * ((-90) + z * ((-48) + z * ((-86) + z * ((-47) + z * ((-5) + z * 1))))))))))))))))))))))))))))))))))))))


def pow11_131 {R : Type*} [CommRing R] (z : R) : R := (104 + z * (44 + z * (41 + z * (40 + z * (103 + z * (20 + z * (46 + z * (45 + z * (62 + z * (28 + z * (70 + z * (16 + z * (104 + z * (109 + z * (66 + z * (65 + z * (29 + z * (49 + z * (116 + z * 122)))))))))))))))))))

def pow11_131_q {R : Type*} [CommRing R] (z : R) : R := (21 + z * (18 + z * (117 + z * (11 + z * (42 + z * (35 + z * (92 + z * (3 + z * (89 + z * (28 + z * (17 + z * (42 + z * (128 + z * (66 + z * (62 + z * (98 + z * (120 + z * (21 + z * 106))))))))))))))))))

def pow11_131_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-4) + z * ((-4) + z * ((-37) + z * (9 + z * ((-25) + z * (52 + z * (45 + z * (35 + z * (33 + z * ((-5) + z * (31 + z * (75 + z * (110 + z * (55 + z * (228 + z * (105 + z * (189 + z * (146 + z * (247 + z * (205 + z * (140 + z * (394 + z * (349 + z * (117 + z * (255 + z * (161 + z * (302 + z * (261 + z * (279 + z * (317 + z * (182 + z * (108 + z * (251 + z * (128 + z * (133 + z * (80 + z * (88 + z * (48 + z * 0))))))))))))))))))))))))))))))))))))))


def pow12_2 {R : Type*} [CommRing R] (z : R) : R := (120 + z * (101 + z * (111 + z * (87 + z * (32 + z * (15 + z * (72 + z * (0 + z * (1 + z * (97 + z * (0 + z * (50 + z * (40 + z * (25 + z * (24 + z * (70 + z * (126 + z * (70 + z * (7 + z * 53)))))))))))))))))))

def pow12_2_q {R : Type*} [CommRing R] (z : R) : R := (41 + z * (1 + z * (96 + z * (95 + z * (130 + z * (36 + z * (34 + z * (87 + z * (50 + z * (54 + z * (118 + z * (51 + z * (25 + z * (118 + z * (78 + z * (91 + z * (115 + z * (33 + z * 81))))))))))))))))))

def pow12_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (66 + z * (54 + z * (22 + z * (12 + z * (50 + z * ((-34) + z * (3 + z * ((-65) + z * ((-9) + z * ((-117) + z * ((-14) + z * ((-180) + z * ((-32) + z * ((-5) + z * ((-28) + z * ((-225) + z * ((-44) + z * ((-46) + z * ((-74) + z * (64 + z * ((-101) + z * ((-140) + z * (1 + z * ((-30) + z * ((-39) + z * (48 + z * ((-14) + z * (52 + z * (54 + z * ((-7) + z * (120 + z * (228 + z * (157 + z * (91 + z * (27 + z * (37 + z * (140 + z * (175 + z * 113))))))))))))))))))))))))))))))))))))))


def pow12_4 {R : Type*} [CommRing R] (z : R) : R := (61 + z * (70 + z * (51 + z * (89 + z * (36 + z * (83 + z * (22 + z * (54 + z * (84 + z * (26 + z * (73 + z * (1 + z * (129 + z * (81 + z * (84 + z * (28 + z * (124 + z * (20 + z * (97 + z * 125)))))))))))))))))))

def pow12_4_q {R : Type*} [CommRing R] (z : R) : R := (106 + z * (127 + z * (17 + z * (92 + z * (93 + z * (19 + z * (37 + z * (43 + z * (109 + z * (63 + z * (123 + z * (83 + z * (44 + z * (103 + z * (61 + z * (37 + z * (88 + z * (58 + z * 58))))))))))))))))))

def pow12_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (69 + z * (98 + z * (177 + z * (208 + z * (130 + z * ((-26) + z * (63 + z * (0 + z * ((-207) + z * ((-51) + z * ((-109) + z * ((-145) + z * ((-199) + z * ((-252) + z * ((-224) + z * ((-153) + z * ((-127) + z * ((-24) + z * ((-45) + z * ((-175) + z * ((-220) + z * ((-285) + z * ((-241) + z * ((-291) + z * ((-273) + z * ((-143) + z * ((-237) + z * ((-212) + z * ((-78) + z * ((-222) + z * ((-73) + z * (17 + z * (48 + z * (26 + z * ((-11) + z * (17 + z * (1 + z * ((-24) + z * 21))))))))))))))))))))))))))))))))))))))


def pow12_16 {R : Type*} [CommRing R] (z : R) : R := (107 + z * (74 + z * (65 + z * (108 + z * (47 + z * (106 + z * (69 + z * (73 + z * (87 + z * (103 + z * (20 + z * (11 + z * (23 + z * (39 + z * (73 + z * (96 + z * (102 + z * (121 + z * (14 + z * 64)))))))))))))))))))

def pow12_16_q {R : Type*} [CommRing R] (z : R) : R := (21 + z * (105 + z * (3 + z * (88 + z * (99 + z * (23 + z * (20 + z * (4 + z * (87 + z * (117 + z * (47 + z * (76 + z * (63 + z * (116 + z * (46 + z * (12 + z * (104 + z * (119 + z * 105))))))))))))))))))

def pow12_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (4 + z * ((-15) + z * ((-25) + z * ((-52) + z * ((-20) + z * ((-77) + z * ((-78) + z * ((-14) + z * ((-143) + z * ((-107) + z * ((-39) + z * ((-72) + z * ((-114) + z * ((-126) + z * ((-89) + z * ((-13) + z * ((-124) + z * ((-225) + z * ((-112) + z * ((-96) + z * ((-124) + z * ((-140) + z * ((-109) + z * ((-18) + z * ((-70) + z * ((-130) + z * ((-21) + z * ((-18) + z * ((-35) + z * ((-129) + z * ((-2) + z * ((-50) + z * ((-25) + z * ((-65) + z * ((-26) + z * ((-86) + z * ((-41) + z * ((-19) + z * 24))))))))))))))))))))))))))))))))))))))


def pow12_32 {R : Type*} [CommRing R] (z : R) : R := (22 + z * (33 + z * (27 + z * (63 + z * (89 + z * (122 + z * (55 + z * (39 + z * (76 + z * (10 + z * (37 + z * (56 + z * (110 + z * (79 + z * (105 + z * (3 + z * (56 + z * (52 + z * (76 + z * 1)))))))))))))))))))

def pow12_32_q {R : Type*} [CommRing R] (z : R) : R := (53 + z * (130 + z * (74 + z * (21 + z * (113 + z * (113 + z * (19 + z * (41 + z * (15 + z * (127 + z * (92 + z * (13 + z * (69 + z * (29 + z * (48 + z * (100 + z * (123 + z * (6 + z * 35))))))))))))))))))

def pow12_32_mul_t {R : Type*} [CommRing R] (z : R) : R := (67 + z * (52 + z * (47 + z * (142 + z * (92 + z * (109 + z * (107 + z * (176 + z * (244 + z * (131 + z * (157 + z * (136 + z * ((-1) + z * ((-43) + z * (48 + z * (150 + z * (118 + z * (143 + z * (153 + z * (258 + z * (67 + z * (72 + z * (280 + z * (95 + z * (217 + z * (126 + z * (40 + z * ((-108) + z * ((-56) + z * (8 + z * (130 + z * (128 + z * (152 + z * (151 + z * (96 + z * (47 + z * (100 + z * ((-4) + z * 31))))))))))))))))))))))))))))))))))))))


def pow12_130 {R : Type*} [CommRing R] (z : R) : R := (88 + z * (23 + z * (73 + z * (10 + z * (28 + z * (71 + z * (8 + z * (15 + z * (75 + z * (66 + z * (83 + z * (122 + z * (75 + z * (129 + z * (120 + z * (82 + z * (51 + z * (74 + z * (77 + z * 40)))))))))))))))))))

def pow12_130_q {R : Type*} [CommRing R] (z : R) : R := (15 + z * (101 + z * (65 + z * (98 + z * (35 + z * (64 + z * (31 + z * (26 + z * (40 + z * (92 + z * (42 + z * (106 + z * (19 + z * (13 + z * (41 + z * (23 + z * (38 + z * (92 + z * 89))))))))))))))))))

def pow12_130_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-2) + z * ((-6) + z * (14 + z * ((-98) + z * ((-25) + z * ((-12) + z * (43 + z * ((-41) + z * ((-58) + z * ((-69) + z * ((-56) + z * ((-101) + z * ((-45) + z * ((-230) + z * ((-78) + z * ((-31) + z * ((-76) + z * (25 + z * (8 + z * (94 + z * ((-77) + z * ((-108) + z * ((-81) + z * (112 + z * (169 + z * (27 + z * ((-88) + z * (46 + z * ((-101) + z * (83 + z * (69 + z * (149 + z * (247 + z * ((-5) + z * (19 + z * (10 + z * (52 + z * (96 + z * 40))))))))))))))))))))))))))))))))))))))


def pow12_131 {R : Type*} [CommRing R] (z : R) : R := (87 + z * (57 + z * (55 + z * (73 + z * (5 + z * (71 + z * (56 + z * (76 + z * (10 + z * (77 + z * (114 + z * (21 + z * (33 + z * (61 + z * (48 + z * (71 + z * (34 + z * (111 + z * (63 + z * 80)))))))))))))))))))

def pow12_131_q {R : Type*} [CommRing R] (z : R) : R := (11 + z * (9 + z * (11 + z * (104 + z * (1 + z * (130 + z * (63 + z * (128 + z * (51 + z * (64 + z * (1 + z * (47 + z * (125 + z * (17 + z * (109 + z * (18 + z * (124 + z * (66 + z * 33))))))))))))))))))

def pow12_131_mul_t {R : Type*} [CommRing R] (z : R) : R := (65 + z * (40 + z * (80 + z * (16 + z * (74 + z * (5 + z * (30 + z * ((-105) + z * ((-36) + z * ((-4) + z * ((-55) + z * ((-21) + z * (16 + z * (83 + z * (13 + z * (150 + z * ((-116) + z * (74 + z * (81 + z * (33 + z * (30 + z * (40 + z * (43 + z * (77 + z * (42 + z * (19 + z * (230 + z * (204 + z * (192 + z * (218 + z * (219 + z * (224 + z * (210 + z * (116 + z * (74 + z * (46 + z * (103 + z * (90 + z * 37))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod131Result
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131
def g17 {R : Type*} [CommRing R] (z : R) : R := (25 + z * (104 + z * (95 + z * (82 + z * (11 + z * (75 + z * (106 + z * (48 + z * (52 + z * (8 + z * (79 + z * (49 + z * (111 + z * (2 + z * (54 + z * (63 + z * (80 + z * (41 + z * 1))))))))))))))))))

def a17 {R : Type*} [CommRing R] (_ : R) : R := 106

def b17 {R : Type*} [CommRing R] (z : R) : R := (47 + z * 125)

def bezout17_t {R : Type*} [CommRing R] (z : R) : R := (60 + z * (136 + z * (219 + z * (143 + z * (106 + z * (184 + z * (43 + z * (151 + z * (146 + z * (172 + z * (84 + z * (227 + z * (155 + z * (208 + z * (114 + z * (153 + z * (201 + z * (173 + z * (156 + z * (176 + z * 101))))))))))))))))))))


def div17_f {R : Type*} [CommRing R] (z : R) : R := (2 + z * (25 + z * 1))

def factor17_f_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * ((-6) + z * ((-21) + z * ((-20) + z * ((-16) + z * ((-3) + z * ((-16) + z * ((-21) + z * ((-10) + z * ((-10) + z * ((-3) + z * ((-15) + z * ((-11) + z * ((-21) + z * ((-2) + z * ((-11) + z * ((-13) + z * ((-16) + z * ((-8) + z * (0 + z * 0))))))))))))))))))))


def div17_u17 {R : Type*} [CommRing R] (z : R) : R := (107 + z * 105)

def factor17_u17_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * ((-104) + z * ((-160) + z * ((-143) + z * ((-74) + z * ((-70) + z * ((-146) + z * ((-124) + z * ((-80) + z * ((-48) + z * ((-70) + z * ((-103) + z * ((-129) + z * ((-90) + z * ((-45) + z * ((-94) + z * ((-115) + z * ((-97) + z * ((-33) + z * 0)))))))))))))))))))


def df {R : Type*} [CommRing R] (z : R) : R := (47 + z * (128 + z * (69 + z * (22 + z * (46 + z * (12 + z * (97 + z * (14 + z * (93 + z * (39 + z * (97 + z * (103 + z * (84 + z * (98 + z * (31 + z * (66 + z * (47 + z * (14 + z * (75 + z * 20)))))))))))))))))))

def da {R : Type*} [CommRing R] (z : R) : R := (87 + z * (35 + z * (111 + z * (110 + z * (33 + z * (84 + z * (107 + z * (66 + z * (16 + z * (96 + z * (53 + z * (63 + z * (25 + z * (84 + z * (129 + z * (21 + z * (82 + z * (94 + z * 23))))))))))))))))))

def db {R : Type*} [CommRing R] (z : R) : R := (97 + z * (91 + z * (127 + z * (46 + z * (9 + z * (0 + z * (82 + z * (112 + z * (45 + z * (17 + z * (60 + z * (42 + z * (103 + z * (71 + z * (9 + z * (129 + z * (93 + z * (119 + z * (76 + z * 84)))))))))))))))))))

end DimensionTen.Mod131

section
noncomputable section
open Polynomial
namespace DimensionTen.Mod131

def derivative_extra {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (2 + z * (4 + z * (0 + z * (3 + z * (6 + z * (3 + z * (1 + z * (9 + z * (7 + z * (7 + z * (0 + z * (4 + z * (10 + z * (6 + z * (8 + z * (9 + z * 0)))))))))))))))))))

end DimensionTen.Mod131

end
end

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_PolynomialData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

def W5 : Fin 20 → ℤ :=
  ![374768125339302934395297745598342118218862210017378667118202271235324437879790150715165992367080262643984611333532113239749688439779454988341175038140295500800000, 32522631167647811010316523515410346647024865628819714569652765125723001315563269027652918341635274158102157963737974129677542427974414495729390040497787926400000, 28656134470122455084650254660427118865166672666390763748491531889744739269920396290691489294612234901921779027066681366062291316059836116253636998919218208000000, -2861493494165839373995890498880478534417070731795836071738662660427804453697326388228588155701875648144279124124484684681965595677022506524675105439741521683200000, 31281884539128231327884500902352556840481717496281954608582827656517976849341667282985726337728797237878860373402984262714454615788754907039861567340076926400000, 44227458771559309156279338385790942553728660015830275992171973826048868286572157848671957971969541461029296540607553769971227673401042166423775834879018723200000, 34143285382697251319657743090435707535108678138109066689135761549023531374218938697846469298272354315463183803667661226743826755151075089064885890205116211200000, -159506768097933044222006202434831578186895170726174676657673972374918795242338613470604633586118177256831483695058727273413882958172985426513903022904794107200000, -65980786163087531787444999184624947757314784521111960835304103647989075470160593165736245043124662010850072658572447811245136467789375198522021131230472294400000, 836775880666302003994684370904536209793179240964159813890839666412575033436055250209313555090249631329630628392796629657973440102537321326859502041021814396800000, -22169995293763326574697652723406633116051267233876389277373219987621640576230527611047649351946997416954567506680811746886853647664226054438559749516616416000000, -25796367286700870577710402128607150351780157630780415500787883849217545995334012445800570267049753291627340591208149239074449064107876844607283240701529603200000, 9893955454445228410300805073795013936589806965470799574193686400975480410078987431657191664863277808768840525570480428739009464863960556621918105214349980800000, -2603391937407594041773177355457176637271622894484677127363947015855165109216695664075114028715053765817141004966741662215867504200031618789911315691299849600000, -28235901240644974762039821346781730919063370448677461396979696416940325312817324254178981695241305740796568078789622099049420600076944611848014388844281130400000, -36624328224636972325292155555162901017313101105367700837113908735475730842019470189803672949178713904315546892195081347635044751206470248826107452922432616000000, -96714296610258754887140315456176618734953311785269921840627095073898624483773823016387970709410316114832192796704076335951330740459991873157365285429020009600000, 167643843588872544864429880908877400656620180928177849565779892654333113747317159666903410550586903690150671051274755081559705986440213504377113845569814712000000, 10781808853205357167476262560261593596574965234966552599323825733100427107884008513551158111056529548596023933587630338793104923971540432795149299928497744000000, 48298425672734144885286195058974095567516398018506384139916680220446006170037540751283656011478126670877983237620115124527081054459678987396964463790598627200000]

def W6 : Fin 20 → ℤ :=
  ![1224845852938646202752855767076001134697529245736956802676439649328718204692222346574395781745284356986561033024019833309188063903509981314067014572872629075871601724065006454829268399636416000000, 22048099129017470242080608747277411491452627247180855080410034994986975157927534543843695179413068912083674599835328481809669064382542119117716795324187706165874932022670154207738990265664000000, 14974088320209612769578561372125072499615533237938889754975547571546037909312451474512590597629268724973171851210874385129115880270990287482095404641101508170424103995389280125152163958976000000, 18016515106050525646469498391650635209528158332856370404738387719060960674167890595712336813684661218594920624922478065535077549508708741455302569276796572439638712524406956025901064964928000000, 23733054071807418060871034326071839445202701072216639185158134490802157031955678130886294487135025312837976894407327184553602703509790257324609747173822357921783234054175595222635141141344000000, 32571313066119807368719626307305217537442081474267217341422862513053743845563841365173273752160812322647355043203367147998870603346947304733407112670456045390582510425996202347178865722912000000, 7615248471888727400148360132185735286704704757033306401520956281305639480222808122659176888635946830314781024585214002434610674009305988596938783047827344644431648077037269505045458042496000000, -74848658363455475037474986682290900830215382144710067773908365255634608973265083281782476165604593396939721495399321648782153480692828553490996639092113354618616569475660134410007398458016000000, -64164813297216283523395907492692186621156769689896257786362748115167612319050778816246990039577818118755743651316302562520060851882621476616005710480745366664433609090730985214148202430464000000, -249581193335844678464779090850235486901464363784094600495886106107916185831952020682304558684554359611348189279648323748664884840164666202951645915452944870374657960283680225979293939679168000000, -1211125675138180912481899994365012121160796367542738869664449347587923188880348514144426090805710004489208531988335943318632504173302782709672416379132939119398782835012255516968524314832000000, -914348955219055776099114232379584032766578862399521137430463563271654014942286225374978671730228699412623099693252448838709283954351577921920740845566018922484461020149966211795825258320000000, -10082487506689152610268995162037153586050706068010806107855881714919312332556151404457907876993217871884863138624346420940562167273760247452319385733989914543204088351126056852769407190304000000, -5610944379739281548879032985346789200919066531780455511547937358841094704474218063685677225785927497932883637867391467311120629028749048491369212092769240706927102043018748233978749803584000000, -20974413353618014181908700891683420958767106887665063541185022015655090729494382719451143675535358736162151151741168540832679594598391826994647644714074252161586146785559138710111537657584000000, -48482081286567089833342568877840802672078185286461839632402724906969452533748407642869837070772936584815635076017793783461217837083972703697072223752512598406794841594710422516047699211904000000, -26414303097640893275755029247754078748476343227929426837607468127356173085613617892433076925398984888865419134203671633465396554773539588581643313811379780842262991258905589417179797937472000000, 53913811772986000898019545772191881364554733934330502883276690730915783194950401900700482570287295039055103518909022741028793558662945209995197554894444505452979985648514748708618937037664000000, 38931709348140564146194658048138954656258439167372345797150263401720598214863369575353475132904038368461109226407864021337012176756720398467385759268762061158104848067676202144578642960000000000, 95879989754065057544189537713019671642234331143844188925901193591782725707843108694229859708178070533352075238313346118645441101520774032562063599176447093930718974919763209992315360184960000000]

def W7 : Fin 20 → ℤ :=
  ![-248873536117568346762903470582672516538204398560802355591650114988145290183862232379920282880815251412348574487002708027510172107940125402596880717568175899492698498644612273239183327874814966964492085077703318424311700480000000, -8175013185097138639632085606549257119961924071931459804724980064336153504403651468167962411170483136763368247722662754282040022265252049882374100645686400761942834718176719827582688758961655395306280564289503023395384320000000, -6430678866991168899563859530380265174302760188143755221898878503576087681977044725786436636918791540541247327553206339091782662163777084545815657044656958874126101464574767350497552560185535707963085576476718600467532800000000, 95497951650181257506028262071766319040786385677528003157581212426575098389214203821707569484854612077437288290377341980047564201203242739867010268827212955851582265029012040145869217635131824252526273584267206660901226240000000, -8355928050555001270490757741110422534474209992531690621010530339101983568301453093349622159983017705306280304189436717138412314847658078424456376529114378038792112863066852175682869110987425066783281698030543474532327680000000, -10235409922249613985948904875578502707107779504371698940500880061592486340024638007409316020825939194199396056073162695753866334815090058581402801559330786231586191387436355852979007082491717979427329980596769048315048960000000, -5326762241082743804070159080039110819889548102738601554836101752942937664730049321545405724287449808459037163438412759292403208901521198768084881082957984139799131371965103269331659450193328528605359646204484701897751040000000, 37044036392595965429904749246732147184220214189521460314610436620623460386655672593864323978574894863099886364514365078883585524240256497204044383561631922708046093252075517583994687682573542377892939223363156224204003840000000, 20570609785592003135199416684011288479086681791849557232525563186479550145685170487511936996080238398709181636889159368999363285224875745779967330139154460171045062895695193723830053760992144316189743187517793238063635200000000, 27551044464300994215835058092925370344302211749753913202822195706278109357742347792617769018366829850154198070103639973396337398367521424411214662715068747503042767661112015284036086894857997528060122532884649182515864320000000, 3014192338158475829353925697248873921417170952152262004330294046134301767102102184185715187101877803230574459263218025513859756501172962284987889850717743061280885327079279734864622689842162690188976253309849749038584960000000, 3194582208874088330012403613591332163348241944864173001737554644105775280847419118729690131801389176543568386686782457819990337659390797183144484023754722911166550101978892012689469479987288948343270998706051005993804160000000, 1710430191998198735895275915795827774366886574881745430984670350941289044652770502094473656090318337039120571589524060990956086866596258956147590085602910290249049143518205048018112759285448430148158361797076351266507520000000, 2475568765309012511542966725355549748469285665898468466992071643400610490017020141490328340856340840199306645415657054668943374287728910327111467853250917432789008204330382695897747298356630191758498080147866167674695680000000, 5841000899121521779353507956634521854380060140937839374280083945148417662663370942023400066407150089193234391692386281810832144238632268333134912479237445316121152480967562746761955812319379285333786254939693044777284480000000, 11036322868102420725730611224173427495954545244460444624730967427842392319471071840113102179590833208000986137982356548756522729752829170155064258321580749150296011380312922730617127448686214691362600630097157005231117440000000, 19697447896933427229812755028842828140546148652261988556274675199587887730197710811763302722922549278028863739236109719479650187535572963094684663194591908703986475656167110076350355601490336026377275566845919800608040960000000, -36780771131879657683349824693407741180206856809585638068899482516995765832370018119458468842031024504582507726007201587360254536047162572789079822836007792487789765717974363508008696477891750517183696842887494905366848640000000, -8419027600789396374332537750541463420189119761390593814140699708700120398232612356410762756709864169713249286296385697425985131193575951515412182154402374527303384894318350330758813046290131798006811070289310675606625280000000, -35373124854286956134906820288086379123931204090061916917433061753707583011582496551056687537548309609463002684479160522735591421465840232429543179779683162684207668393427756529823695120270855287196260356923296458426123520000000]

def W8 : Fin 20 → ℤ :=
  ![23863000557921814908034029498820652405396555238593217628801439654270372192662044945743391880708642497014816546015776834253614606694014459112670395449565585064552927715637123810679254421259953054266775330494837384305545598725576538115623330696784858112000000000, 722759916307911466464816182567126152006962636811374622479212179811011654610122722302949508525051897850193298797446372079609822674446387479205207152411643455156990429989025315826967690787994144127733688821799268003822799857198493802533172137145112678400000000, 722930053547605755207519097463369626041510328223291589220686613152520850045636042455767186296988861697890245732156110452186634281993037933398293735047671556520618066035240454062100393054489745388587620477929909150317491253848630555101653094068022041600000000, -17489101337030307288408319810876359845661180474599552685677131509356603723047105041993882136656789136964406704336955761482538836668949951859326079962111423557187819593874359924911247654069369993203989192409283190319907163363439851260433855085581718092800000000, 658630429052749029408310119763272463272015262997261236487001094063164810255065288559892491030410654275789891378359531784590117474911566852924732117674899623642145710746416186763354081775333268559679261507216545403282639750606074175002434120962436889600000000, 247869926340648770154237416103609038047728261722521802496655692644320274367640743383353972360259265578864401244031653562372903005398301381222109364183332867481514745481113368670122941054831558524178059744229173895136283849429770460945758211273021580800000000, 1015261897991366856976964658538434978856066162248242740005799262223483891047107258667963630469609023683649093257230827145740927843396681744257748357805433159415377841065209871697469829874671311308239835963135861262873047684820368213129410135450241356800000000, -5780872076927759574440872860494696735641714504632309838800453018012697654971642603038871485282556874050355050355923141554389590982522369499852981986172593788448914524039856463204812776602266742151006520012657315975545546063212166806015718530635302284800000000, -852842841407067446882339150559954319425457912215595348878771121136465388062676104608161658740223583593385241491583552419604741998037293108202862308504728292175696151276791968433974373940487503881597580602161316632475943340965038969978448022504101222400000000, 290041554011252383286920849941155518367903540954303652464145236060482318640260957018800719905652181855301463031469647402458024361652046004684497379362549031355803586175642815338743355595251563698425475420085766828465242713186561536133919400418108953600000000, -785766109188030213055456191798584364150296646038010326185821601667574158439193619504308855974249529318486139696098169244311665989016333511720778572694040299692407690089849367150870454815033612678717885663582993654121401203324900811481986066816714886400000000, -651447244777590307577414919866920756937360890112596790998896642270940447283606933124756355050132116801039645849314286840803569770674895781448713897391330260084317844120495940238709489439811301824020208551371569846262967774633408409565830156547400761600000000, 451580909019363576925432329729916474817412389922351202708292738173809162659578359440014609354155734243804276325097180289951067923487205939434026352244130234801893630705108101796735714429387753070466483084311396041178969582575742650589584532807702323200000000, -380741522827850354628240179332280874786229653138909895014247251637846753105630482562415850809463169188717854184723152057079947503202641135275504775295641876941686395541012106613242962574804869271419702840315326635442402526486709189137221533359189990400000000, 211308388056074901794895094805353017781961986463077098462028805670635684923746269172076307082792639529445906595805904520635645231844775029017763535762746029938423892727638468873206924024676587803372201251088632582606142265866933670166996495095535097600000000, 1054829014809778699526648103684904237605266388117346119809487372396810158300125487170123554494228402849453003167867200880336697350726877936998776773849561733298159380121506682314734088587644634511417506342437665216750785932374837425084549535536306380800000000, -4456016534535719338389087431381570534374577719498405234048031565255972853778685400320248927901270904237162297953680278761411417655875400331711667947597957245516002077302293395635549428437781364348947067295619791979437438563803924127696783933609483392000000000, 7609450674735384935876486881425444951084163358529120572072547074585147578045281931324283373179961328799794647625422167617579071787166636085051059999256217888603218412203581195062972196685184326962540778917790812736915191900916680673086024597553415910400000000, -1227789230036011711560616459932075527276164970526980879316326181095553908645942052891990227977301805107761417380542174067614115533184085862762446715315237167836958253877554940198082316758089872758370454419269358877850947320887746422048968579401105408000000000, 4911827659125655634703864903711081471100117215370278409645263290560593615163422792423092688147509054098568900875274322866191400901414411006279177938693892812957658780595882322849915176673265792863738094340430918149007129855413125908850722568600019660800000000]

def W9 : Fin 20 → ℤ :=
  ![-1120994509079545231919078596782490471030777820462732373793608866251803421643587346041377196361839192609786450818465618125688068078423670876022915471752833528343578423992860302806392398277379642479912521921325889813360797149311488259732273315723695194555488840718363602778386094813184000000000, 66310634039202525730507999649531789757441727663654282583723513882416780526213266759686860463979295808878513051021590298437639200088915114646115986597127690812641234719272960027590676822412291272152598687356329122819162645188811586207271214387023485378262041089079438387858982399488000000000, 26564434053726796774852108229522959448899711670759667668005204823694639855753052616873752118878533620512834280045181232607765493909426106345677811928073908061782433526495657125295688186356448602474407950221942447402024318037532372069375219301084495126690997601822261820298725865472000000000, 1399270384989749185984769137851034976278240222278756559142193583204099997015993960731327457732920359523239345134585334011212797239879484103109810514947763251790048397344874354198984839085574636443709497117235396488271073857559010786422302054080844812183464900493868235071328889317888000000000, 88337528688307154419710070500422528375079106454522827250586669295068186110378531207969082104814248040250142910816887645172232352580608817022148786028863428268604128492624925346426607392190882939473186541001135954383656063387269435542139337409258619254378216949408188595937717122816000000000, 272577696295150103503510494297875362006896939593891287630157387745722010128024689581666172845270470359013196681432636535988098939746963079815859421350237633458892158357653272532330564429197394032884724677304664319461787745145350396658229699251011546210251789217616161016529841015296000000000, -90967321746633404739663504268255239137529783951557012566650584093480550103814856292123669405801923850919447216826913877359556755395882104500854796453399676751142289681943179573582620130383657515292023792794212436623884156471933074684415305068606708941495510871063785155902549082112000000000, 328325068229886930688669515356284410617948992478205904698539736006286045931933527418658425775645328534046644865515727437117721220967987990800087155289399181310162919608052249562861644170904442123826929689911260000634245086807041455960038426357792634895551063138977986269170054988032000000000, -457275810568070182504563688979839287322943408429184256044531094266271702323269423353150730547871592762627302134250504391654619476373962651167476864654490791621298642194401363500415388773341454001470536653976599981371261301086560354063669787805592351303666626562008738026135137322496000000000, -401584721632611090951670492087541028828310796919255662215370548809458913919573942648882906003811617996489417930352104663541904872574751210040169121790211915387843370293993228097738810409499735680571730339829542168253325298333951758968633720331384112003027342373879672856574470813696000000000, 91808185763863562336431358734466940329263481823787111031648283071327659560795146266823191325253043141969708853476410659047542013732831480850306374043731088211876657683888834357019011930606031748405233829604756535511391152115646685863110987578308109621933028960717893597026257316096000000000, 17196129657948698809095191316586336054297348550133290021554328381179132755988685244587287037404021573478208519169117244656349952674261524179681607932135767540022109042837720699343375498243262572465142489691778348971648392918927261180225870693203346404406776301763802790922985123328000000000, -214768152434685238117528269251957994818940004030729248179808936601534861354249420655472940379109073102060088222595370520130200715214043098300155281943641370490264964121283026705624647974869756466586927655575330413254791144966927746295787053758665966911961638367858167137292103674880000000000, 8997976135505602486536240581922604558759755084291696828242998399209500185939518046869922028519509534324122389208896157272913612141147684459510782065421953015444795265182769932574818117566574945191436543815712705766320680169467914181458648716110618407361890052044755253323374445056000000000, -254752845963550591403291200718276605654017229650139249503585870402293560644133744879794850974917654090859164718041555247491582369702706667297072637081233951058006863500271000515484323456980608192684150173379261163649159470025664159483206004971177649081285657907515152031351518922368000000000, -645401637600947456508089274584384411593161036570483442949368586204161024805349324222484902730353113134784578271998548281827721547468187020318470480384727241611329139509964468877250700915225750985448252488678956797066245412339702819751302663703563487866194652109201841008684205065984000000000, 537208180767933292951943424107310298743122076682465925170870504764081187536190037875455269269711508235770270674358567835916760356340104208074549327523042460181822865160737701317788432408183280844393396624079549427583186776690115003830316940904519647353358168239833109178445364325376000000000, -769770202311923300481460148185973268068071458967069900966554406604479302993745995519843251059221176013004659301927598300660870981678031704984343720487353881773620099454234130006478514270111805856387543442824484156629046794808023790575726088898267483119686766640171053407392275785984000000000, 657476368057240032519942372797226307106004359287601157195819773031476871433860595413051963761096028766777747589146889884669649427946115380740466129964875107660760308203095129146561022873461282779331854688601665693821198559737177695311276954944625627112972340959880383452183482601984000000000, -204932351058618164102454158846129158902662213642664021979875887881921802641440526817192276625438757875563820001041986264959432131022582763105168487482783547819821851075322546025251934754603359290635754452366176355860972571585563450744709087421891529155109674506205527521915944948736000000000]

def W14 : Fin 20 → ℤ :=
  ![-69890226737767372760913093256949576547265116507399603920891898757635648249683481626181746940897792128268802724094049031726091970116605919785517782508609723235935004993267810335792493633744783330756497390286402578319621875115327769655841762245712368320402738535193158092044432860316197557878307781857164957286297294086265076130323038539007932472184632347101302953571917010822694176357881655171378538614279590038074137079349824040910848000000000000000, -18896801537397941273553194178949876196048372471118190823070862490746461227939452872058647098371229659309881866416636601709166554638132260310310900295094784308405786423922565378158184418318873243228259845858844823586010943539738729124358737324775551863872897048472181792394699532722809440206383657300415665000754085335564704371654264159646318629844028903564020210798962016206004189796651705223752411059897790732360264345225691613652582400000000000000, -57935174322754289029047069252635758955291641558342389321916494358315539727885235417238235400264547813496734530412091169455710163552791037197090515103232785753715860776377913571264542588545657751023999275427251487541348331180992844509071652313996534828365097780763944755510097813965610377421681765746189379915785542192426111383599182406814688365560774308786798516075300581458302894897939699990286834498851938524707178961292476206127513600000000000000, 126120511472804647299152604229528890041863414499342705135904927247639966951799461667649399759506591376787538741479745151818090163065552880731428012764192029857694909004395810317200678090573888816010761643961539035918153179017950012441094916440932008765758998110733758685091575597827219069751329647794914832620657156813417237509364152245819798793976254709850827423835222012595264975188715724330812713646529807791012335261281040151402905600000000000000, -73689223893316713835361363069255574489704720008704824383431946322616072283735240420710511700207301223559739807537625575729807887045279204691399629269797685593423057196889520752187384873850193925404647825682593219419702702936099875955616196452741115307108258350317186174759461178341955459019534279932291992231956459510819241730857901340209164843836612750568129658308068159704666324791968302969489658778852769989996752188779233294573568000000000000000, -146343024035755822191938847250642657959109881709477327032446845444435544078036774650916279635349158569190969776925751558372076133773211976772838420422674416012297333245339175773289646128408064212626554106254204044001051352479354637293362943142614891973879761869656431374793459559149347634652773279654672786054726419291904864426692308332830238321825379123810269184914857068454876387642659570381663754725279184192190998099546277686743859200000000000000, -37316160921228043725714565311400798454507117820511826124138351827505771376013335873482774386189453312364094793438199978167353344516584564848137586802439060786032140968023653148494017607004879937407596162390324783047533052114051659339660745591460279515973172382117258789861537118466293012373606318176731937603950913241132833964786436910411516670547213274070453075382653256111587628777220746111212454047867472349918667696644521256550400000000000000000, 31640558952509871497801289492162140772052333212330749397451632732640041664180544443646067516212720877625481243620905868588513358966645652232296245380855728491640425388554124885533263506016226643123719728241005946240864952344323474398281973230855443509258904926784841006368111605375488710140502387701010622087291775449416733335818692847403637671887643465788435062357702972474724665094608933706614223591631843595682122585250382846186291200000000000000, 141843518939991304584169089212639455350820527970558952263543836885775313119552970619698848348601314514926283900042825045647621186153148691486003058700352343873904362045974421302775455315474125088073156704451361011015718117083402714979176776734201708307260586637422223124755247592864354047237469654224569618934105192442770813664213678677826791012316865038341046856111921478140550373592513333792908426406472558754511254580896282001627545600000000000000, 9437088850185915513505703331248673736554681448007930385267325014521096244715812625559191905536033095041174286277509504148899080101395616971925263310260303166511653724242316842603691485504606527962336920051189336373761902966882787254242648412335213150785836710379985252063090246866468316992328172058298928644409605723190234138492921191568840381085015504897489755883845354410103090856126172502589574254825366590272117156275085687488512000000000000000, 22255177298260087681549923920259361033005449363488247879492930065126054094898802033043749747208087736371521184157019726535434700982170330546346371555720187433085434175751448536474643045724278856017449535803768141672930446868323148450977051629617401673381880740169217003462734923158443207606215958469767753449330037531546688293817992178550612865858237852003782005017501751188961766134575839108599961834545818473290140559115320079729868800000000000000, 86647349433776202643872758871817365631521504189723065983390910414628909913344297383472730219548095887341259814547115838908531012855981567055069910228877460726203155926996467608515005032345617055996018792527001606842403565815877864847963108469393434388916066853491966906690533819463754866718497994464920828654699157091877511080442999392073141497279381241451347587946716422751586950640497430042575294320069479427955656237362532603144601600000000000000, 126046257961091830694105928733636126206612548752957492536115706973254239414625031109573858304292157154292516133079787157920983960011589820794901665063491881822560793714059280769536444203994228320358909823151231545542481639242076068693118756483794679134797895983131946945615631349989572802055331863951408788649288969676968182891252233485624638018932596904475180478562453568623293483885978499721086211410769556278394016002412323141101158400000000000000, 47440763783498537227243427719864252836177195565462940522582184112036263771275799246021989859215349553145049742664260722269704303031877121387089015128046169206027683509530434891218266918988516634336716570226098868639462442006207332380395592667620111915520146707172043764863511837703436319548048397633334450212448006335815525580878260991640722634273060935810634032834693254575894747995839096946073992215930475101649880041608052798917836800000000000000, 128220566028065662373886450803067314572470723450688178920804851440642354044547608960172305526358092618818496651282370506817729467689877798196870092093726371335770169743281235648733926191133382690676864043359238712666697288150226973907614440968599167628881943700634380008618188611848065894779517951891397295906631570973607422512852339358055641448356430542679635249086784589887104560447521383319096342969610260087104525706429683684885299200000000000000, 301664062199196509721078473686538934465702782677662009976617576585672042752986272089159629599634304935576866742169274293809874806851033350096947599419517788865408665516209400129021541465302479935960549333922328130959108753538227027277574297747708321593108731764531695160184608584541687303452228707182312143029090263445264954746964846253328758230711830290919801911679637037051490252157475000551307772480260867357941106597297348091699200000000000000000, 106875352334504867252197572466796317205245049085778782494836199741921598443180396969380977223503542968601366714364075633255673730555892695177575506005282682445934935469002807722146278218750514331299679976439028134061846705773138064501784414976634539710857353828691665866410642327955530785585956571593721478506629364042864451943252823844926506605554518147615908646185463148145044689355761318236618336956139836855403071566426713517352550400000000000000, 8954845458246542731428582712710666433416109430873356747670264081148182962761271145945596834703226534624566404804369687869294731746619293562568685963365817521867794030090658106921708574074315698467528051665296583181821486076003359570436400373953869934173409356261604038016608039947290273817420126229900534888340704210849252994770441719602022373877388703178779490727607865268827300336120693698429393334897612358869172542190879137713356800000000000000, -75821959076291297102776780402768313908600150131512579283347070458680072237394912114406682716770496607931650594641550109146475228116434273711296092621960187127748483234857362839590109030646129321905650990666419584271963182309120991594227244278476677178012668165496590507538765282869317845347351017975101087995065703260309438441128497873111494618420828871347898221340192414251656592220434902878747067077765119348462481251117283405601177600000000000000, -88680012701966054835643290276592919195279431767262503998248555426314067087297925560007246938707385136812455343106458750666888024866148555298543924780756950050154534240683131715923617561262972625332583808858716568192774650581006152751084586473057762517859378582988117741482096657367477029928357142901940554033121971472762428239247144173279657394709137043945779118038196069049404485323064072805941497119020928869566719484578456453323161600000000000000]

def W15 : Fin 20 → ℤ :=
  ![315326608210896254498255207259361210983234841109478795710464299224138036157264036954184001988295070223931923845367833282460035930056211442714966099199797955369500285919051423095252957543560867725235481426291480163680860719429057067481386671557185870794725290083931756047647741115495895818986699845345921202671566855773976033232151397023387720749344936071481588674646655637032460867104569925971910204408613717465338273324658739148315985397791796500133572465335205888000000000000000, -52405017820084147308869633993321196493890878658431502479688798504544596459677329324498699458625789488112282511151604915389974731820554432421258234095981843291003195869462304421354270288127023852682420505072802105376980479385986976568308315271663969982979229060284972615908782029571318217340651967548516936148388258141191393049694407217682003124181363980780960837788020121607465354052585269713321396180995066982090508636570448779964642625315787982962168868128751616000000000000000, 439907227704479840658697322953528307465782720213187695728252199051570867543629957967387286950288828929205412084628721552070211261048835810399267667707674699363530988320942312511326853131277121756170148744778661218413464023205832713088969298766405961627467561121621855831689826507669154637771988346927708759202451934390667373512814719006276770041770523544618245823553107842421986886067538881952659637268932537854314778079035186342197244270660701059554596568669880320000000000000000, -645790817961931545863673326604927231572466263861165019464282234603720628398569761867389278178927662425931545737212555003937623090568516417961597995684460488469155350910628970334412308999967191612216863569569524150063057979831245894690277383641010959964340335212377055928324103538728109844880352535345528019919753957389940620607698818301606155490949265590470972086049897633173513087552140300944504090222658658364167939530268010925989695283864961539567996812159746048000000000000000, 1004517290842079486988473254085985128808377324890631721477404901048710753227487201730233864624115409842506568573419015597395839856189280330196396393032671021369978877800186722747160683517312962373947879928293749256137183134392630369225449679933905506613984945068380674997833016406383194862027496259084178079986960663886707768352470857748555040952640990709910352927363517583696691138715424146745822760114455449813620682115509440751340346745504838640405568104351498240000000000000000, 1429534243924231780719217050656311366692177825204490638154718095715803542127219205420773525353141986416426752453136312634958983336595054839020128179989659246286439765878559731117232129825071306553456761668332579383748330187494787851292603811960772624501933221927888590586798707104239190490226941532442648244651541702062645972985523955781097645439210197442880092264410187223559659485760902302502079737084654093770641502125500728235041312663259465062307726503590625280000000000000000, 500011405533735805824623548632177052689356221023672379545754995402124981787388868577896207654221614628842849153547841608595297614532876571262027656125186284463909447287978884135624216335240111636707599607691516714685045667292846301999077051454421685366891958707390478169296009602554540065857716060977361535186358624345350650415527786425266369168581283070979872427294770029129673280961219494846689000683891793545512672767826671933962209207611523288696717742970634240000000000000000, 747922989975858572813158411336124856198806036797761093383958979277760118225679888836205165106117581087670453550494436798621845263271357336598330299304532378091675590745854381012184413760645009374254902370721404740586423972011895163882974433939310279276081160768949559377847629260847292540873985520091587589030008287544350476513197520363408171937101925303600776675824400194286477370212088941704071685359126041813511197525065589666889596677825660331794454213037522944000000000000000, -283072783662090777474649977729511231507049558675839263493236855459773145999995402655548727733462245206317730656579085141798179921933913053239252520929851234262539461960367443936421260791142422149482430413089954877522603548035066013430549785059248510580344371443617252127198673901090593313416755720464346924153625475744761930053726835690530542389105898763409932449675376701111906628177047900307042650854196025988928603105469072492583980074422054518351187933661102080000000000000000, 136517215038209434574174549882050125551557480149821742041802913222418927300649533491138173678565135197121687673635463159923088253292149196643023822468683245297117860614198955456663112188291923825074439918531181781705351543536156791588255143346777895893268555893186704765473017329686716447233423022550308996384950635061634580047385187175927245654187814802809782831618550387580642250130772189257879743085581934221371765048889214584928624598886349982796667941648728064000000000000000, -367060319402533990324591036335222816691669927148642859166818460362661232757489918530268263752331555951209246800869621684716594066334914536010769660928109493750183913444849713432249914762480306332073330224709510161766066431500076688482699894286964047274275762585788787507309994568678880752954008815691169114376931689130489495821491217492100914193590086686586324596536122908329361568623921870578388944594082035023166872158074273605927907874774039059429746982542360576000000000000000, -1108290254508227194727592028137337957421602487312839345545260457578093873133306126768895256817370548175581198852365411293177378235615811474463502309712830844673435774240565419456713314798303611210550677025695535197174196645658024020322193115403114592264168986086717977839607031550924979192149325739123622292063291983074389389751050921589754490616658210726127412609723802661874357328281507378205106676778179590547902739604107686420428187698567409133706390647156113408000000000000000, -1110049222521586622737101666890436198874350980921944380944621014314978496121473512580316490488853158148658394782191086686084609075233560804778307740427911792464657167207849866466635566169825901394042720534967426527166006429447333094280360076109308265506372516380866266972557504693492261501795501684739573166985865067224308212710671481073434967782042604888452566295850599616562105363461056732864866550620400098572449941313221420282442435261204516704317916577149485056000000000000000, -411726757526810811874963080275936301405786990589355352260093823609188070433602947976448718435672188325179379055054111835699499847104384878955785094212044317192574181208976284162690040774116778412041687806174152632469716372504797476887917122821857002848671708578383008680180686586471428252319689898584711487832480416308487711040242258715603636311350271597629340749539891065028409421848402452340985553208506960426490039034012559271246962771828427670126253931802656768000000000000000, -1814514671318739041948531060781389303470517903376410515277896961443115710432357840028425166556195309257172760854650222891793383929062566132485542802964293157390193445009847889531836818863342929609105878815136903505576974918845164494102100291829966133575664500924786341757637841926577859702460951541374314147719344511616129140520165874929582918231482788795664310112841416273650166914967153139822439888165258120236069613370745038669719743798066403370619841656795136000000000000000000, -3393706180816642563360814980566701141464229727866239881379178448154954105764573424941980422121517777596807764218236902562942791853056110468457837501601259386326168047461405576224037892898837119573306618887424065509198047346352772256265373694173551077990102348071163875267284887450268937654547084111395874955792441621512046630490393158989768932414404255018785792459026716091661715214104761011240348975627538461140526979711968009429848556857752566342326814575528771584000000000000000, -1566271109395205574167404996930543480618741311253205345393745047144411260400730091977572832209540060658623753937939396706833280973211466763901365080627617300534724532528109261091636357805865569933237160795151547027114621691292682841655498612682875977381886936534475679694987232264760425283571522527234464112308616024832655303809307553565344257218403122104161611865632996955266999168102353474025912580068881303429528609468976725781256437549640782571456450758037471232000000000000000, -1243296250745008142963910135838990997396267977282123049409973784701068942382830886509249485232500140780041667238853408028061877286968911590087946573921464019177729672955801240166398959029786725889386680605032098872839618147570870208540456654442829645511926514694632239375974783170794763899248815452454932186681648271875455761396470212475997290346708969053847630428199050048428599862398305820727640639866341032361765632162227970712626594125020201302480919965163192320000000000000000, -838720441667136304499292638951637840407886158449788748700133271845784245782439282407821489776277507278305220220162654618818335076788194945858649805967503407799272860289299351328870265817553991799933716969484274847801489139420201351211081534391298270834913403761001719241649415419336887615980554008907530379178368663111411351552463249979516575994879238970579696944962920933323142504736528822144858952067396894420752444701636381795109630404191296030299845507164667904000000000000000, 125575939801049038276499623489916648290575783056867011605365214818343104808496582956481223067259774022882837177454909015755231080960720797791683929496033111274448851089312259168673021672387182138582063838946955844480122856908876774285764298793443337826368440320641996108615301194575767316503667024420905068679252379396569546593488398033111717403691347109335781680248540928557167293338726414874759382980299510032592989864187914377909653258737504442054452658161057792000000000000000]

def W16 : Fin 20 → ℤ :=
  ![3783734092798993418602337079666489960408966795413590499216134986206610555269301997455895593377675171692540615684464753334560869706530954104091010091615656478028928992865755752745554107701679903730131633235014669453169828242256960308718697740116565541779736204903079690103275860879493808929683328487549878434208417746411771639847590260222125668213271292978824227924808503889668539131658538399135899633789465682875445429482558235068940344184506102372535994065357459773569040148583649420620154798080000000000000000, 3334482840320887013672206544630057817343443306080585038469124891318777156971079412412246263650618700580471580923258567384663839361836940654222583245111433080574914253950425210183112004965795057050182292260744225551462715725202627047399185444566415594651724622690948561232381049333132901413071308268509216421201804056028165872839647299810216746375509872229023154008563583224642613063397829942917272786851063907751648876706321263382366005105405339683116415899337033804800946540921514271246576517120000000000000000, 3206612064259445902225085735653340973834627556277999951344935624777515266351532431347391825556974059906791538157026305129330246240179443961133786355328578965578108341143571928893524054292768385411281839528014419964260835281681757441351790084137711157920716598799709815628512989464963099291241888704859422950959216089491477735715119297615872625021450954247088613544074786138548175064714223487430865061183852599177077825221833741126010355985039802604124995328670754586409315844954505122479934013440000000000000000, -6676981300134004990759939122788012579696317967235854853184385855193656109921119160280150099939043721816395731761063213045147613478991737460468899130608652624818912523723334581232940143071276093276250461057849312796387789382686996078599559824779818597828419288591190730995985400844841614772959233610331789528120062850301289151287662518625992794603794936423312489889392047400829080206529295403041351392445329856507843604163628203123455862638284923714293908610165027389745078497958182272004018667520000000000000000, -7578689742689629306725986440385981011848577685706567948681718586777239935005033202536816954261179331020513991689794091318877783761779481512765051140469048824163818622153525365187442628627464161594442478783634200147969872561810702106572853296366574345423538841667639041980064512172057041006030040791649175935464042157012103520791936794158342280639936699846105035119241885098306549621437679065008534916382222158305784825525424584102110761388904716182758766378682366213044335364013655004050383175680000000000000000, -803102545962574491622699624206910292863443683231162448888756843864097297352284386396331988004459682094654779929172154998433100641519349333245740056223535144292882028620649045748109839895135199929331283412769036029940585245606069808748832661199624669534374173438117916824586394206879634289583819793056358846299148546064056747943759206588447339057925894087161417393756884915977128150078824121929542504555759011185573450300232674723220788187938742194425491551912922833825712636343476659108671651840000000000000000, -1133504523578850541981552688307679330953980331816615241636312483322039694873250841927356904440268412820103834023493139289809023941482268477415035195641347851379707351085003581774451633183698243219798868244613960451047870512459044563506597869779899912149360684190042665592239629958475361890993280489746378246487112831889393759419222055363053137822519059057576446942242989652629965595293723761900468247773479799880429521740001856225624342258592906505098134564258361557199917394275130640321719828480000000000000000, -16826516778440745257962240812069960897433910808629155951931078296607667082187658513819232071289279578244213490270120502914761076469714142780492871134234747037050389693109241557385883078606309545650376911066547800157173983943308880503765907186748059789969394625409432331137771284562431739251673206714033893246158177893989572845240499407164741551633295048765750156190935415860444614701040174427751082686646940077698351668908228086357982541980413917020651148105654126448964163446783128092146610995200000000000000000, -14375460602961603114234189269893298715941470771315835211713133208279948544578146453059559990698156176410881145732341052847372402147465727597745673969826244860918225175713883328897695242569215648705239180412325242039592037397211187269079029379808882368545908245153226497298069223437278637379806592716464883432055652193479615255204186224457957071563499436285086574724039550517605197083755943557981236931656161057162696448201905818428168644069998920665004750742865164753044256602233546131080735621120000000000000000, -2993148756007344389456783317440261320212337756553268231582014923774189072917984671372484695429554323645822243163125309079472968361360248564533344544800575919195823468288982611795696008031561930726092675995635290078356470935264780018159633416976448490382093089589269900393941696268900314213863240088238456862938962445176107441214528079219816354740360531309473190057752733333615959689884528103124589964674069054408186796077592147279012225498988223838347305498507166352964990052100348182735418818560000000000000000, 3153847050610448389338368279900229834831543464032429575019391483081960958446070129194264965992392932484291848816804309986334475902130270145075104230683451342664140347046592047513796604090306660634351094252395530315054736285491395544984778223449749060613477615511815775480506139219414115745313237821508128976336533268613048501893220088265056134219802895905354263664915791487091876605048827407542867070975627995555958599975343294719198592458780360589998782410382014827410509732452397830138852147200000000000000000, 5206843151267724021204014165125118929139666687209667372703242550089678188301626989649198100098727608383325552221152526821041759226190600009965815557329792095990828140307195494692939357823481658049231023299869911856207660103341259656594537546516540130938582287879075492932362461312881618848380688097653445419582635642782491254307156500143990294584405775985145991834802768667969317351210423489873224810798216450100699596747828073683022156351609285603385573412544599139347709498222836091359431229440000000000000000, -3949416044431453948660641077239964246193435250624628858554378754315315171903219201144910933304321707916807430133470789122371970360550203836608111555072054852333241572798946434202720616282556576994180901936267655293606170158954019823218220119682628609626911925489102936416741069039117796151322796365137373576615394887009405100037250892055460783776083187970720752616011370047552024420718219400873544708327546402160248164222228441472801583239594843569678831228226393181583412248394457095769025413120000000000000000, -3053916075775497615688524384713442563051388311433329565312147321198512124030827240890302921919075732321019320051231952533375466943666875702432367996366916220124036432998720514922575261104339110679400695735257558746294635595918999088358899211327294439419484671670735118746486362108897034305276389488018216798289553159944683747712569342221673821372349557548253465868251538676321881420591815128871429511736641311733995076168400472881074974463099115982861779878835004844204457584807470961138283315200000000000000000, 13325001938135835681031984240738128807167812814725147377780435027033256923204223282202391714660803538276578880285858054542518844515831497474257614982846277758740745554555937041597722206868206958796219277567201704943801907749803225899304937140038549881502550972828083736745968888018866313239114801190889978206350398487536933727406421091611199229374258020997477868526924065584034021976652294663360516072416553770791575733799073752802216299492469804802280230635101450092974080420708774684104827863040000000000000000, 6617975059577468701804354481890604731443993176683981904992627312654262349254954462357353526345333631888091938149974644974180313047830284837340992817625070441488290058258548096312299747676382030101620389516615491352530386828832540713101402200156885758350146714791921939828295711637350847251430293944204025313256801994555746720832305939978636149331722498185566177653961626284869380304455742476126230091154027896774838102329509965776965420461952508679493200362405201221026351132317916429291120230400000000000000000, 951641109433701094244725978982221260653562192145307632928124266015142915862795606846782093523496183649788014245514787716300638831286447911899655552022012058525304496940595365343722451239970914440849243897053751620477278536953026277565459329019319116457421201769344167717219644639861234774123062880988927108413546868154624619883597571139545841783808718428635294964471621569470147077043012866886348958405786989338213919329038648830389333825796901618434845492986185389421419777757605377126988513280000000000000000, 18623298507911518444628109669409147955601547943661823835203548075419425136472025038419876423888913316196111180041650458488978354189718745084191918514741419114976743215479515939618967644224164508079488693387352193546950067238803711209288386789809264465682366954790138439171822380670445453123888559586959131510569782349073791470189077843393522836489945286277354498569669720845746363252912786358988794418707207363584890082094227189095197296796022252902408614694494045847746435706427497531147949178880000000000000000, 16019007706630931963292292846487996304563047441975330546408791657185512540350403792748800975363022060269286826002301648536645106495767714932223494245384618364680475609802903098182863604449010620254317865143647118453008477850588449499226869436882832119123819257549469320981840154568019838806890883211850235128973301747056444196397945200454559744841827514694102862903140777643030557000303182713549040089055366529982484925097330012656893616526780110074971254729426632353570484865198205805334290759680000000000000000, 8709841748867079095721851257942745282993322583629931689078355724333655796209325559051547406904632960252228088394948348695283847355450698475733859266282069351479353458459344949665145760269390411616999160930797326021610921935615779253631361371428038547839643347210218684694583984150149707252682117089749626732999170389025118844351792889550947288818564495069023723314019322291857169024101523234267728355215578634978054586845769065222976117008712102787459413438208832454348082864054043474935582556160000000000000000]

def W17 : Fin 20 → ℤ :=
  ![-42636021896791261752999715174557357756394526128745378093665933890738099790937351460332913953976991161184469934496300122906716508607484132297767159042339524057483357459160607761836868125987611206297397947437177353237283193438818726577267651599709204720498511735809238595921752761975568142921499718080508159199363720844915098445743523015156204264694286264813090125783796235228421029394810062740194382266484611599510070758170863371501484183202059838676052569049481290822677995194554970031832903055527154968661617971642944087654400000000000000000, -34696260301567237199383484666145898146888406900625590895307516745809017272970839519698491429353882365656683985632447374471072383262591745436297214864493568020913450572009190412512672875847727645766869447490485464538809949433489911923814566785647059435241499718620026722741345891680353960935373802776665136665970064567534679633779471632518737926156974289208295414830699415701819647114532841807102418114040097509965617437946495751478948007246776149689231408077756824882755554856517635066284938776812727689824200365415203759718400000000000000000, -69143688574626729435317048751493969617848086695163636268354974231566608424298340920348234131426235912177032591291485555013465991089196432052585319100007633411261632256620385969353485710028110771662577561531838668222883314853579613480562625297143245580206908134612559547829931638964986876310557493624714131588614149692301053314081368681196875894571785200314546544681640019361168049892220279879632369154494697249568252578698360436946770376048503686139530803010608242557267278349776368699899261819338381049062211052220201723494400000000000000000, 68804866011268679727647434122877664915275953444057627382177600478079655591423489382509120699909489986162148128424353444583731794008439942295329502456952478805371285036853796301569703687208450325486597466209557396671943899851404393205093001005860092346566194766593910699746536917742662295481094482307539611167499620758209160977914597902406818560403643442263473129824560212473780026149200579410320261491003417355707963320244775206379383635007579842928056821913834740746503173685118068185954055928910887907740682454103905796096000000000000000000, 10309442920326335699201694157643960034898868137204114734929084823969062860687401540632777021374032217736576111428801676048221177160604509978205489618201616034306875281286462622439498996913429906147094115216984278037371371723608110436742528645768652400309932376298527270180794768543334715706387837064107790192445090508377214246820826645276576684611841514537747449228550007591276913172502455496198571764478200948337771113477847934741773644091285371487139511277748069684782088951527167701912364906875870627745878026284893051289600000000000000000, -98508527384974357293635689184358263460333989170076887148617281118058871154027141284600866743281524457217555210771166702317490147948300709057034119755543524518495374962371629174733774199358606230498820248198689257231377994958780086851697517188903258073688210109657361598898032969608525412433999946324562684231023076555566159281487394520702188101072611295443925294050995208099085802052111727079191951622618029025597653681583687203277841087162065144862248331819869403931868717097936294837329341398302553219159869232030438286950400000000000000000, -36251728984322693623557516771549981924858268199250469945397351029152460877429370940566191689857116210758588692281174639905411796787950430318302008645530510381723782327119066662428038961403954979888396396173830225940142725805993399930363365146315558380853802715505297668823015606032983507869529406023596689180338228353117989805026899578410039092320691675011434321140420018768518819029169314147760258955762970938512494725778950194070534046253953873472205697148806159864681530873977833528002284012522222628410992009951231082496000000000000000000, 94358188892803549787723571449654096733767002120950428821802682633883695482100650423355096011369128864514808639629675153786385429167443393762490527219426370529368052762698991305655680497091685773409300098442024147426634268942743447117586734929461906394451418630370633004123105005900818208608067167204406123268944409376401765349391489737126943900853959260939025510068097396079653428922566219073624897297234810212975408178148893189358685963840647316111919964380330795289563283335856432745382684891475691923188317406527807815680000000000000000000, 118094530446718995254261833370528303323525512464051586578560143191631574255766906768902524318390700832630168326145539867877464759563035165114374211555185155727230775058530272918638311983498908190192149058973455666504704645111173124528044058089460574827360202483025331161220955819289150249578545422005755788077871726506118649440588113979137656511703587514713809598286380303631911085465400694944834703921743924369613356443219943311528525428893305004348491962051990767921357471357814221411863805222229456648918088288641926509363200000000000000000, 21345897751022148149027026655012003483172854503297599745128757538705429736393113709247289219887055923774313192186303354779204014278455699973978759888421011488740058417779505621443093207817587309394456410419969619606587364525902006564698851039700127445305423859041901809003041826137977453605977793486908442278484392893979104073189840004633273364368002483262509856006717637897627545939937317972597316791026669824048548462832248562663775011069210442731625550577298865402528690393444069481894697625480072810771870679285195236966400000000000000000, -5446632150951084513836044197841663896661847048288774299112615406005306619377405981407968630090905747870085383661442695447981034827912284814622764783499695026034838159671661620655397687944592181447024331298746447916269231616443666451743681804139706478728243469657653909312530325760444479560200134577421092857527549326455054259459976634020727322391999171038553794882721314513862922084751328963618734320990368055338113029066335043426639534202440236320279881796864166881351790650933498925380040979867766636927219547897105507942400000000000000000, 37443107456687549655855589328424411780796726679627767716171818254074394717748088993223483202404391931772629342529994944680570730129863174584884936340159936821767352905219636426754977027372486302233043494081721399007782891101761515437473847921541020420377258299314317354334122491280502779738019679913624120312129243927692339731964738403438544889921880714436974572514294803169384209092459970643464091319552577207572724200812347597890859987764341174887350482218531973501024800236135212428800582346576019001306327158026711806771200000000000000000, 141787590894693190490927044120537444476459999609102733768539994309253984693501509002161220623972321868021062991863836868697449088975510095295804822434699199179286180874359071539531982881994679895516294092899403458946910376835218376320173169727906950870784945025598328712578646583418911538344173024456799771098198762558343372182267734389107511153391151218396548660616328276697850838405269182077416763436026575982527100494644665346610002545010926429673936609758271830795466049866846874834478789508519187427188019629431240785920000000000000000000, 72543485385980232747552390572568058216713632564618870870099803115605800298618672826093356867411808465578272193301421199666625652734070553647503174633497015698528313168475189269129457981537298458282768273858617417421307608594418802787109019223666519427671506661273911912078777103742748213034300349443322080640485081392398397819512186293680254407056155308181274105192395640480019929092287252396985303545138342601156613476779681007688541500145974930485757583166361699263735850920455951711591441494914693020705776025456345088000000000000000000000, 2669894393982786418952831293088280645936300991114187965990532960639930047366791339619698146715852522932904470205843305746311418149818336858017618669171879644667064305926874845131189733296503115797384060303023560000018613493511964716617953970885472676739767089309796197669211561981191882636784612848346579919747150793655182010145605735143189350437311399494333275881819791701446781287511688775706031821078865918144286275443801242932845876075891006659295327219472419701664246443121367435775932905587744738926502298395541189427200000000000000000, 232067647805479092837914257765760608388950167394235266822944247657387930143835273660720152267519830849698004679132696287763970524036990019011639426502282654977829275388245155371610038103844451119728345471061475607712439165714582496185187959098458817511499214270321267044704256609868309978951932952852888490579010783411218873658037961145262045475927898109370696711798611885619958447907640130463589807998378535122959660280625625827342357104024518083974478687662540595814539694281851753851160745530828339168747779686234818242150400000000000000000, 162952012987272949727778761445341639448014311736180931088952372567697355313353847898604022502675809536351720810556122191468432063411597316315583161931997537826776621996553984742489794332205302602051363628926454938859194917738190693195848387002968520544411802580488131918380016508981515783861784380829065789414674822716914563236905904259356535131961546921549103141576628721249879325959232998719960736218927142480026472921488689820257316744352998356957267174241673590253954992595945548660824620210696117354535520596541562263961600000000000000000, -41097011230848767864610498427121220044784444374248503225608574904078512400297749601182791185524541174615439704230433052584960849881683573197435051746858236736270185950533955720879421331324854810780412815618756044184609663824380999204998245262842711765161449029126699204338634539338823304811307977765298967450368663373896010916533003426638552209573947856282701440956968724115233481768288470159443010325851488983419505517104974408388739206859751934817683753364387570486989775519755858471864541259578689018423881510622402812313600000000000000000, 4715041534153941113044748455121119969856573692434094342853508971245856224844596012009440822406298921626636011764985914754709772230652511666014038663053739203076033520395987732344415291917431722290970907140268859309903688627068558387836598402112460045423566669714470819477093710479088431138414916571608223226103387427924749614569190056099998363157851464695054384910381391441655840764609008555989424743817827161620357280060483686908891243514571588454273529042515290026557281749021149343627505829497870242813614238304503962009600000000000000000, -49758289253625890540054477163981795957559119184262557922975031084485507618419929899870550054098591952119787360752963937539115683740383403202391064051120645591300471917167671437956700488411355021847584787450729011100365152438348227802411503351257593524410096604951872856016830560256885736014895541246854325382944107954268539083377784604463728348271438011819356661469531585302505090409382506724328876871529289562753741828658788891495866338765495315703625833468185594755942279347466592092236408973556042161170594135527842539110400000000000000000]

def W18 : Fin 20 → ℤ :=
  ![36003900747152911692536692473511345090828082870167594061535239801230706055609618906280335220679589342546239866186191204809894076008950158101071075306537963167007819371312696425912229400921521782187331913707974139567047989654251422618328951517106213221837885218251791990226330497236829073652761036305881622966823609011225586733297936804224090145147093709730333367918750816604446949633541838217509335147826919827991746103454554526682924832805202093971079168422732118375769759033513367494923668890889654307529511569873384414457057539582082165667516750233600000000000000000000, 86650902340141051298149307508634668074098380427138929296264726242874628015492881191562448386352769582304817501685794978463413497481092896008654402302607451942734804156162574764587649875164072234422638030489903250208749894552957157913499699344280744413926259284232664417450393328196700989773530082039448773206610631183972058846102258399189939508357276606698069960751600206168442887767209253898360840175863712126262749972834441006642956986448154082027227287589547052286119387062109669165044136925134924581015970947249587267554839007271409276826562804580352000000000000000000, 151067734456964150486979099092948357244890567577301375891287089383294354591668871918840119090200604811683243128976429306211451776140799299657672752319536283900113478537685765012202150372610475903485826950658398817595786111756956094998846009808132651339557336060046302792149108431193039990054958787947731520775289368744908867934913803639462960919646492023765422286489168751782388240491992326058408850814034011230658352240590927668751162361624140667492084173511585139311626532662208114009555920879591312931300937967907018843124302818074417714498576744185856000000000000000000, 3101085342081771521467480905596807056175203679983015057340056731626687525247250641003946820933279032721816750205583869948782156259940791285434744891300388396617412267290355769980036420608184255205486581347171127610700641691179559886766178785366568866338789899166864542251385963397122618125019802520834793349615679772910584997048631436630285195684733477570989446703909086568788716495488297139781627251206920522526957899602294747531336803986667243424935431249939217274941165918358021786952206409825084800874992900583860205307012905832336368292591063531520000000000000000000, 131643269697664158121261891615599082948813666556707159172437663257750176176868631843691672021002827370459307392246720553306430322579144953948990748081534997973843478525195445800177313336973087351160245934695598254626169038910474856464801007407603116853453853141069148022865671875743637318995436408110371624236210176144054230379129763739852838566189887590300546727130417393524218887445976205979157574663746804528108720548222367924197263308356906218316124741511119422275401800229725763641909868075913000099611334769644252623235887397792376878496884805599232000000000000000000, 394872285863332835192607949181118532113136298481461836202397489572350837227442542849602870377052479699327639574779350589413154643167410745719331644960867337544310128500930306072888371882392403982064735285738017248792041567650309296281520045607199686689464550443754261558584992741788038379415233056215392332202321729518634180480186818695143206889546359163249459935324620006385477141444459088128275620943429507447909663654696443300482973625613935956591907018407099130058440867784587356977266180574652959659488479348618223902254775535251215142330522325221376000000000000000000, 196988418704615569541335555654598408034513419969698862177896184215191916600970311269335607366842544116882777081241850907517827496031339741743043261844129892491437220004039584686898544827842081627033216152395099659117681787115789278908358324834380181098401528107881510760182008495827081449029382667401503361297416622316496702771497873421671717815369512028901164230086946226948674898234946182639831271100767352579413161404378065888209948640790373797748612691144338275657673712857760598152615381785791502434025454496640298424034449213268450869992042828660736000000000000000000, 63831689577273565696679898190739844955487705688833079177691592662683848720626476851634243182440818512988875929027401383844978358876940757950613143640806685943055339284104807178560396086273424687585741084254944557548719795299363913259509674230087146845364764086288626209613633826137088344256551475042913125098264705191966937851540784999480225890285885808425269225734751880389079692401021622063459988141264242321377450779399780256930686643554536107853893424611273625755148242567200306147038513356813425957573718700691619412673157422905656347919188152549376000000000000000000, 41335303586300151468112204591369989783214465571113057343021603060024871508656793812134381482876793850412022521895180872083739447507947004215639264196604007757003886707573196302099785952901708464755236129761769128030961997822937123347124350245058721768483360042997372892272167476626440862432393963506042695385836439843067256307196491740387561248162267266352429377269951260334267198513932813251676990881130971385433939024593839804253193969009481742602284270419754533013272805867758573051496499127222727963719750116134685432569757724212777759436770256093184000000000000000000, -13706324406962704889427461623497513292581855013766253949977460083239672881567981543336120101174592522720274686691575051393802529090686604761248429478082123914710076203743991080416486957006883895857236213705675996683130183709004039425807544666591225927232400152825095590441380357479439209332329912889187037353424405509279487234801840048942693320179649569849458471470722733245897256993108757935264271769538779575068704771663521942134430009466627518098725290059082736816067561184834876177134837076679842438515457443528382665110441408402134271841019772272640000000000000000000, -57640763041606202420889477486484375583017053494173379407430872286628936994540549688266773005128210067273857568201610777993942347422183453187084803897236726547530349776098862748668652190634688143516983783840596439245453661722764504761082657395963793649418740857021788112592046878566386937643447973815370923732579594535176587332042154889552242991760144369826753006696717873825451591379473546949470791758792722261212342905056258654216725657512244482075986009349633054626719909284332814374899193191144912426703702151365484131172095808652094531716547001450496000000000000000000, -293200346008425151124174803063739273950351942897411552070888612240706817260085931053814362751552440433094649047299845413023450516752069618634367407366922276929927771641333946994623480408462355924844089442479504795925480482643658389036437326224715640569496543672651321804848009325403238989247832252775179854652704008653471185082582346728958053370515121812611109779957586748248885151337679409619379692331624696343730384248896071990618556380797370925661812226082888805571841162795035378831278858690822738931897248761994365428784040036058519313301770336206848000000000000000000, -440275005522488528864328372275424836062816238760155592998640010912051222573288465346231004156024002768442035743804264697935711731320949848682832360826850962234707485254661876809604378958597151350890941602985766795523158437264380916445566152199680727374083868996413704611866826419166262830566848993144387247197812904577672021510874923348373228248879590728243802502001849278169035954542355842457929805685542638916102025385554722092497696227149863973587319472970789077194929806555617266620358707789379841459918836254316361041334209515373461391948516757078016000000000000000000, -154343121468118043223263452899857169789622993566100410751996766830863145863057485700536478843495087669487422711100505544781300173857827869562717150053888837109591530635796427427503522719260164629432378809610366074551357101002679114404865749029672621343674078735448898553298891059451328618236647687209385472410287206207472510452339417512097944093519972149400872253385381552373272265464031463463912504967613892484061236888056404623118427617013378858290031617961381365578805436942571827153616101629727927193738444039366318531110445965353908816392433778556928000000000000000000, -373560789880675856568906793025221474293223436593218775502071505458955706611620375346053491922954230131553594494543837157459732120924875359578614755209465166487129870594514944758537249212126548876435731783791447840708057234671237275359132657162349422478057390564914231547245329528120349401485140540383245619214692781332157589570102890327998822007042894900714479422804855000054878662514208897214863221057464614677141631130731494467390608426577639169804119585365979190307014964806013442060842351226503221264092535816647632663577730419994170727036762961477632000000000000000000, -1115332819860685770140961290775814520306151005216860042436120743923514115086173604393646585092441304605842701451118423195897775319154055136224824274889145530972360391880410567765143132775329403820217864214352161419589558334281732315891233692400227785659348440028802674002109482743841593686131632432364283693174696791862552488558888135108815054278229555448872291830427216175341659663736795423000557799414628517533963061842564556848209177661936985313746811181637188581465074169399036363752724850660467333663438248638156553499898396122236523857838318609760256000000000000000000, -584802185206748060815352183065781240096612579203651838536340234097146558363205669214867543142119558157164837051042924343481106226937006802923481049169483825740707437206039282014642178508024133499799510885052256918948725713982824049457511571993569131367200659320844205022520265427096575808683073370522062566194889375035408858582586756278896165689768813246751842325124600160481944047091077272521518284882726644017717876756075464958805936706000552275122965893630273592761816839513357809486985068567208967892112043862547436550983773430616216867398421011496960000000000000000000, -428088714389690504240816638538266285086021116917329901812059317236222527968786340161006036826801722989647807890879804257292516872488815843686558136283893236027216633670401044777403159204182286806501465369200376151904356199723111464011944228040764482395518832928785840937405780856960909135651159979641873188955880174403116877088518704431130767104263949116157184499732406421509997569780076554862108959454539792632225584631963120311202426824712614266650138616275045474632878448632092201801760603702147878593308424516469367342285401068571582909197618771918848000000000000000000, -510001818432111013890559798287370669819568948227130866641436990596382555156512243136531186515078512848803215796320317852651616917076420025068580719843867446049776898627149418621621143725539265228393967491027475985565245867380445627323899244705830403055194571742870080079047341284355459134451127058371673137473463620139756082715367480291656894588506069390460714035544081848952265179799445085271982534229884916715641797062048802214040210876011950808122038312359315391036104408974318647671178920627417000066161566017485656165855483819682984532618628296605696000000000000000000, -108604595096985139850626709167481262807516449964348428928296891368946791567268030834170425179895618878917763454234333819747523702147470384932214868192163875860670375177874412477860132024475309905810384466176937931511059084286350011294570701018237954429627489482905478181345094090703372379839484579012817194270530186887884976590416781643476052821800372937662229355957944586394857824982909208949940729291386665629433255291868383856118101201529416223428595724616127490451965340879783843200170998547799692413262793382794183370991226858915420658115741883564032000000000000000000]

def W19 : Fin 20 → ℤ :=
  ![295890647821400076424300560861862298660371506269253221661164571753533960009092374360323214809372358417108012770793701787121653771621442721146734090496258319239478885751280544725890011279784589550235531038899647152056529462340303514517879704204397867894439156192595470032073960907659691064374368463196998258050160009617747349521003066591918251333863790517612686507251781196090463587187896663225752392308778622643987903450408158719629712410484414532667642483152298060213592807683446548139120853681987937237089486827111978011817239573887813217312388946024799583959620590578491802559447040000000000000000000, 362504355914176645197576680086330652703137456288561187202906122095872072096226259843835390377556678368526568279833236777711977121625398782104369834684730773593012235695897697668256288309768121529375877248784509370723696897978945927612701320466980494856976753382110893469879458113487518212721566238030705722318293405198589697756168938395062484761784288080844543124077961663077693023550814107238565288920384367695419978346386573480708299531390167018931825986086722615567091451019883292075570587583430456021118711831302767947429171219825553906059085831946699323804570765096447898005012480000000000000000000, 557647544146974617910967941857887362494965796968272877877944528563558606432009289007463294452710198083389193338493535942480906706826347365636118768893506013555330123185616376398437142275961744610298824804629800477423262463245639405374845362989554664233011594031301641814037465156403298274905591321425151583085405620952483670528123762738076366065174049735920894526338738473951918118446084392764316167507864535754558191932765300092878029860081398238866298680549978881828088748857922891704276629647225496634791860874965582546269785319540621715944086489526186353600539539359646133256192000000000000000000000, -416336102266415119152365652112662941383790933734375209278877894409179577001925145153564978468169589249855543038267781515955807678597353909549726051558039580196939858679599914879479952801567324511756772642679775033956724442498430266216082574982060809819204651623481165563701006154322974577246771539985676457576005959053755345827723345067250391225710848207637011839054903823967278770886763413743765113606037833164964564640170491796200374483133590519519588750434035898889851643764056724207025521863688646152728104651429333218514405099559260852169703665024992383326175552792696968718581760000000000000000000, 178720269180645453313435087963257923376792572662172351411919192104836355792539883566565959623649495849811454004847638768865585857950264480562832058161102638326977912075721219127688650065802665860075214818668496645974263434485125780962903324450736367507768711236176843732499083978069333838361956127075542362115258837526361382892226039211203843007119998283468873973078149326345906583917543433430595090502142853588919281246982722682396174700734950025583353828612127862918603428559741644285443809823551653698292949936915727952571448516458025915161516714038474935111296562043320637094625280000000000000000000, 1227098226454052618068017536974456231568964416794472766035280404882665976272871280519626945587971071538513786157314943524316554360211312716358384267435778244850769281876247377317374115640275720167392704691645710896935232895176018705290002503911221220645249765245455656929770433091970269513162322257094449676123974057176992107056906273028952587688899579816218609440974384617881563776516748207502826044243057832020468967250940055815042971145485198381758779030562610028786151123198872006671573780386786686768198022193136792944331407088532912339940437492045214413637130524723323674044661760000000000000000000, 297952203589359037055842517937173518835670123857321620961095655375476617489179952879644088624448350518713611749094833397311480779657769826678416106564577498181850958185346844430647277702577188692419804717938631863589645330222394588962041841753791462389482311993759456702581359049681957340647432301119087038599028327362652815840509550710865333699332607917054872598443522596251290468373322028695990711820341651525843566437154282427362482684308734443819616866835953172925046019870065233252115217387292467315245440842975932159904367792847734958557438273804031637055671138331496025287557120000000000000000000, -458715007353567950153766952557810214902843629512447684743870809196422020410974815374191913911473527958822854053755513516506877651505824948495045270107909303551645923309193638073426239586836243483782895151259182080171772770136661028620604100311894304729380560083001026654620685894728971129421773045820775230263103377814506933137484626642644490814376504894977095119894796595380410689698574815042393400020737947310334105747774168123740486260642394229161113730340120635473046620296660343315250074529612741815242923854777616661704796645181543954179161351020993395889197658833441783304683520000000000000000000, -797486826072933144069597264581283315144838396993132137977888738712469549521139184380413072076042156412816582628440399868467270637077758741653261890852050271659626550223098185521116105268291332412124603245642371007684716597033595676006065427081956754195939681987151444316172644821820131399420121911644897131933434674028751017196561064176081051684934067352602610410768289519001659629589682668904285556641577074991433089574176754383417473586850062275150763452506493808239519138139301922474814064747490319653886581667046567263634287180102787364426365407995571056268558679578947073521745920000000000000000000, -164262315867575634261403874178657762698714503817545784015111121370514873113235230107519169709241265670504682472375310258613893945775462936226997289361574595427450636242871573964053751395934215723195980222689541036380607728168333579632494057143726855088316372998765380296791008778185470275776291137748308377790096774006612272182706043494754621442605518544839897809684305170764830071958149722457941894750394821259292888894673673714566995163237530054066626188396739174066310566160098697346605443218476633866983290269176325235270169771604940900121699203899079026899989520633881056352665600000000000000000000, 7255425211822837504911264956493268464729205479772536889504998965202487308811452827774332593063103867949746510462103559900051238997912707247291105827683932111837528392754974744192919611611334877519935708377176995427151937608290228383381607298455211034796136251608272542026987472752958159099186933412771547263595110858718169449199826531231889544925606969538445233306345054072028427215112737971525658598989351428512008318894959527723094517204733710128400593219518798965436054967245950475785773803265060185681275603327230317918486790908061864917013616112110844286577811361504550883164160000000000000000000, -554410934819519822417598359135726695169838393104568649316244809284660142550657982186720005838915000142917843939644020364852076577946926037062752034088849443709470577665109115647742984322800590106760172227728566892582706171068884306074941005305276429683178490108219631619055063254192052307171354081774077208333708350149336881706427504045298279140296668855086690446872933004814532566465254280656477891831364118499268238442426171653708463647470364347694571391880407188588948668503244437312024345760282486402496238909764746445762421650157105430868956447762567457986676662189433879380623360000000000000000000, -1664642383958649908230257229690917278786948167856526523706806522105231081823971561627698367782770447105431392030791401208119396909784250536873740281031677501830442853433064376074379892241007044450771375435202131129237856605910307296482435445776099925220570709689651469425062962466332761079267653756221974693317711037125638194672918177965105128252916957587347962423064494685425622963762993525817535788960461151095802227292633207214576674350814838715831686894540593744876413725415419585900620150760130454457795469260250215430405126413118944933129115238286698057563042264708555659123097600000000000000000000, -892443142095608963661157577950058885237259048985294751316068381235426078689649558644796467219629934114538700623149506032573264259549329628490176238882679637317772470880346466482313365283851924193622942114462864021846457825457929833937706125421201313198843871856223245616215441883372249743133123885887410994283677042558242133431674325147690006810436396590913390150864087378773149449409630099655682818189703508229606419319796441600486527438309479821779402092350664416373565662808681091245959656304707066222890825746734588464462382070013700774662851243560703795474614179814208950899834880000000000000000000, -442386853118252668679621595119018462069354477191856960948874503823342942488440494712312253678582906872598757723285704748150627930417231465992283015420121489339947082794565467186742473372280003540103600031028846857255813377083557164279137741329250822782068043127631660465806770392268995116363383050541924347832105302694195446223942853706250054330956060759283671897023587696291619751178486911687695032409968458330603926429190811742432872424312387786580703521147223454761545002692944638161023373938971324310583077700720503112949626375315858819748509010399223373267273816729480708080271360000000000000000000, -3092652391725778620981822123048303977821836459379795511839955301919610387887993865559994275064998835973679553220238459513806825622951095346140258792955238671155314029176924349109006244071646595354296619463330518219491543597221132525134986135887196903840350322887225392180800549563147393093851690654829359817417025219197441646983017551282446096075735864854256717957780881732112470582108830043423434115009912338092302607819392032799238889381801846645139085254092465731657887073626556828902914240944687363261052793950502428191669998573084998916396940108687646112403722045770256338984632320000000000000000000, -2175591826751612921955507288034251920452273289260423606587798832655244746008029600095217111855997341566875545415895408200739727018321442726858491790087519605811021993357746620485385087266215086130947926135985826998817700630762483517720963024878513389779088061187714486064420315048451548494388606716318089028054322079744187070808772957835105221229435863233557439536054683492480422444933098090623892190238275753567369915653759542469060054640933259744939799403172060553463175844970896025232137425999588065324382296174077970820576916147326714928414906505961598976758335130422958149064458240000000000000000000, -310534099959915992934386575827801677892686883045115657071742576561989793206017097763717314558707804318167062766979117837022982495089686534049549329966616018637507292755739649208763440931776592631938163551252751396302650307871801431173143823791706370629758320570574470134130290378940474785482101571424935876055441029046335975597788971181760894730759887025612665566350246763297665364729728058287551170022227706872257527988775413237882823947718065873285555479630658494253810560209285400538173681787003204445341121633869015432077924745440689623456114238793191490578535340642502472703672320000000000000000000, -840120169839087769764310010527180326758181671537308797207313833470531269787397010849880041234472815716890696960071640507057398629762985662087992910482896737839699193929380840804764261328706528405254165835503091793418150988485538291366143920678496536053578812583520876509768408064230003132306164607699853917080298806514504019174906105650138076336600521465440541164161561545842580752310324882176070395092048899177291293170549521028035138824911835186042183807267950505709554199518717549257438907320130509838256762694228049083828267852898965551810893566862605358707103806006839012082319360000000000000000000, 154086632851423303315729690856943750691396582374760379156378107692472354462573965961543416501306045750892053063585718944946607945873805838192280747922422334516846666801969249045720989904688467555318466769039228893590077819177543816582816730841175874681232897502220538892304331411283194661786296712121476438766214148595434661119769694096399401134286104453979476342644453125474626936486829102326301523254663681728075982181146811733185335751251994805407682547364931495815464226968187609287577635955673074261680531563329787247254535433968530720513132051398549670515215875737399784185528320000000000000000000]

end DimensionTen.Border

end
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
local instance prime41 : Fact (Nat.Prime 41) := ⟨by decide⟩
end GaloisAction

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_PencilModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix ComplexOrder
open Matrix Complex

namespace DimensionTen


def ExactDimensionTenPair : Prop :=
  PPT phiOne ∧ PPT phiTwo ∧ compositeChoi ≠ 0 ∧
    (∀ u v : Fin 10 → ℂ, ∀ w : Fin 10 × Fin 10 → ℂ,
      compositeChoi *ᵥ w = productVector u v → u = 0 ∨ v = 0) ∧
    ¬ EntanglementBreaking (phiTwo ∘ phiOne)


end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_MinorData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

def homogeneousLow {R : Type*} [CommRing R] (x : Fin 4 → R) : Fin 20 → R :=
  fun i => x 0 ^ (4 - ∑ j : Fin 3, monExps (Fin.castLE (by decide) i) j) *
    low (fun j => x j.succ) i

def pencilExplicit {R : Type*} [CommRing R] (x : Fin 4 → R) : Matrix (Fin 6) (Fin 4) R :=
  ![![(6 : R) * x 0 + (-12 : R) * x 1, (6 : R) * x 2, (-2 : R) * x 2 + (-4 : R) * x 3, (-3 : R) * x 3], ![(6 : R) * x 2, (6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3, (-3 : R) * x 3, (2 : R) * x 2 + (-4 : R) * x 3], ![(-2 : R) * x 2 + (-4 : R) * x 3, (-3 : R) * x 3, (6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3, (6 : R) * x 3], ![(-3 : R) * x 3, (2 : R) * x 2 + (-4 : R) * x 3, (6 : R) * x 3, (6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3], ![(-6 : R) * x 1 + (6 : R) * x 3, (6 : R) * x 3, (6 : R) * x 1, (6 : R) * x 1 + (6 : R) * x 2], ![(-6 : R) * x 1, (-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3, (6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3, (-6 : R) * x 2 + (6 : R) * x 3]]

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Cofactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

def cofactorCoeffs : Fin 20 → ℤ := ![216, 324, 576, -432, -282, 180, 120, -1116, -1296, -216, 32, 80, -412, -384, 468, -456, -912, 936, 288, 432]

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_RootReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open NumberField Polynomial
namespace DimensionTen

lemma map_eq_prod_rootSet {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (f : R[X]) (hm : f.Monic) (hs : (f.map (algebraMap R K)).Separable)
    (hsp : (f.map (algebraMap R K)).Splits) :
    f.map (algebraMap R K) = ∏ x : f.rootSet K, (X - C (x : K)) := by
  classical
  conv_lhs => rw [hsp.eq_prod_roots_of_monic (hm.map _)]
  have hroot : f.rootSet K = ((f.map (algebraMap R K)).roots.toFinset : Set K) := by
    simp only [rootSet_def, aroots_def]
  have hfin : (f.rootSet K).toFinset = (f.map (algebraMap R K)).roots.toFinset := by
    ext x
    simp only [Set.mem_toFinset, hroot, Finset.mem_coe]
  rw [Finset.prod_set_coe (f := fun x : K => X - C x) (f.rootSet K), hfin]
  change _ = ((f.map (algebraMap R K)).roots.toFinset.val.map (fun x => X - C x)).prod
  simp only [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr (nodup_roots hs)]


end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_GaloisCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open NumberField Polynomial
namespace DimensionTen

lemma roots_card_int {K : Type*} [Field K] [CharZero K]
    (f : ℤ[X]) (hm : f.Monic) (hs : (f.map (algebraMap ℤ K)).Separable)
    (hp : (f.map (algebraMap ℤ K)).Splits) : Fintype.card (f.rootSet K) = f.natDegree := by
  classical
  have h := congrArg natDegree (map_eq_prod_rootSet f hm hs hp)
  rw [hm.natDegree_map, natDegree_prod _ _ (fun i _ => X_sub_C_ne_zero _)] at h
  simpa using h.symm

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_EvaluationMinors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Polynomial Matrix
namespace DimensionTen.Border

abbrev firstTen : Fin 10 → Fin 20 := Fin.castLE (by decide)

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_QuadraticBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

def quadraticPairs : Fin 10 → Fin 4 × Fin 4 :=
  ![(0,0), (0,3), (0,2), (0,1), (3,3), (2,3), (2,2), (1,3), (1,2), (1,1)]

end DimensionTen.Border

end
end

end OAI
end


