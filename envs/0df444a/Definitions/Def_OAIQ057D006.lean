-- Prove2me | Definitions.Def_OAIQ057D006
-- name    : OAIQ057D006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T20:45:37.99641+00:00
-- url     : https://prove2.me/theorems/deaba6cb-da4e-4328-ae1e-1d1c45ac7a69
-- title:
--   Definitions bundle OAIQ057D006 of the split of OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DimensionTen.exists_channel_fin21`, carved from OpenAI's openai/math development (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 344 declarations of OpenAI's Lean: 342 definitions, 1 inductive type or structure and 1 theorem. The definitions and types are `OAI.DimensionTen.Mod139.pow18_138`, `OAI.DimensionTen.Mod139.pow18_138_mul_t`, `OAI.DimensionTen.Mod139.pow18_138_q`, `OAI.DimensionTen.Mod139.pow18_139`, `OAI.DimensionTen.Mod139.pow18_139_mul_t`, `OAI.DimensionTen.Mod139.pow18_139_q`, `OAI.DimensionTen.Mod139.pow18_16`, `OAI.DimensionTen.Mod139.pow18_16_mul_t`, `OAI.DimensionTen.Mod139.pow18_16_q`, `OAI.DimensionTen.Mod139.pow18_17`, `OAI.DimensionTen.Mod139.pow18_17_mul_t`, `OAI.DimensionTen.Mod139.pow18_17_q`, `OAI.DimensionTen.Mod139.pow18_2`, `OAI.DimensionTen.Mod139.pow18_2_mul_t`, `OAI.DimensionTen.Mod139.pow18_2_q`, `OAI.DimensionTen.Mod139.pow18_34`, `OAI.DimensionTen.Mod139.pow18_34_mul_t`, `OAI.DimensionTen.Mod139.pow18_34_q`, `OAI.DimensionTen.Mod139.pow18_4`, `OAI.DimensionTen.Mod139.pow18_4_mul_t`, `OAI.DimensionTen.Mod139.pow18_4_q`, `OAI.DimensionTen.Mod139.pow18_68`, `OAI.DimensionTen.Mod139.pow18_68_mul_t`, `OAI.DimensionTen.Mod139.pow18_68_q`, `OAI.DimensionTen.Mod139.pow18_69`, `OAI.DimensionTen.Mod139.pow18_69_mul_t`, `OAI.DimensionTen.Mod139.pow18_69_q`, `OAI.DimensionTen.Mod139.pow18_8`, `OAI.DimensionTen.Mod139.pow18_8_mul_t`, `OAI.DimensionTen.Mod139.pow18_8_q`, `OAI.DimensionTen.Mod139.pow19_138`, `OAI.DimensionTen.Mod139.pow19_138_mul_t`, `OAI.DimensionTen.Mod139.pow19_138_q`, `OAI.DimensionTen.Mod139.pow19_139`, `OAI.DimensionTen.Mod139.pow19_139_mul_t`, `OAI.DimensionTen.Mod139.pow19_139_q`, `OAI.DimensionTen.Mod139.pow19_16`, `OAI.DimensionTen.Mod139.pow19_16_mul_t`, `OAI.DimensionTen.Mod139.pow19_16_q`, `OAI.DimensionTen.Mod139.pow19_17` and 303 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, lean/OAI/InformationTheory, in whole or in part: `Quantum_DimensionTen_Kraus`, `Quantum_DimensionTen_Mod139Model`, `Quantum_DimensionTen_Mod139Powers01`, `Quantum_DimensionTen_Mod139Powers02`, `Quantum_DimensionTen_Mod139Powers03`, `Quantum_DimensionTen_Mod139Powers04`, `Quantum_DimensionTen_Mod139Powers05`, `Quantum_DimensionTen_Mod139Powers09`, `Quantum_DimensionTen_Mod139Powers10`, `Quantum_DimensionTen_Mod139Result`, `Quantum_DimensionTen_PencilModel`, `Quantum_PPTSquare_GaloisAction`, `SecretKey_Model`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ057D008`, `OAIQ057D009` and `OAIQ057D010`.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis, lean/OAI/InformationTheory at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ057_CH.Quantum_PPTSquare_GaloisAction
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

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_PencilModel
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

def symmetricPairs : Fin 10 → Fin 4 × Fin 4 :=
  ![(0,0), (0,1), (0,2), (0,3), (1,1), (1,2), (1,3), (2,2), (2,3), (3,3)]

def exteriorPairs : Fin 6 → Fin 4 × Fin 4 :=
  ![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]

def symmetricIsometry : Matrix (Fin 4 × Fin 4) (Fin 10) ℂ :=
  fun ij a =>
    let p := (symmetricPairs a).1
    let q := (symmetricPairs a).2
    if p = q then (if ij = (p,p) then 1 else 0)
    else ((if ij = (p,q) then 1 else 0) + (if ij = (q,p) then 1 else 0)) /
      (Real.sqrt 2 : ℂ)

def exteriorIsometry : Matrix (Fin 4 × Fin 4) (Fin 6) ℂ :=
  fun ij a =>
    let p := (exteriorPairs a).1
    let q := (exteriorPairs a).2
    ((if ij = (p,q) then 1 else 0) - (if ij = (q,p) then 1 else 0)) /
      (Real.sqrt 2 : ℂ)

def firstSix : Matrix (Fin 10) (Fin 6) ℂ :=
  fun i j => if i.val = j.val then 1 else 0

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Kraus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix ComplexOrder Kronecker
open Matrix
namespace DimensionTen

def krausMap {r a b : Type*} [Fintype r] [Fintype a]
    (Q : r → Matrix b a ℂ) (A : Matrix a a ℂ) : Matrix b b ℂ :=
  ∑ k, Q k * A * (Q k)ᴴ

end DimensionTen

end
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

def u0 {R : Type*} [CommRing R] (z : R) : R := (0 + z * 1)

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
def pow1_2 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * 1))

def pow1_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * 0))


def pow1_4 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * 1))))

def pow1_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * 0))))


def pow1_8 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 1))))))))

def pow1_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 0))))))))


def pow1_16 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 1))))))))))))))))

def pow1_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 0))))))))))))))))


def pow1_17 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 1)))))))))))))))))

def pow1_17_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * (0 + z * 0)))))))))))))))))


def pow1_34 {R : Type*} [CommRing R] (z : R) : R := (117 + z * (57 + z * (122 + z * (89 + z * (70 + z * (31 + z * (109 + z * (36 + z * (76 + z * (24 + z * (69 + z * (127 + z * (118 + z * (80 + z * (50 + z * (34 + z * (12 + z * (90 + z * (71 + z * 50)))))))))))))))))))

def pow1_34_q {R : Type*} [CommRing R] (z : R) : R := (122 + z * (2 + z * (75 + z * (70 + z * (8 + z * (28 + z * (125 + z * (125 + z * (111 + z * (116 + z * (135 + z * (60 + z * (19 + z * (11 + z * 1))))))))))))))

def pow1_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-93) + z * ((-109) + z * ((-169) + z * ((-237) + z * ((-233) + z * ((-201) + z * ((-295) + z * ((-383) + z * ((-456) + z * ((-612) + z * ((-734) + z * ((-657) + z * ((-651) + z * ((-667) + z * ((-522) + z * ((-591) + z * ((-655) + z * ((-515) + z * ((-613) + z * ((-639) + z * ((-505) + z * ((-520) + z * ((-485) + z * ((-409) + z * ((-405) + z * ((-436) + z * ((-367) + z * ((-256) + z * ((-230) + z * ((-179) + z * ((-71) + z * ((-26) + z * ((-11) + z * ((-1) + z * 0))))))))))))))))))))))))))))))))))


def pow1_68 {R : Type*} [CommRing R] (z : R) : R := (106 + z * (39 + z * (2 + z * (92 + z * (90 + z * (63 + z * (33 + z * (65 + z * (127 + z * (100 + z * (47 + z * (1 + z * (86 + z * (25 + z * (59 + z * (0 + z * (94 + z * (130 + z * (2 + z * 87)))))))))))))))))))

def pow1_68_q {R : Type*} [CommRing R] (z : R) : R := (87 + z * (105 + z * (64 + z * (94 + z * (97 + z * (56 + z * (82 + z * (26 + z * (55 + z * (37 + z * (68 + z * (67 + z * (43 + z * (136 + z * (56 + z * (52 + z * (85 + z * (128 + z * 137))))))))))))))))))

def pow1_68_mul_t {R : Type*} [CommRing R] (z : R) : R := (32 + z * ((-60) + z * (10 + z * ((-55) + z * ((-84) + z * ((-116) + z * ((-11) + z * ((-118) + z * ((-2) + z * ((-116) + z * ((-104) + z * ((-49) + z * (92 + z * ((-36) + z * (6 + z * ((-86) + z * ((-236) + z * ((-157) + z * ((-224) + z * ((-272) + z * ((-276) + z * ((-190) + z * ((-199) + z * ((-57) + z * ((-78) + z * ((-76) + z * ((-265) + z * ((-239) + z * ((-133) + z * ((-54) + z * ((-30) + z * ((-182) + z * ((-223) + z * ((-199) + z * ((-130) + z * ((-72) + z * ((-118) + z * ((-76) + z * 17))))))))))))))))))))))))))))))))))))))


def pow1_69 {R : Type*} [CommRing R] (z : R) : R := (39 + z * (56 + z * (6 + z * (55 + z * (61 + z * (50 + z * (57 + z * (6 + z * (90 + z * (60 + z * (83 + z * (130 + z * (101 + z * (35 + z * (122 + z * (100 + z * (55 + z * (94 + z * (13 + z * 125)))))))))))))))))))

def pow1_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-66) + z * ((-76) + z * ((-78) + z * ((-83) + z * ((-68) + z * ((-26) + z * ((-30) + z * ((-48) + z * ((-49) + z * ((-74) + z * ((-85) + z * ((-20) + z * ((-22) + z * ((-81) + z * ((-37) + z * ((-56) + z * ((-73) + z * (0 + z * ((-63) + z * ((-81) + z * 0))))))))))))))))))))


def pow1_138 {R : Type*} [CommRing R] (z : R) : R := (132 + z * (136 + z * (31 + z * (133 + z * (59 + z * (108 + z * (31 + z * (22 + z * (29 + z * (29 + z * (82 + z * (17 + z * (54 + z * (43 + z * (44 + z * (72 + z * (111 + z * (42 + z * (73 + z * 106)))))))))))))))))))

def pow1_138_q {R : Type*} [CommRing R] (z : R) : R := (45 + z * (37 + z * (95 + z * (19 + z * (111 + z * (17 + z * (61 + z * (126 + z * (39 + z * (79 + z * (131 + z * (92 + z * (119 + z * (111 + z * (114 + z * (61 + z * (37 + z * (124 + z * 57))))))))))))))))))

def pow1_138_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-24) + z * ((-37) + z * ((-119) + z * ((-139) + z * ((-178) + z * ((-179) + z * ((-181) + z * ((-249) + z * ((-256) + z * ((-235) + z * ((-379) + z * ((-353) + z * ((-331) + z * ((-442) + z * ((-428) + z * ((-354) + z * ((-376) + z * ((-442) + z * ((-341) + z * ((-299) + z * ((-277) + z * ((-270) + z * ((-116) + z * ((-104) + z * ((-61) + z * ((-22) + z * ((-135) + z * (1 + z * (0 + z * (56 + z * (16 + z * (61 + z * ((-78) + z * (22 + z * (122 + z * ((-9) + z * (14 + z * ((-30) + z * 112))))))))))))))))))))))))))))))))))))))


def pow1_139 {R : Type*} [CommRing R] (z : R) : R := (129 + z * (127 + z * (91 + z * (78 + z * (116 + z * (55 + z * (24 + z * (70 + z * (94 + z * (64 + z * (69 + z * (132 + z * (27 + z * (35 + z * (11 + z * (62 + z * (8 + z * (111 + z * (72 + z * 127)))))))))))))))))))

def pow1_139_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-81) + z * ((-93) + z * ((-95) + z * ((-101) + z * ((-83) + z * ((-32) + z * ((-36) + z * ((-59) + z * ((-60) + z * ((-91) + z * ((-104) + z * ((-24) + z * ((-26) + z * ((-99) + z * ((-44) + z * ((-68) + z * ((-88) + z * (0 + z * ((-78) + z * ((-98) + z * 0))))))))))))))))))))


abbrev u1 {R : Type*} [CommRing R] (z : R) : R := pow1_139 z


def pow2_2 {R : Type*} [CommRing R] (z : R) : R := (82 + z * (73 + z * (105 + z * (120 + z * (95 + z * (40 + z * (32 + z * (36 + z * (46 + z * (92 + z * (110 + z * (136 + z * (114 + z * (110 + z * (131 + z * (109 + z * (124 + z * (81 + z * (55 + z * 74)))))))))))))))))))

def pow2_2_q {R : Type*} [CommRing R] (z : R) : R := (24 + z * (118 + z * (53 + z * (5 + z * (103 + z * (25 + z * (75 + z * (116 + z * (18 + z * (23 + z * (85 + z * (10 + z * (49 + z * (118 + z * (51 + z * (138 + z * (9 + z * (134 + z * 5))))))))))))))))))

def pow2_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (101 + z * (125 + z * (119 + z * (131 + z * (156 + z * (152 + z * (79 + z * (28 + z * (106 + z * (123 + z * (38 + z * (227 + z * (290 + z * (72 + z * ((-138) + z * ((-43) + z * ((-223) + z * ((-240) + z * (108 + z * (197 + z * ((-37) + z * (156 + z * (44 + z * ((-118) + z * ((-53) + z * ((-169) + z * ((-32) + z * (51 + z * (47 + z * (3 + z * (47 + z * ((-203) + z * ((-67) + z * ((-167) + z * (72 + z * (22 + z * (113 + z * (126 + z * 116))))))))))))))))))))))))))))))))))))))


def pow2_4 {R : Type*} [CommRing R] (z : R) : R := (138 + z * (23 + z * (65 + z * (82 + z * (67 + z * (49 + z * (130 + z * (95 + z * (71 + z * (131 + z * (12 + z * (72 + z * (53 + z * (2 + z * (90 + z * (125 + z * (0 + z * (115 + z * (110 + z * 132)))))))))))))))))))

def pow2_4_q {R : Type*} [CommRing R] (z : R) : R := (117 + z * (97 + z * (121 + z * (91 + z * (31 + z * (10 + z * (7 + z * (57 + z * (114 + z * (49 + z * (100 + z * (109 + z * (60 + z * (11 + z * (5 + z * (85 + z * (97 + z * (127 + z * 55))))))))))))))))))

def pow2_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-41) + z * ((-90) + z * ((-120) + z * ((-122) + z * ((-79) + z * ((-15) + z * (33 + z * (6 + z * ((-91) + z * ((-145) + z * ((-197) + z * ((-104) + z * (37 + z * (182 + z * (343 + z * (307 + z * (267 + z * (220 + z * (123 + z * (171 + z * (182 + z * (212 + z * (384 + z * (389 + z * (329 + z * (363 + z * (314 + z * (385 + z * (479 + z * (405 + z * (306 + z * (254 + z * (259 + z * (162 + z * (66 + z * (13 + z * ((-50) + z * (7 + z * 39))))))))))))))))))))))))))))))))))))))


def pow2_8 {R : Type*} [CommRing R] (z : R) : R := (76 + z * (10 + z * (97 + z * (94 + z * (37 + z * (77 + z * (14 + z * (129 + z * (3 + z * (63 + z * (58 + z * (14 + z * (55 + z * (108 + z * (68 + z * (18 + z * (54 + z * (79 + z * (56 + z * 109)))))))))))))))))))

def pow2_8_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (68 + z * (31 + z * (48 + z * (118 + z * (60 + z * (18 + z * (83 + z * (5 + z * (47 + z * (33 + z * (12 + z * (13 + z * (57 + z * (61 + z * (112 + z * (41 + z * (111 + z * 49))))))))))))))))))

def pow2_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (107 + z * ((-40) + z * (14 + z * (22 + z * ((-64) + z * ((-91) + z * (109 + z * (19 + z * (57 + z * (253 + z * (25 + z * (166 + z * (226 + z * (41 + z * (133 + z * (281 + z * ((-90) + z * (88 + z * (194 + z * (101 + z * (95 + z * (378 + z * (156 + z * (244 + z * (328 + z * (214 + z * (331 + z * (134 + z * (121 + z * (137 + z * (60 + z * ((-13) + z * (130 + z * (106 + z * (158 + z * (62 + z * (167 + z * (163 + z * 125))))))))))))))))))))))))))))))))))))))


def pow2_16 {R : Type*} [CommRing R] (z : R) : R := (30 + z * (88 + z * (64 + z * (53 + z * (96 + z * (27 + z * (52 + z * (57 + z * (82 + z * (67 + z * (19 + z * (80 + z * (56 + z * (82 + z * (108 + z * (51 + z * (53 + z * (59 + z * (100 + z * 74)))))))))))))))))))

def pow2_16_q {R : Type*} [CommRing R] (z : R) : R := (109 + z * (71 + z * (45 + z * (2 + z * (21 + z * (37 + z * (108 + z * (20 + z * (21 + z * (83 + z * (43 + z * (5 + z * (26 + z * (74 + z * (129 + z * (86 + z * (81 + z * (7 + z * 66))))))))))))))))))

def pow2_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-41) + z * ((-139) + z * ((-88) + z * ((-92) + z * ((-90) + z * (41 + z * ((-88) + z * (37 + z * ((-144) + z * ((-87) + z * ((-139) + z * ((-143) + z * (52 + z * ((-146) + z * ((-98) + z * ((-269) + z * ((-235) + z * ((-151) + z * ((-259) + z * ((-130) + z * ((-27) + z * (62 + z * ((-52) + z * ((-57) + z * ((-104) + z * ((-186) + z * (136 + z * ((-103) + z * ((-132) + z * ((-50) + z * (1 + z * ((-2) + z * (3 + z * ((-48) + z * ((-78) + z * (68 + z * (91 + z * (27 + z * 85))))))))))))))))))))))))))))))))))))))


def pow2_17 {R : Type*} [CommRing R] (z : R) : R := (57 + z * (75 + z * (15 + z * (125 + z * (114 + z * (122 + z * (34 + z * (47 + z * (96 + z * (130 + z * (53 + z * (87 + z * (114 + z * (41 + z * (79 + z * (44 + z * (90 + z * (109 + z * (86 + z * 41)))))))))))))))))))

def pow2_17_q {R : Type*} [CommRing R] (z : R) : R := (80 + z * (60 + z * (42 + z * (31 + z * (60 + z * (77 + z * (49 + z * (85 + z * (108 + z * (43 + z * (9 + z * (32 + z * (114 + z * (63 + z * (88 + z * (116 + z * (13 + z * (59 + z * 85))))))))))))))))))

def pow2_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-33) + z * ((-7) + z * (3 + z * ((-9) + z * (23 + z * (18 + z * ((-8) + z * ((-64) + z * ((-69) + z * ((-87) + z * ((-115) + z * ((-5) + z * (31 + z * ((-43) + z * ((-94) + z * ((-162) + z * ((-203) + z * ((-157) + z * ((-114) + z * (11 + z * ((-19) + z * ((-88) + z * ((-58) + z * ((-42) + z * ((-124) + z * ((-63) + z * ((-13) + z * ((-128) + z * ((-81) + z * (82 + z * ((-37) + z * ((-110) + z * (20 + z * ((-49) + z * ((-28) + z * (107 + z * (48 + z * (51 + z * 67))))))))))))))))))))))))))))))))))))))


def pow2_34 {R : Type*} [CommRing R] (z : R) : R := (8 + z * (115 + z * (17 + z * (4 + z * (120 + z * (38 + z * (66 + z * (68 + z * (80 + z * (64 + z * (58 + z * (42 + z * (13 + z * (69 + z * (68 + z * (60 + z * (80 + z * (44 + z * (93 + z * 9)))))))))))))))))))

def pow2_34_q {R : Type*} [CommRing R] (z : R) : R := (105 + z * (51 + z * (39 + z * (115 + z * (68 + z * (33 + z * (47 + z * (115 + z * (25 + z * (78 + z * (45 + z * (79 + z * (48 + z * (0 + z * (117 + z * (20 + z * (50 + z * (106 + z * 13))))))))))))))))))

def pow2_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-56) + z * ((-70) + z * ((-116) + z * ((-148) + z * ((-89) + z * ((-47) + z * ((-21) + z * ((-94) + z * (67 + z * (26 + z * ((-85) + z * ((-52) + z * (160 + z * (76 + z * (82 + z * (114 + z * (24 + z * (168 + z * (82 + z * (83 + z * (249 + z * (332 + z * (243 + z * (231 + z * (136 + z * (142 + z * (203 + z * (114 + z * (236 + z * (162 + z * (31 + z * (149 + z * (48 + z * (23 + z * (156 + z * (64 + z * (10 + z * (38 + z * 12))))))))))))))))))))))))))))))))))))))


def pow2_68 {R : Type*} [CommRing R] (z : R) : R := (26 + z * (2 + z * (66 + z * (104 + z * (16 + z * (37 + z * (43 + z * (111 + z * (53 + z * (106 + z * (115 + z * (48 + z * (24 + z * (102 + z * (35 + z * (121 + z * (63 + z * (111 + z * (17 + z * 17)))))))))))))))))))

def pow2_68_q {R : Type*} [CommRing R] (z : R) : R := (97 + z * (16 + z * (19 + z * (30 + z * (87 + z * (76 + z * (41 + z * (86 + z * (112 + z * (75 + z * (105 + z * (18 + z * (80 + z * (22 + z * (16 + z * (21 + z * (65 + z * (63 + z * 81))))))))))))))))))

def pow2_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-73) + z * ((-84) + z * ((-19) + z * ((-118) + z * ((-178) + z * ((-17) + z * ((-158) + z * ((-208) + z * ((-173) + z * ((-245) + z * ((-289) + z * ((-230) + z * ((-237) + z * ((-332) + z * ((-180) + z * ((-151) + z * ((-253) + z * ((-162) + z * ((-316) + z * ((-243) + z * ((-242) + z * ((-195) + z * ((-65) + z * ((-177) + z * ((-77) + z * ((-151) + z * ((-180) + z * ((-140) + z * ((-143) + z * ((-32) + z * ((-38) + z * ((-45) + z * (23 + z * (5 + z * ((-6) + z * ((-37) + z * ((-50) + z * ((-63) + z * 0))))))))))))))))))))))))))))))))))))))


def pow2_69 {R : Type*} [CommRing R] (z : R) : R := (134 + z * (79 + z * (128 + z * (91 + z * (11 + z * (53 + z * (66 + z * (33 + z * (85 + z * (88 + z * (83 + z * (33 + z * (46 + z * (116 + z * (22 + z * (33 + z * (81 + z * (64 + z * (13 + z * 133)))))))))))))))))))

def pow2_69_q {R : Type*} [CommRing R] (z : R) : R := (77 + z * (39 + z * (38 + z * (96 + z * (41 + z * (121 + z * (4 + z * (133 + z * (12 + z * (88 + z * (124 + z * (123 + z * (138 + z * (68 + z * (62 + z * (106 + z * (88 + z * (27 + z * 74))))))))))))))))))

def pow2_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-35) + z * ((-72) + z * ((-53) + z * ((-42) + z * ((-71) + z * ((-138) + z * ((-103) + z * ((-93) + z * ((-100) + z * ((-105) + z * ((-81) + z * ((-105) + z * ((-282) + z * ((-293) + z * ((-255) + z * ((-296) + z * ((-332) + z * ((-132) + z * ((-245) + z * ((-334) + z * ((-260) + z * ((-210) + z * ((-230) + z * ((-331) + z * ((-139) + z * ((-266) + z * ((-131) + z * ((-106) + z * ((-147) + z * ((-209) + z * ((-169) + z * ((-249) + z * (36 + z * ((-45) + z * (16 + z * (28 + z * (44 + z * ((-44) + z * 15))))))))))))))))))))))))))))))))))))))


def pow2_138 {R : Type*} [CommRing R] (z : R) : R := (112 + z * (35 + z * (0 + z * (119 + z * (137 + z * (72 + z * (104 + z * (136 + z * (30 + z * (78 + z * (43 + z * (28 + z * (43 + z * (130 + z * (71 + z * (104 + z * (52 + z * (20 + z * (41 + z * 71)))))))))))))))))))

def pow2_138_q {R : Type*} [CommRing R] (z : R) : R := (23 + z * (70 + z * (59 + z * (96 + z * (38 + z * (40 + z * (5 + z * (40 + z * (55 + z * (30 + z * (6 + z * (88 + z * (44 + z * (124 + z * (39 + z * (110 + z * (37 + z * (101 + z * 36))))))))))))))))))

def pow2_138_mul_t {R : Type*} [CommRing R] (z : R) : R := (111 + z * (79 + z * (165 + z * (111 + z * ((-9) + z * (14 + z * (27 + z * (13 + z * (143 + z * (142 + z * (174 + z * (90 + z * (58 + z * (80 + z * ((-31) + z * ((-25) + z * ((-33) + z * ((-138) + z * ((-61) + z * (167 + z * ((-83) + z * ((-1) + z * (32 + z * ((-107) + z * ((-69) + z * (44 + z * ((-66) + z * ((-75) + z * ((-8) + z * (41 + z * ((-123) + z * ((-155) + z * (50 + z * ((-102) + z * ((-51) + z * (58 + z * (4 + z * ((-9) + z * 127))))))))))))))))))))))))))))))))))))))


def pow2_139 {R : Type*} [CommRing R] (z : R) : R := (8 + z * (50 + z * (33 + z * (26 + z * (46 + z * (83 + z * (9 + z * (43 + z * (113 + z * (94 + z * (70 + z * (33 + z * (113 + z * (96 + z * (46 + z * (99 + z * (98 + z * (9 + z * (19 + z * 53)))))))))))))))))))

def pow2_139_q {R : Type*} [CommRing R] (z : R) : R := (25 + z * (2 + z * (107 + z * (104 + z * (26 + z * (46 + z * (89 + z * (65 + z * (119 + z * (100 + z * (36 + z * (53 + z * (81 + z * (91 + z * (50 + z * (102 + z * (50 + z * (113 + z * 121))))))))))))))))))

def pow2_139_mul_t {R : Type*} [CommRing R] (z : R) : R := (85 + z * (111 + z * (0 + z * ((-2) + z * (120 + z * (81 + z * (29 + z * (185 + z * (140 + z * ((-28) + z * ((-43) + z * (33 + z * ((-147) + z * ((-45) + z * (118 + z * ((-18) + z * ((-159) + z * ((-85) + z * ((-265) + z * ((-201) + z * ((-143) + z * ((-317) + z * ((-150) + z * (15 + z * ((-74) + z * ((-200) + z * ((-115) + z * ((-317) + z * ((-227) + z * ((-98) + z * ((-85) + z * ((-201) + z * ((-14) + z * ((-108) + z * ((-60) + z * ((-35) + z * ((-97) + z * ((-38) + z * 64))))))))))))))))))))))))))))))))))))))


abbrev u2 {R : Type*} [CommRing R] (z : R) : R := pow2_139 z

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Powers02
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139
def pow3_2 {R : Type*} [CommRing R] (z : R) : R := (119 + z * (31 + z * (110 + z * (57 + z * (41 + z * (15 + z * (21 + z * (60 + z * (98 + z * (111 + z * (50 + z * (134 + z * (125 + z * (18 + z * (118 + z * (67 + z * (27 + z * (7 + z * (65 + z * 97)))))))))))))))))))

def pow3_2_q {R : Type*} [CommRing R] (z : R) : R := (112 + z * (89 + z * (122 + z * (111 + z * (57 + z * (55 + z * (69 + z * (5 + z * (18 + z * (69 + z * (37 + z * (104 + z * (19 + z * (135 + z * (38 + z * (10 + z * (112 + z * (109 + z * 29))))))))))))))))))

def pow3_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-85) + z * ((-160) + z * ((-250) + z * ((-351) + z * ((-391) + z * ((-356) + z * ((-331) + z * ((-317) + z * ((-271) + z * ((-280) + z * ((-315) + z * ((-365) + z * ((-337) + z * ((-352) + z * ((-322) + z * ((-366) + z * ((-353) + z * ((-199) + z * ((-359) + z * ((-443) + z * ((-190) + z * ((-155) + z * ((-122) + z * (12 + z * (61 + z * (9 + z * ((-118) + z * ((-25) + z * (108 + z * ((-112) + z * ((-100) + z * ((-12) + z * ((-160) + z * ((-78) + z * ((-13) + z * ((-106) + z * ((-113) + z * ((-13) + z * 20))))))))))))))))))))))))))))))))))))))


def pow3_4 {R : Type*} [CommRing R] (z : R) : R := (74 + z * (103 + z * (33 + z * (24 + z * (131 + z * (70 + z * (27 + z * (103 + z * (101 + z * (17 + z * (85 + z * (43 + z * (27 + z * (54 + z * (100 + z * (65 + z * (8 + z * (120 + z * (87 + z * 107)))))))))))))))))))

def pow3_4_q {R : Type*} [CommRing R] (z : R) : R := (64 + z * (77 + z * (25 + z * (51 + z * (126 + z * (50 + z * (69 + z * (131 + z * (100 + z * (17 + z * (53 + z * (23 + z * (100 + z * (122 + z * (27 + z * (22 + z * (28 + z * (44 + z * 96))))))))))))))))))

def pow3_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (53 + z * ((-62) + z * (51 + z * ((-44) + z * ((-104) + z * ((-164) + z * ((-192) + z * ((-265) + z * ((-250) + z * ((-136) + z * ((-200) + z * (23 + z * (17 + z * ((-204) + z * ((-88) + z * ((-153) + z * ((-172) + z * ((-233) + z * ((-53) + z * ((-52) + z * ((-126) + z * (16 + z * ((-85) + z * (8 + z * (18 + z * ((-24) + z * (10 + z * (47 + z * (22 + z * (76 + z * (176 + z * ((-97) + z * ((-77) + z * (90 + z * ((-2) + z * ((-14) + z * ((-71) + z * (2 + z * 67))))))))))))))))))))))))))))))))))))))


def pow3_8 {R : Type*} [CommRing R] (z : R) : R := (110 + z * (39 + z * (13 + z * (72 + z * (85 + z * (27 + z * (67 + z * (112 + z * (81 + z * (53 + z * (20 + z * (46 + z * (50 + z * (21 + z * (72 + z * (119 + z * (2 + z * (108 + z * (122 + z * 3)))))))))))))))))))

def pow3_8_q {R : Type*} [CommRing R] (z : R) : R := (112 + z * (16 + z * (112 + z * (119 + z * (16 + z * (106 + z * (108 + z * (105 + z * (134 + z * (4 + z * (130 + z * (98 + z * (95 + z * (90 + z * (62 + z * (93 + z * (75 + z * (136 + z * 51))))))))))))))))))

def pow3_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-46) + z * ((-1) + z * ((-88) + z * ((-235) + z * ((-138) + z * ((-74) + z * ((-235) + z * ((-252) + z * ((-130) + z * ((-256) + z * ((-411) + z * ((-247) + z * ((-325) + z * ((-505) + z * ((-288) + z * ((-384) + z * ((-594) + z * ((-435) + z * ((-353) + z * ((-339) + z * ((-411) + z * ((-393) + z * ((-130) + z * ((-183) + z * ((-248) + z * ((-180) + z * ((-321) + z * ((-150) + z * ((-116) + z * ((-129) + z * ((-208) + z * ((-95) + z * (21 + z * ((-23) + z * (30 + z * ((-7) + z * (76 + z * (86 + z * 82))))))))))))))))))))))))))))))))))))))


def pow3_16 {R : Type*} [CommRing R] (z : R) : R := (62 + z * (36 + z * (4 + z * (131 + z * (70 + z * (107 + z * (124 + z * (128 + z * (61 + z * (5 + z * (74 + z * (40 + z * (49 + z * (121 + z * (118 + z * (95 + z * (136 + z * (107 + z * (67 + z * 4)))))))))))))))))))

def pow3_16_q {R : Type*} [CommRing R] (z : R) : R := (112 + z * (77 + z * (81 + z * (67 + z * (102 + z * (85 + z * (61 + z * (104 + z * (6 + z * (72 + z * (12 + z * (92 + z * (47 + z * (125 + z * (99 + z * (106 + z * (125 + z * (136 + z * 9))))))))))))))))))

def pow3_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (2 + z * ((-95) + z * ((-198) + z * ((-177) + z * ((-194) + z * ((-282) + z * ((-228) + z * ((-164) + z * ((-182) + z * ((-263) + z * ((-264) + z * ((-203) + z * ((-200) + z * ((-406) + z * ((-370) + z * ((-311) + z * ((-604) + z * ((-522) + z * ((-310) + z * ((-525) + z * ((-514) + z * ((-182) + z * ((-189) + z * ((-316) + z * ((-203) + z * ((-204) + z * ((-234) + z * ((-269) + z * ((-221) + z * ((-160) + z * ((-225) + z * ((-215) + z * ((-71) + z * ((-74) + z * ((-105) + z * ((-26) + z * ((-21) + z * ((-4) + z * 0))))))))))))))))))))))))))))))))))))))


def pow3_17 {R : Type*} [CommRing R] (z : R) : R := (114 + z * (69 + z * (80 + z * (8 + z * (17 + z * (71 + z * (138 + z * (118 + z * (81 + z * (48 + z * (48 + z * (6 + z * (108 + z * (3 + z * (117 + z * (29 + z * (54 + z * (45 + z * (50 + z * 91)))))))))))))))))))

def pow3_17_q {R : Type*} [CommRing R] (z : R) : R := (46 + z * (47 + z * (38 + z * (95 + z * (41 + z * (19 + z * (82 + z * (81 + z * (29 + z * (51 + z * (99 + z * (104 + z * (110 + z * (4 + z * (67 + z * (42 + z * (31 + z * (121 + z * 73))))))))))))))))))

def pow3_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-32) + z * ((-52) + z * ((-84) + z * ((-162) + z * ((-150) + z * ((-111) + z * ((-153) + z * ((-160) + z * ((-49) + z * ((-128) + z * ((-213) + z * ((-170) + z * ((-182) + z * ((-205) + z * ((-168) + z * ((-9) + z * ((-77) + z * ((-100) + z * ((-57) + z * ((-109) + z * ((-120) + z * ((-74) + z * (44 + z * (120 + z * ((-5) + z * ((-33) + z * (57 + z * ((-59) + z * (25 + z * (130 + z * ((-49) + z * (13 + z * (78 + z * ((-49) + z * ((-11) + z * ((-44) + z * ((-115) + z * ((-42) + z * 1))))))))))))))))))))))))))))))))))))))


def pow3_34 {R : Type*} [CommRing R] (z : R) : R := (66 + z * (81 + z * (125 + z * (62 + z * (31 + z * (20 + z * (114 + z * (47 + z * (42 + z * (137 + z * (104 + z * (89 + z * (138 + z * (18 + z * (24 + z * (97 + z * (109 + z * (43 + z * (76 + z * 63)))))))))))))))))))

def pow3_34_q {R : Type*} [CommRing R] (z : R) : R := (4 + z * (16 + z * (127 + z * (129 + z * (25 + z * (110 + z * (87 + z * (67 + z * (95 + z * (70 + z * (10 + z * (94 + z * (101 + z * (11 + z * (33 + z * (65 + z * (137 + z * (111 + z * 80))))))))))))))))))

def pow3_34_mul_t {R : Type*} [CommRing R] (z : R) : R := (90 + z * (97 + z * (51 + z * ((-135) + z * ((-183) + z * ((-213) + z * ((-97) + z * (17 + z * ((-8) + z * ((-173) + z * ((-186) + z * ((-270) + z * ((-153) + z * ((-138) + z * (84 + z * ((-260) + z * ((-256) + z * ((-341) + z * ((-438) + z * ((-242) + z * ((-226) + z * ((-410) + z * ((-250) + z * ((-139) + z * ((-146) + z * ((-236) + z * ((-84) + z * ((-315) + z * ((-90) + z * ((-121) + z * ((-226) + z * ((-123) + z * ((-126) + z * ((-13) + z * ((-136) + z * ((-105) + z * ((-85) + z * ((-9) + z * 59))))))))))))))))))))))))))))))))))))))


def pow3_68 {R : Type*} [CommRing R] (z : R) : R := (33 + z * (33 + z * (31 + z * (10 + z * (73 + z * (20 + z * (6 + z * (71 + z * (58 + z * (126 + z * (4 + z * (101 + z * (6 + z * (118 + z * (102 + z * (127 + z * (69 + z * (75 + z * (42 + z * 112)))))))))))))))))))

def pow3_68_q {R : Type*} [CommRing R] (z : R) : R := (65 + z * (71 + z * (123 + z * (131 + z * (18 + z * (95 + z * (67 + z * (21 + z * (122 + z * (29 + z * (57 + z * (76 + z * (73 + z * (40 + z * (132 + z * (121 + z * (121 + z * (137 + z * 77))))))))))))))))))

def pow3_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-18) + z * ((-34) + z * ((-48) + z * ((-128) + z * ((-144) + z * ((-231) + z * ((-200) + z * ((-137) + z * ((-109) + z * ((-127) + z * ((-122) + z * ((-49) + z * (17 + z * ((-43) + z * ((-128) + z * ((-254) + z * ((-283) + z * ((-234) + z * ((-208) + z * ((-228) + z * ((-163) + z * ((-143) + z * ((-43) + z * ((-137) + z * ((-157) + z * ((-12) + z * ((-101) + z * ((-50) + z * (79 + z * ((-102) + z * ((-161) + z * ((-93) + z * ((-167) + z * ((-179) + z * ((-45) + z * ((-67) + z * ((-103) + z * ((-3) + z * 28))))))))))))))))))))))))))))))))))))))


def pow3_69 {R : Type*} [CommRing R] (z : R) : R := (128 + z * (79 + z * (119 + z * (7 + z * (82 + z * (124 + z * (5 + z * (50 + z * (71 + z * (132 + z * (29 + z * (49 + z * (77 + z * (67 + z * (37 + z * (114 + z * (53 + z * (90 + z * (12 + z * 79)))))))))))))))))))

def pow3_69_q {R : Type*} [CommRing R] (z : R) : R := (135 + z * (132 + z * (23 + z * (63 + z * (133 + z * (99 + z * (82 + z * (80 + z * (108 + z * (77 + z * (104 + z * (121 + z * (99 + z * (19 + z * (83 + z * (26 + z * (76 + z * (11 + z * 98))))))))))))))))))

def pow3_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-101) + z * ((-205) + z * ((-234) + z * ((-289) + z * ((-376) + z * ((-349) + z * ((-374) + z * ((-466) + z * ((-497) + z * ((-490) + z * ((-594) + z * ((-612) + z * ((-508) + z * ((-626) + z * ((-643) + z * ((-549) + z * ((-472) + z * ((-429) + z * ((-505) + z * ((-555) + z * ((-440) + z * ((-279) + z * ((-233) + z * ((-122) + z * ((-129) + z * ((-126) + z * ((-73) + z * ((-23) + z * (17 + z * (28 + z * (8 + z * (36 + z * (70 + z * (13 + z * (10 + z * (40 + z * ((-41) + z * ((-59) + z * 42))))))))))))))))))))))))))))))))))))))


def pow3_138 {R : Type*} [CommRing R] (z : R) : R := (44 + z * (32 + z * (40 + z * (137 + z * (110 + z * (20 + z * (63 + z * (103 + z * (69 + z * (50 + z * (129 + z * (4 + z * (50 + z * (83 + z * (73 + z * (118 + z * (43 + z * (9 + z * (123 + z * 115)))))))))))))))))))

def pow3_138_q {R : Type*} [CommRing R] (z : R) : R := (10 + z * (137 + z * (100 + z * (38 + z * (17 + z * (123 + z * (21 + z * (10 + z * (85 + z * (99 + z * (61 + z * (34 + z * (59 + z * (55 + z * (122 + z * (87 + z * (65 + z * (74 + z * 125))))))))))))))))))

def pow3_138_mul_t {R : Type*} [CommRing R] (z : R) : R := (110 + z * (33 + z * (59 + z * ((-102) + z * ((-14) + z * ((-14) + z * ((-8) + z * (52 + z * ((-93) + z * (122 + z * ((-37) + z * ((-134) + z * ((-108) + z * (97 + z * ((-64) + z * ((-175) + z * ((-93) + z * (4 + z * ((-314) + z * ((-124) + z * ((-194) + z * ((-160) + z * ((-104) + z * ((-167) + z * ((-79) + z * ((-156) + z * ((-51) + z * ((-229) + z * ((-111) + z * ((-96) + z * ((-82) + z * ((-123) + z * ((-44) + z * ((-188) + z * ((-36) + z * ((-39) + z * ((-57) + z * ((-102) + z * 44))))))))))))))))))))))))))))))))))))))


def pow3_139 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (84 + z * (22 + z * (94 + z * (42 + z * (86 + z * (71 + z * (70 + z * (0 + z * (20 + z * (72 + z * (135 + z * (38 + z * (47 + z * (74 + z * (60 + z * (0 + z * (25 + z * (35 + z * 29)))))))))))))))))))

def pow3_139_q {R : Type*} [CommRing R] (z : R) : R := (92 + z * (105 + z * (85 + z * (98 + z * (8 + z * (86 + z * (19 + z * (37 + z * (33 + z * (113 + z * (22 + z * (7 + z * (44 + z * (108 + z * (40 + z * (133 + z * (87 + z * (133 + z * 118))))))))))))))))))

def pow3_139_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-67) + z * ((-143) + z * ((-215) + z * ((-293) + z * ((-255) + z * ((-234) + z * ((-223) + z * ((-181) + z * ((-105) + z * ((-241) + z * ((-287) + z * ((-135) + z * ((-91) + z * ((-194) + z * ((-149) + z * ((-165) + z * ((-255) + z * ((-290) + z * ((-379) + z * ((-307) + z * ((-190) + z * ((-264) + z * ((-60) + z * (57 + z * ((-116) + z * ((-146) + z * ((-35) + z * ((-68) + z * ((-120) + z * ((-11) + z * ((-50) + z * ((-122) + z * ((-130) + z * ((-143) + z * ((-65) + z * ((-72) + z * ((-182) + z * ((-47) + z * 43))))))))))))))))))))))))))))))))))))))


abbrev u3 {R : Type*} [CommRing R] (z : R) : R := pow3_139 z


def pow4_2 {R : Type*} [CommRing R] (z : R) : R := (101 + z * (106 + z * (23 + z * (122 + z * (23 + z * (102 + z * (102 + z * (59 + z * (21 + z * (15 + z * (113 + z * (31 + z * (51 + z * (64 + z * (1 + z * (115 + z * (122 + z * (49 + z * (73 + z * 104)))))))))))))))))))

def pow4_2_q {R : Type*} [CommRing R] (z : R) : R := (84 + z * (10 + z * (21 + z * (52 + z * (57 + z * (49 + z * (53 + z * (71 + z * (16 + z * (47 + z * (70 + z * (44 + z * (99 + z * (36 + z * (101 + z * (109 + z * (118 + z * (22 + z * 7))))))))))))))))))

def pow4_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-64) + z * ((-76) + z * ((-48) + z * ((-114) + z * ((-63) + z * ((-101) + z * ((-47) + z * ((-121) + z * ((-53) + z * ((-155) + z * ((-164) + z * ((-115) + z * ((-82) + z * ((-256) + z * ((-181) + z * ((-264) + z * ((-289) + z * ((-250) + z * ((-295) + z * ((-421) + z * ((-223) + z * ((-147) + z * ((-219) + z * ((-304) + z * ((-211) + z * ((-255) + z * ((-217) + z * ((-221) + z * ((-212) + z * ((-179) + z * ((-221) + z * ((-234) + z * ((-145) + z * ((-135) + z * ((-164) + z * ((-113) + z * ((-7) + z * (8 + z * 6))))))))))))))))))))))))))))))))))))))


def pow4_4 {R : Type*} [CommRing R] (z : R) : R := (17 + z * (89 + z * (25 + z * (26 + z * (60 + z * (12 + z * (115 + z * (2 + z * (74 + z * (45 + z * (41 + z * (128 + z * (97 + z * (6 + z * (43 + z * (132 + z * (17 + z * (80 + z * (127 + z * 37)))))))))))))))))))

def pow4_4_q {R : Type*} [CommRing R] (z : R) : R := (3 + z * (50 + z * (92 + z * (116 + z * (137 + z * (10 + z * (44 + z * (4 + z * (23 + z * (117 + z * (7 + z * (65 + z * (101 + z * (63 + z * (54 + z * (83 + z * (100 + z * (25 + z * 113))))))))))))))))))

def pow4_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (71 + z * (113 + z * ((-2) + z * ((-4) + z * ((-115) + z * ((-136) + z * (54 + z * ((-3) + z * (63 + z * ((-39) + z * (27 + z * ((-44) + z * ((-216) + z * ((-96) + z * ((-278) + z * ((-92) + z * (10 + z * ((-179) + z * ((-113) + z * ((-105) + z * ((-42) + z * ((-53) + z * ((-83) + z * ((-20) + z * ((-60) + z * ((-48) + z * (17 + z * ((-200) + z * ((-120) + z * (50 + z * ((-83) + z * ((-43) + z * (40 + z * (4 + z * (73 + z * (123 + z * (5 + z * (5 + z * 77))))))))))))))))))))))))))))))))))))))


def pow4_8 {R : Type*} [CommRing R] (z : R) : R := (103 + z * (8 + z * (46 + z * (20 + z * (134 + z * (19 + z * (65 + z * (101 + z * (28 + z * (83 + z * (93 + z * (38 + z * (47 + z * (1 + z * (113 + z * (45 + z * (109 + z * (135 + z * (100 + z * 113)))))))))))))))))))

def pow4_8_q {R : Type*} [CommRing R] (z : R) : R := (109 + z * (8 + z * (42 + z * (30 + z * (15 + z * (46 + z * (24 + z * (1 + z * (73 + z * (88 + z * (93 + z * (46 + z * (42 + z * (133 + z * (25 + z * (94 + z * (67 + z * (132 + z * 118))))))))))))))))))

def pow4_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-81) + z * ((-80) + z * ((-74) + z * ((-132) + z * ((-117) + z * ((-65) + z * ((-104) + z * ((-3) + z * ((-130) + z * ((-167) + z * ((-211) + z * ((-233) + z * ((-56) + z * ((-311) + z * ((-214) + z * ((-257) + z * ((-226) + z * ((-254) + z * ((-394) + z * ((-324) + z * ((-248) + z * ((-166) + z * ((-188) + z * ((-25) + z * ((-129) + z * ((-215) + z * ((-74) + z * ((-156) + z * ((-235) + z * (43 + z * (53 + z * ((-279) + z * ((-95) + z * (5 + z * ((-87) + z * ((-4) + z * ((-50) + z * ((-42) + z * 9))))))))))))))))))))))))))))))))))))))


def pow4_16 {R : Type*} [CommRing R] (z : R) : R := (95 + z * (119 + z * (38 + z * (78 + z * (26 + z * (13 + z * (107 + z * (113 + z * (43 + z * (99 + z * (73 + z * (57 + z * (108 + z * (22 + z * (122 + z * (0 + z * (67 + z * (92 + z * (46 + z * 65)))))))))))))))))))

def pow4_16_q {R : Type*} [CommRing R] (z : R) : R := (26 + z * (126 + z * (72 + z * (126 + z * (55 + z * (20 + z * (118 + z * (89 + z * (103 + z * (55 + z * (70 + z * (28 + z * (9 + z * (65 + z * (75 + z * (42 + z * (46 + z * (12 + z * 120))))))))))))))))))

def pow4_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (56 + z * ((-107) + z * ((-120) + z * ((-262) + z * ((-141) + z * ((-295) + z * ((-190) + z * ((-212) + z * ((-241) + z * ((-285) + z * ((-317) + z * ((-292) + z * ((-279) + z * ((-251) + z * ((-106) + z * ((-323) + z * ((-233) + z * ((-260) + z * ((-64) + z * ((-180) + z * ((-151) + z * (28 + z * ((-124) + z * (189 + z * (104 + z * (87 + z * (163 + z * (40 + z * (155 + z * (94 + z * (141 + z * (130 + z * (126 + z * (273 + z * (188 + z * (320 + z * (192 + z * (52 + z * 91))))))))))))))))))))))))))))))))))))))


def pow4_17 {R : Type*} [CommRing R] (z : R) : R := (66 + z * (13 + z * (71 + z * (103 + z * (119 + z * (13 + z * (39 + z * (24 + z * (72 + z * (74 + z * (26 + z * (89 + z * (93 + z * (16 + z * (30 + z * (126 + z * (56 + z * (119 + z * (134 + z * 35)))))))))))))))))))

def pow4_17_q {R : Type*} [CommRing R] (z : R) : R := (82 + z * (116 + z * (93 + z * (101 + z * (124 + z * (73 + z * (24 + z * (120 + z * (69 + z * (93 + z * (46 + z * (21 + z * (55 + z * (57 + z * (76 + z * (76 + z * (102 + z * (19 + z * 78))))))))))))))))))

def pow4_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-59) + z * ((-98) + z * ((-158) + z * ((-232) + z * ((-278) + z * ((-310) + z * ((-224) + z * ((-244) + z * ((-288) + z * ((-366) + z * ((-359) + z * ((-299) + z * ((-189) + z * ((-236) + z * ((-289) + z * ((-258) + z * ((-490) + z * ((-384) + z * ((-401) + z * ((-403) + z * ((-323) + z * ((-204) + z * ((-289) + z * ((-260) + z * ((-127) + z * ((-177) + z * ((-229) + z * ((-141) + z * ((-146) + z * ((-76) + z * ((-66) + z * ((-141) + z * ((-117) + z * ((-100) + z * ((-149) + z * ((-63) + z * ((-33) + z * ((-46) + z * 13))))))))))))))))))))))))))))))))))))))


def pow4_34 {R : Type*} [CommRing R] (z : R) : R := (61 + z * (31 + z * (84 + z * (107 + z * (77 + z * (31 + z * (104 + z * (130 + z * (137 + z * (18 + z * (57 + z * (6 + z * (30 + z * (128 + z * (60 + z * (120 + z * (74 + z * (66 + z * (132 + z * 48)))))))))))))))))))

def pow4_34_q {R : Type*} [CommRing R] (z : R) : R := (74 + z * (32 + z * (121 + z * (106 + z * (87 + z * (104 + z * (60 + z * (48 + z * (42 + z * (27 + z * (93 + z * (88 + z * (40 + z * (37 + z * (9 + z * (106 + z * (119 + z * (59 + z * 113))))))))))))))))))

def pow4_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-25) + z * ((-77) + z * ((-118) + z * ((-175) + z * ((-188) + z * ((-273) + z * ((-209) + z * ((-218) + z * ((-195) + z * ((-262) + z * ((-297) + z * ((-243) + z * ((-246) + z * ((-340) + z * ((-242) + z * ((-186) + z * ((-347) + z * ((-266) + z * ((-328) + z * ((-253) + z * ((-182) + z * ((-95) + z * ((-92) + z * ((-118) + z * ((-161) + z * ((-204) + z * ((-15) + z * (82 + z * ((-56) + z * (29 + z * (71 + z * ((-129) + z * (79 + z * (146 + z * ((-6) + z * (104 + z * (51 + z * ((-37) + z * 8))))))))))))))))))))))))))))))))))))))


def pow4_68 {R : Type*} [CommRing R] (z : R) : R := (88 + z * (115 + z * (58 + z * (106 + z * (121 + z * (67 + z * (88 + z * (41 + z * (65 + z * (131 + z * (102 + z * (92 + z * (110 + z * (137 + z * (7 + z * (11 + z * (103 + z * (0 + z * (50 + z * 3)))))))))))))))))))

def pow4_68_q {R : Type*} [CommRing R] (z : R) : R := (118 + z * (58 + z * (130 + z * (56 + z * (6 + z * (126 + z * (51 + z * (111 + z * (53 + z * (44 + z * (52 + z * (2 + z * (7 + z * (136 + z * (31 + z * (59 + z * (96 + z * (69 + z * 80))))))))))))))))))

def pow4_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-63) + z * ((-121) + z * ((-175) + z * ((-190) + z * ((-153) + z * ((-165) + z * ((-88) + z * ((-100) + z * ((-74) + z * ((-126) + z * ((-35) + z * ((-59) + z * ((-66) + z * ((-66) + z * ((-22) + z * ((-80) + z * ((-99) + z * ((-104) + z * ((-126) + z * ((-31) + z * (75 + z * (226 + z * (224 + z * (121 + z * (104 + z * (157 + z * (47 + z * (6 + z * (48 + z * ((-13) + z * (155 + z * (128 + z * (50 + z * (158 + z * (63 + z * (37 + z * (48 + z * (17 + z * 16))))))))))))))))))))))))))))))))))))))


def pow4_69 {R : Type*} [CommRing R] (z : R) : R := (48 + z * (105 + z * (48 + z * (126 + z * (69 + z * (40 + z * (72 + z * (26 + z * (104 + z * (63 + z * (98 + z * (123 + z * (66 + z * (35 + z * (110 + z * (60 + z * (67 + z * (114 + z * (101 + z * 41)))))))))))))))))))

def pow4_69_q {R : Type*} [CommRing R] (z : R) : R := (13 + z * (28 + z * (74 + z * (36 + z * (51 + z * (73 + z * (92 + z * (108 + z * (85 + z * (120 + z * (85 + z * (110 + z * (111 + z * (69 + z * (1 + z * (2 + z * (11 + z * (10 + z * 87))))))))))))))))))

def pow4_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-7) + z * (24 + z * ((-7) + z * ((-14) + z * (8 + z * ((-8) + z * ((-17) + z * ((-26) + z * ((-135) + z * ((-202) + z * ((-193) + z * ((-182) + z * ((-215) + z * ((-203) + z * ((-75) + z * ((-87) + z * ((-67) + z * ((-62) + z * ((-165) + z * ((-127) + z * ((-253) + z * ((-276) + z * ((-224) + z * ((-54) + z * ((-127) + z * ((-289) + z * ((-223) + z * ((-149) + z * ((-212) + z * ((-93) + z * ((-73) + z * ((-127) + z * ((-57) + z * ((-21) + z * ((-53) + z * (13 + z * ((-60) + z * ((-69) + z * 0))))))))))))))))))))))))))))))))))))))


def pow4_138 {R : Type*} [CommRing R] (z : R) : R := (76 + z * (85 + z * (70 + z * (53 + z * (93 + z * (5 + z * (103 + z * (109 + z * (21 + z * (94 + z * (122 + z * (115 + z * (134 + z * (31 + z * (31 + z * (58 + z * (14 + z * (91 + z * (116 + z * 116)))))))))))))))))))

def pow4_138_q {R : Type*} [CommRing R] (z : R) : R := (98 + z * (119 + z * (72 + z * (25 + z * (23 + z * (25 + z * (30 + z * (97 + z * (89 + z * (14 + z * (133 + z * (81 + z * (7 + z * (64 + z * (21 + z * (128 + z * (115 + z * (85 + z * 13))))))))))))))))))

def pow4_138_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-58) + z * ((-104) + z * ((-135) + z * ((-123) + z * ((-40) + z * ((-34) + z * (56 + z * ((-2) + z * ((-107) + z * ((-42) + z * ((-212) + z * ((-64) + z * (80 + z * ((-1) + z * (59 + z * (1 + z * ((-132) + z * ((-72) + z * (39 + z * (39 + z * (52 + z * (179 + z * (282 + z * (19 + z * (52 + z * (89 + z * ((-23) + z * (182 + z * (216 + z * (40 + z * (47 + z * (46 + z * (81 + z * (69 + z * (13 + z * (36 + z * (52 + z * (47 + z * 12))))))))))))))))))))))))))))))))))))))


def pow4_139 {R : Type*} [CommRing R] (z : R) : R := (71 + z * (55 + z * (107 + z * (127 + z * (2 + z * (120 + z * (43 + z * (97 + z * (94 + z * (116 + z * (134 + z * (9 + z * (5 + z * (24 + z * (117 + z * (116 + z * (116 + z * (101 + z * (14 + z * 126)))))))))))))))))))

def pow4_139_q {R : Type*} [CommRing R] (z : R) : R := (134 + z * (135 + z * (28 + z * (123 + z * (133 + z * (30 + z * (5 + z * (136 + z * (116 + z * (31 + z * (28 + z * (106 + z * (49 + z * (79 + z * (88 + z * (29 + z * (55 + z * (87 + z * 28))))))))))))))))))

def pow4_139_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-99) + z * ((-171) + z * ((-195) + z * ((-258) + z * ((-340) + z * ((-239) + z * ((-206) + z * ((-216) + z * ((-316) + z * ((-330) + z * ((-374) + z * ((-309) + z * ((-172) + z * ((-260) + z * ((-335) + z * ((-213) + z * ((-396) + z * ((-399) + z * ((-292) + z * ((-398) + z * ((-283) + z * ((-129) + z * ((-108) + z * ((-165) + z * ((-30) + z * ((-17) + z * ((-248) + z * ((-266) + z * (24 + z * (8 + z * ((-66) + z * ((-59) + z * ((-86) + z * ((-58) + z * ((-9) + z * ((-68) + z * ((-32) + z * (27 + z * 24))))))))))))))))))))))))))))))))))))))


abbrev u4 {R : Type*} [CommRing R] (z : R) : R := pow4_139 z

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Powers03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139
def pow5_2 {R : Type*} [CommRing R] (z : R) : R := (21 + z * (19 + z * (79 + z * (96 + z * (15 + z * (31 + z * (8 + z * (97 + z * (88 + z * (125 + z * (47 + z * (16 + z * (133 + z * (122 + z * (51 + z * (76 + z * (115 + z * (47 + z * (128 + z * 33)))))))))))))))))))

def pow5_2_q {R : Type*} [CommRing R] (z : R) : R := (114 + z * (45 + z * (137 + z * (1 + z * (18 + z * (82 + z * (129 + z * (74 + z * (40 + z * (23 + z * (61 + z * (132 + z * (21 + z * (81 + z * (5 + z * (75 + z * (113 + z * (105 + z * 30))))))))))))))))))

def pow5_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-50) + z * ((-78) + z * ((-115) + z * ((-56) + z * ((-85) + z * (41 + z * ((-89) + z * ((-60) + z * (18 + z * ((-87) + z * (123 + z * (8 + z * (78 + z * ((-82) + z * ((-120) + z * ((-71) + z * (18 + z * (235 + z * (2 + z * (161 + z * ((-51) + z * ((-16) + z * (366 + z * (150 + z * (355 + z * (95 + z * (61 + z * (64 + z * (109 + z * (94 + z * (2 + z * (91 + z * (80 + z * (237 + z * (130 + z * (49 + z * (65 + z * ((-3) + z * 114))))))))))))))))))))))))))))))))))))))


def pow5_4 {R : Type*} [CommRing R] (z : R) : R := (60 + z * (120 + z * (84 + z * (105 + z * (14 + z * (1 + z * (52 + z * (128 + z * (46 + z * (132 + z * (94 + z * (52 + z * (23 + z * (57 + z * (17 + z * (89 + z * (72 + z * (98 + z * (87 + z * 101)))))))))))))))))))

def pow5_4_q {R : Type*} [CommRing R] (z : R) : R := (91 + z * (94 + z * (51 + z * (118 + z * (96 + z * (59 + z * (70 + z * (57 + z * (22 + z * (29 + z * (22 + z * (116 + z * (87 + z * (79 + z * (60 + z * (8 + z * (82 + z * (133 + z * 116))))))))))))))))))

def pow5_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-66) + z * ((-146) + z * ((-177) + z * ((-255) + z * ((-307) + z * ((-262) + z * ((-309) + z * ((-353) + z * ((-311) + z * ((-245) + z * ((-195) + z * ((-210) + z * ((-221) + z * ((-466) + z * ((-351) + z * ((-157) + z * ((-206) + z * ((-235) + z * ((-258) + z * ((-333) + z * ((-201) + z * ((-32) + z * ((-103) + z * ((-3) + z * (42 + z * (221 + z * (45 + z * (32 + z * (167 + z * (51 + z * (48 + z * (86 + z * ((-21) + z * ((-5) + z * (99 + z * ((-32) + z * ((-68) + z * ((-47) + z * 7))))))))))))))))))))))))))))))))))))))


def pow5_8 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (127 + z * (81 + z * (36 + z * (126 + z * (84 + z * (137 + z * (20 + z * (56 + z * (79 + z * (51 + z * (54 + z * (5 + z * (123 + z * (35 + z * (55 + z * (50 + z * (128 + z * (130 + z * 113)))))))))))))))))))

def pow5_8_q {R : Type*} [CommRing R] (z : R) : R := (54 + z * (7 + z * (107 + z * (127 + z * (10 + z * (127 + z * (118 + z * (135 + z * (6 + z * (75 + z * (28 + z * (135 + z * (123 + z * (36 + z * (118 + z * (55 + z * (0 + z * (98 + z * 54))))))))))))))))))

def pow5_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * (50 + z * (40 + z * ((-12) + z * ((-21) + z * ((-191) + z * ((-293) + z * ((-271) + z * ((-141) + z * ((-125) + z * (24 + z * ((-110) + z * ((-245) + z * ((-320) + z * ((-357) + z * ((-505) + z * ((-199) + z * ((-84) + z * ((-108) + z * ((-53) + z * ((-61) + z * ((-406) + z * ((-180) + z * ((-142) + z * ((-135) + z * ((-45) + z * (143 + z * ((-72) + z * (91 + z * (25 + z * ((-194) + z * ((-57) + z * (61 + z * ((-28) + z * (192 + z * (155 + z * (67 + z * (76 + z * 73))))))))))))))))))))))))))))))))))))))


def pow5_16 {R : Type*} [CommRing R] (z : R) : R := (26 + z * (14 + z * (131 + z * (118 + z * (15 + z * (17 + z * (57 + z * (56 + z * (74 + z * (43 + z * (41 + z * (26 + z * (138 + z * (119 + z * (30 + z * (41 + z * (0 + z * (95 + z * (36 + z * 12)))))))))))))))))))

def pow5_16_q {R : Type*} [CommRing R] (z : R) : R := (80 + z * (110 + z * (16 + z * (0 + z * (137 + z * (109 + z * (55 + z * (119 + z * (101 + z * (54 + z * (103 + z * (106 + z * (91 + z * (15 + z * (77 + z * (23 + z * (19 + z * (120 + z * 120))))))))))))))))))

def pow5_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-59) + z * ((-126) + z * ((-48) + z * ((-34) + z * ((-145) + z * ((-38) + z * (5 + z * ((-36) + z * ((-187) + z * ((-189) + z * ((-104) + z * ((-250) + z * ((-177) + z * ((-338) + z * ((-283) + z * ((-184) + z * ((-265) + z * ((-222) + z * ((-192) + z * (5 + z * ((-220) + z * ((-22) + z * (97 + z * (90 + z * (12 + z * ((-76) + z * ((-129) + z * ((-151) + z * (19 + z * ((-9) + z * ((-23) + z * (53 + z * (171 + z * ((-13) + z * (165 + z * (215 + z * (131 + z * (100 + z * 91))))))))))))))))))))))))))))))))))))))


def pow5_17 {R : Type*} [CommRing R] (z : R) : R := (87 + z * (46 + z * (4 + z * (69 + z * (118 + z * (111 + z * (134 + z * (95 + z * (95 + z * (11 + z * (60 + z * (3 + z * (24 + z * (29 + z * (61 + z * (109 + z * (99 + z * (9 + z * (13 + z * 114)))))))))))))))))))

def pow5_17_q {R : Type*} [CommRing R] (z : R) : R := (75 + z * (52 + z * (19 + z * (43 + z * (137 + z * (18 + z * (29 + z * (107 + z * (34 + z * (1 + z * (100 + z * (47 + z * (5 + z * (93 + z * (20 + z * (64 + z * (55 + z * (69 + z * 122))))))))))))))))))

def pow5_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-44) + z * ((-88) + z * ((-35) + z * ((-21) + z * ((-99) + z * ((-7) + z * ((-82) + z * ((-137) + z * ((-72) + z * ((-10) + z * ((-63) + z * ((-39) + z * (90 + z * ((-87) + z * ((-160) + z * (42 + z * ((-46) + z * ((-14) + z * (6 + z * ((-117) + z * ((-143) + z * (61 + z * (113 + z * ((-146) + z * (1 + z * ((-72) + z * ((-129) + z * (142 + z * (5 + z * ((-23) + z * ((-21) + z * ((-25) + z * (11 + z * ((-51) + z * ((-55) + z * ((-56) + z * ((-55) + z * ((-79) + z * 10))))))))))))))))))))))))))))))))))))))


def pow5_34 {R : Type*} [CommRing R] (z : R) : R := (6 + z * (129 + z * (8 + z * (7 + z * (35 + z * (107 + z * (78 + z * (8 + z * (69 + z * (9 + z * (70 + z * (11 + z * (7 + z * (14 + z * (5 + z * (5 + z * (77 + z * (132 + z * 2))))))))))))))))))

def pow5_34_q {R : Type*} [CommRing R] (z : R) : R := (76 + z * (37 + z * (19 + z * (111 + z * (0 + z * (76 + z * (93 + z * (39 + z * (20 + z * (60 + z * (57 + z * (53 + z * (75 + z * (61 + z * (99 + z * (107 + z * (135 + z * (109 + z * 69))))))))))))))))))

def pow5_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-3) + z * ((-38) + z * ((-95) + z * ((-117) + z * ((-16) + z * ((-7) + z * ((-13) + z * (4 + z * (91 + z * (23 + z * (73 + z * (134 + z * (35 + z * ((-102) + z * ((-83) + z * ((-215) + z * ((-353) + z * ((-396) + z * ((-451) + z * ((-288) + z * ((-62) + z * ((-186) + z * ((-71) + z * (4 + z * ((-217) + z * ((-278) + z * ((-241) + z * ((-262) + z * ((-329) + z * ((-180) + z * ((-245) + z * ((-192) + z * ((-197) + z * ((-172) + z * ((-58) + z * ((-41) + z * ((-136) + z * ((-43) + z * 93))))))))))))))))))))))))))))))))))))))


def pow5_68 {R : Type*} [CommRing R] (z : R) : R := (56 + z * (130 + z * (71 + z * (136 + z * (71 + z * (128 + z * (84 + z * (26 + z * (91 + z * (82 + z * (94 + z * (31 + z * (74 + z * (48 + z * (116 + z * (26 + z * (129 + z * (103 + z * (128 + z * 96)))))))))))))))))))

def pow5_68_q {R : Type*} [CommRing R] (z : R) : R := (66 + z * (97 + z * (76 + z * (21 + z * (105 + z * (21 + z * (22 + z * (42 + z * (80 + z * (104 + z * (112 + z * (43 + z * (23 + z * (75 + z * (125 + z * (16 + z * 4))))))))))))))))

def pow5_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-50) + z * ((-121) + z * ((-82) + z * ((-218) + z * ((-294) + z * ((-221) + z * ((-52) + z * ((-118) + z * ((-294) + z * ((-225) + z * ((-397) + z * ((-329) + z * ((-418) + z * ((-437) + z * ((-512) + z * ((-461) + z * ((-478) + z * ((-492) + z * ((-248) + z * ((-516) + z * ((-479) + z * ((-223) + z * ((-171) + z * ((-373) + z * ((-315) + z * ((-166) + z * ((-237) + z * ((-207) + z * ((-282) + z * ((-259) + z * ((-141) + z * ((-77) + z * ((-112) + z * (19 + z * (109 + z * (0 + z * 0))))))))))))))))))))))))))))))))))))


def pow5_69 {R : Type*} [CommRing R] (z : R) : R := (130 + z * (76 + z * (113 + z * (29 + z * (115 + z * (52 + z * (99 + z * (43 + z * (86 + z * (62 + z * (107 + z * (82 + z * (8 + z * (95 + z * (9 + z * (54 + z * (7 + z * (21 + z * (94 + z * 35)))))))))))))))))))

def pow5_69_q {R : Type*} [CommRing R] (z : R) : R := (124 + z * (126 + z * (74 + z * (14 + z * (95 + z * (113 + z * (47 + z * (6 + z * (138 + z * (84 + z * (95 + z * (138 + z * (80 + z * (81 + z * (20 + z * (20 + z * (14 + z * (130 + z * 3))))))))))))))))))

def pow5_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-66) + z * ((-116) + z * ((-148) + z * ((-58) + z * ((-104) + z * ((-75) + z * (30 + z * ((-31) + z * (4 + z * ((-111) + z * ((-45) + z * ((-86) + z * ((-155) + z * ((-198) + z * ((-252) + z * ((-81) + z * (25 + z * (79 + z * (23 + z * (189 + z * (113 + z * (117 + z * (305 + z * (121 + z * (161 + z * (219 + z * (117 + z * (42 + z * (196 + z * (104 + z * ((-18) + z * (181 + z * (206 + z * (331 + z * (267 + z * (192 + z * (54 + z * (122 + z * 87))))))))))))))))))))))))))))))))))))))


def pow5_138 {R : Type*} [CommRing R] (z : R) : R := (112 + z * (126 + z * (36 + z * (68 + z * (21 + z * (39 + z * (115 + z * (8 + z * (38 + z * (10 + z * (118 + z * (102 + z * (81 + z * (74 + z * (22 + z * (70 + z * (115 + z * (1 + z * (24 + z * 53)))))))))))))))))))

def pow5_138_q {R : Type*} [CommRing R] (z : R) : R := (5 + z * (21 + z * (136 + z * (60 + z * (38 + z * (84 + z * (120 + z * (102 + z * (70 + z * (67 + z * (43 + z * (53 + z * (87 + z * (11 + z * (113 + z * (99 + z * (43 + z * (39 + z * 113))))))))))))))))))

def pow5_138_mul_t {R : Type*} [CommRing R] (z : R) : R := (117 + z * (121 + z * (127 + z * ((-11) + z * (111 + z * ((-28) + z * (64 + z * ((-71) + z * (46 + z * ((-100) + z * (92 + z * (9 + z * ((-51) + z * (65 + z * ((-76) + z * ((-162) + z * ((-326) + z * ((-189) + z * ((-315) + z * ((-115) + z * ((-277) + z * ((-361) + z * ((-306) + z * ((-169) + z * ((-282) + z * ((-374) + z * ((-154) + z * ((-307) + z * ((-167) + z * ((-93) + z * ((-250) + z * ((-180) + z * ((-125) + z * ((-202) + z * ((-178) + z * ((-37) + z * ((-45) + z * ((-57) + z * 8))))))))))))))))))))))))))))))))))))))


def pow5_139 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (71 + z * (57 + z * (72 + z * (120 + z * (14 + z * (1 + z * (125 + z * (25 + z * (98 + z * (113 + z * (114 + z * (40 + z * (75 + z * (61 + z * (99 + z * (133 + z * (54 + z * (114 + z * 114)))))))))))))))))))

def pow5_139_q {R : Type*} [CommRing R] (z : R) : R := (85 + z * (104 + z * (15 + z * (23 + z * (69 + z * (73 + z * (74 + z * (121 + z * (46 + z * (48 + z * (8 + z * (138 + z * (29 + z * (34 + z * (66 + z * (78 + z * (95 + z * (79 + z * 6))))))))))))))))))

def pow5_139_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-7) + z * ((-45) + z * ((-25) + z * (43 + z * ((-70) + z * ((-46) + z * (20 + z * ((-146) + z * ((-68) + z * ((-107) + z * ((-75) + z * ((-54) + z * ((-82) + z * ((-41) + z * ((-178) + z * ((-7) + z * ((-36) + z * ((-116) + z * ((-36) + z * ((-76) + z * ((-8) + z * (34 + z * (21 + z * ((-109) + z * ((-140) + z * (25 + z * ((-29) + z * ((-4) + z * (83 + z * (66 + z * ((-36) + z * (41 + z * (34 + z * ((-12) + z * ((-7) + z * (20 + z * ((-36) + z * (21 + z * 48))))))))))))))))))))))))))))))))))))))


abbrev u5 {R : Type*} [CommRing R] (z : R) : R := pow5_139 z


def pow6_2 {R : Type*} [CommRing R] (z : R) : R := (44 + z * (137 + z * (3 + z * (84 + z * (61 + z * (97 + z * (44 + z * (118 + z * (76 + z * (88 + z * (118 + z * (131 + z * (132 + z * (91 + z * (110 + z * (28 + z * (51 + z * (101 + z * (71 + z * 14)))))))))))))))))))

def pow6_2_q {R : Type*} [CommRing R] (z : R) : R := (34 + z * (32 + z * (108 + z * (50 + z * (80 + z * (62 + z * (1 + z * (26 + z * (6 + z * (16 + z * (77 + z * (56 + z * (121 + z * (60 + z * (76 + z * (24 + z * (59 + z * (63 + z * 69))))))))))))))))))

def pow6_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-26) + z * ((-55) + z * ((-104) + z * ((-136) + z * ((-162) + z * ((-119) + z * ((-131) + z * ((-118) + z * (7 + z * ((-86) + z * ((-46) + z * (61 + z * ((-103) + z * ((-88) + z * ((-13) + z * ((-141) + z * ((-36) + z * (72 + z * (61 + z * (157 + z * (247 + z * (110 + z * (301 + z * (292 + z * (155 + z * (319 + z * (367 + z * (253 + z * (284 + z * (327 + z * (178 + z * (121 + z * (197 + z * (181 + z * (278 + z * (206 + z * (73 + z * (123 + z * 93))))))))))))))))))))))))))))))))))))))


def pow6_4 {R : Type*} [CommRing R] (z : R) : R := (100 + z * (34 + z * (133 + z * (87 + z * (28 + z * (74 + z * (52 + z * (45 + z * (130 + z * (120 + z * (2 + z * (36 + z * (109 + z * (21 + z * (88 + z * (8 + z * (4 + z * (124 + z * (71 + z * 20)))))))))))))))))))

def pow6_4_q {R : Type*} [CommRing R] (z : R) : R := (85 + z * (25 + z * (63 + z * (41 + z * (98 + z * (46 + z * (109 + z * (4 + z * (127 + z * (131 + z * (6 + z * (71 + z * (75 + z * (134 + z * (31 + z * (73 + z * (101 + z * (113 + z * 57))))))))))))))))))

def pow6_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-51) + z * ((-7) + z * ((-10) + z * ((-131) + z * ((-53) + z * ((-78) + z * ((-64) + z * ((-101) + z * (12 + z * ((-171) + z * ((-33) + z * (52 + z * (107 + z * (35 + z * (141 + z * (119 + z * ((-51) + z * (125 + z * (69 + z * (48 + z * (127 + z * (165 + z * (127 + z * (221 + z * (149 + z * (123 + z * (81 + z * ((-35) + z * (88 + z * (105 + z * (25 + z * ((-94) + z * ((-137) + z * ((-89) + z * ((-58) + z * ((-63) + z * ((-90) + z * ((-39) + z * 1))))))))))))))))))))))))))))))))))))))


def pow6_8 {R : Type*} [CommRing R] (z : R) : R := (68 + z * (129 + z * (60 + z * (82 + z * (72 + z * (20 + z * (40 + z * (8 + z * (137 + z * (85 + z * (123 + z * (128 + z * (63 + z * (111 + z * (18 + z * (50 + z * (106 + z * (52 + z * (108 + z * 64)))))))))))))))))))

def pow6_8_q {R : Type*} [CommRing R] (z : R) : R := (84 + z * (3 + z * (61 + z * (120 + z * (128 + z * (18 + z * (122 + z * (115 + z * (116 + z * (86 + z * (23 + z * (120 + z * (107 + z * (69 + z * (75 + z * (19 + z * (52 + z * (12 + z * 122))))))))))))))))))

def pow6_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (8 + z * ((-28) + z * (75 + z * ((-37) + z * ((-116) + z * ((-33) + z * ((-196) + z * ((-225) + z * ((-116) + z * ((-171) + z * ((-211) + z * ((-126) + z * ((-274) + z * ((-441) + z * ((-133) + z * ((-374) + z * ((-406) + z * ((-104) + z * ((-416) + z * ((-337) + z * ((-133) + z * ((-384) + z * ((-468) + z * ((-222) + z * ((-315) + z * ((-226) + z * ((-44) + z * ((-366) + z * ((-249) + z * ((-59) + z * ((-162) + z * ((-108) + z * ((-111) + z * ((-131) + z * ((-41) + z * (71 + z * ((-29) + z * ((-92) + z * 2))))))))))))))))))))))))))))))))))))))


def pow6_16 {R : Type*} [CommRing R] (z : R) : R := (112 + z * (67 + z * (13 + z * (79 + z * (86 + z * (24 + z * (53 + z * (57 + z * (113 + z * (131 + z * (44 + z * (103 + z * (103 + z * (62 + z * (28 + z * (34 + z * (40 + z * (27 + z * (86 + z * 57)))))))))))))))))))

def pow6_16_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (47 + z * (94 + z * (134 + z * (59 + z * (71 + z * (121 + z * (43 + z * (72 + z * (37 + z * (34 + z * (101 + z * (37 + z * (32 + z * (42 + z * (121 + z * (93 + z * (83 + z * 65))))))))))))))))))

def pow6_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (3 + z * (56 + z * (31 + z * ((-72) + z * ((-74) + z * ((-140) + z * ((-249) + z * ((-246) + z * ((-192) + z * ((-65) + z * ((-56) + z * (62 + z * (68 + z * (10 + z * (85 + z * ((-225) + z * ((-129) + z * ((-62) + z * ((-128) + z * (93 + z * (67 + z * (28 + z * (16 + z * (68 + z * ((-7) + z * ((-67) + z * (201 + z * (178 + z * (197 + z * (210 + z * ((-21) + z * (6 + z * (30 + z * ((-65) + z * ((-4) + z * (31 + z * (7 + z * (39 + z * 29))))))))))))))))))))))))))))))))))))))


def pow6_17 {R : Type*} [CommRing R] (z : R) : R := (50 + z * (86 + z * (75 + z * (126 + z * (81 + z * (130 + z * (117 + z * (68 + z * (29 + z * (127 + z * (4 + z * (137 + z * (106 + z * (42 + z * (116 + z * (24 + z * (138 + z * (104 + z * (95 + z * 69)))))))))))))))))))

def pow6_17_q {R : Type*} [CommRing R] (z : R) : R := (26 + z * (50 + z * (64 + z * (27 + z * (23 + z * (127 + z * (105 + z * (101 + z * (47 + z * (21 + z * (107 + z * (70 + z * (126 + z * (23 + z * (53 + z * (20 + z * (17 + z * (71 + z * 104))))))))))))))))))

def pow6_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * ((-4) + z * ((-36) + z * ((-55) + z * (10 + z * ((-97) + z * ((-205) + z * ((-125) + z * ((-204) + z * ((-209) + z * ((-82) + z * ((-67) + z * ((-131) + z * ((-75) + z * ((-192) + z * ((-137) + z * (5 + z * ((-47) + z * ((-34) + z * (77 + z * ((-106) + z * ((-135) + z * (155 + z * (84 + z * ((-20) + z * (17 + z * (49 + z * (142 + z * (120 + z * (133 + z * (34 + z * ((-6) + z * (49 + z * ((-11) + z * (76 + z * (75 + z * ((-27) + z * (21 + z * 46))))))))))))))))))))))))))))))))))))))


def pow6_34 {R : Type*} [CommRing R] (z : R) : R := (100 + z * (20 + z * (85 + z * (129 + z * (56 + z * (73 + z * (116 + z * (88 + z * (86 + z * (85 + z * (72 + z * (25 + z * (41 + z * (133 + z * (128 + z * (74 + z * (132 + z * (45 + z * (67 + z * 138)))))))))))))))))))

def pow6_34_q {R : Type*} [CommRing R] (z : R) : R := (3 + z * (110 + z * (11 + z * (65 + z * (92 + z * (72 + z * (97 + z * (94 + z * (134 + z * (101 + z * (136 + z * (14 + z * (66 + z * (50 + z * (69 + z * (37 + z * (62 + z * (12 + z * 35))))))))))))))))))

def pow6_34_mul_t {R : Type*} [CommRing R] (z : R) : R := (15 + z * ((-24) + z * ((-1) + z * (22 + z * (11 + z * (38 + z * (122 + z * (78 + z * (16 + z * (16 + z * ((-98) + z * ((-90) + z * (109 + z * ((-26) + z * (90 + z * (149 + z * (71 + z * (200 + z * (308 + z * (215 + z * (361 + z * (388 + z * (278 + z * (334 + z * (98 + z * (258 + z * (44 + z * (185 + z * (262 + z * (167 + z * (389 + z * (178 + z * (202 + z * (231 + z * (181 + z * (213 + z * (131 + z * (62 + z * 34))))))))))))))))))))))))))))))))))))))


def pow6_68 {R : Type*} [CommRing R] (z : R) : R := (54 + z * (46 + z * (120 + z * (15 + z * (55 + z * (69 + z * (105 + z * (89 + z * (112 + z * (74 + z * (103 + z * (100 + z * (126 + z * (107 + z * (75 + z * (115 + z * (109 + z * (45 + z * (27 + z * 21)))))))))))))))))))

def pow6_68_q {R : Type*} [CommRing R] (z : R) : R := (10 + z * (124 + z * (137 + z * (132 + z * (116 + z * (55 + z * (106 + z * (30 + z * (17 + z * (123 + z * (77 + z * (138 + z * (1 + z * (135 + z * (68 + z * (100 + z * (25 + z * (16 + z * 1))))))))))))))))))

def pow6_68_mul_t {R : Type*} [CommRing R] (z : R) : R := (64 + z * ((-74) + z * ((-97) + z * ((-131) + z * ((-283) + z * ((-214) + z * ((-131) + z * ((-116) + z * (9 + z * (15 + z * ((-88) + z * ((-240) + z * ((-170) + z * ((-128) + z * ((-160) + z * ((-119) + z * (73 + z * ((-71) + z * (85 + z * (238 + z * (81 + z * (276 + z * (328 + z * (217 + z * (171 + z * (226 + z * (281 + z * (247 + z * (202 + z * (184 + z * (183 + z * (225 + z * (355 + z * (260 + z * (177 + z * (270 + z * (106 + z * (132 + z * 137))))))))))))))))))))))))))))))))))))))


def pow6_69 {R : Type*} [CommRing R] (z : R) : R := (68 + z * (85 + z * (124 + z * (43 + z * (78 + z * (5 + z * (97 + z * (73 + z * (36 + z * (115 + z * (93 + z * (35 + z * (75 + z * (102 + z * (116 + z * (49 + z * (56 + z * (14 + z * (52 + z * 64)))))))))))))))))))

def pow6_69_q {R : Type*} [CommRing R] (z : R) : R := (2 + z * (40 + z * (17 + z * (98 + z * (74 + z * (60 + z * (20 + z * (24 + z * (114 + z * (52 + z * (85 + z * (91 + z * (29 + z * (35 + z * (112 + z * (74 + z * (67 + z * (114 + z * 31))))))))))))))))))

def pow6_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-2) + z * ((-5) + z * ((-5) + z * ((-19) + z * ((-70) + z * ((-105) + z * ((-80) + z * ((-73) + z * ((-74) + z * (50 + z * ((-56) + z * ((-47) + z * ((-45) + z * (15 + z * ((-20) + z * (109 + z * (97 + z * (41 + z * (15 + z * (123 + z * (189 + z * (149 + z * (225 + z * (214 + z * (146 + z * (310 + z * (232 + z * (119 + z * (235 + z * (158 + z * (89 + z * (214 + z * (97 + z * ((-3) + z * (98 + z * (11 + z * ((-61) + z * (10 + z * 17))))))))))))))))))))))))))))))))))))))


def pow6_138 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (108 + z * (39 + z * (23 + z * (93 + z * (16 + z * (85 + z * (14 + z * (95 + z * (103 + z * (47 + z * (26 + z * (125 + z * (126 + z * (99 + z * (30 + z * (119 + z * (61 + z * (7 + z * 13)))))))))))))))))))

def pow6_138_q {R : Type*} [CommRing R] (z : R) : R := (122 + z * (11 + z * (75 + z * (90 + z * (56 + z * (110 + z * (44 + z * (9 + z * (48 + z * (138 + z * (65 + z * (117 + z * (70 + z * (105 + z * (96 + z * (99 + z * (134 + z * (4 + z * 65))))))))))))))))))

def pow6_138_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-59) + z * ((-33) + z * ((-3) + z * ((-66) + z * ((-56) + z * ((-153) + z * ((-117) + z * ((-115) + z * ((-16) + z * ((-131) + z * ((-80) + z * ((-93) + z * ((-210) + z * ((-245) + z * ((-132) + z * ((-181) + z * ((-173) + z * ((-225) + z * ((-393) + z * ((-315) + z * ((-70) + z * ((-198) + z * ((-157) + z * ((-124) + z * ((-269) + z * ((-138) + z * ((-100) + z * ((-146) + z * ((-119) + z * ((-187) + z * ((-159) + z * ((-165) + z * ((-96) + z * ((-52) + z * ((-156) + z * ((-65) + z * ((-20) + z * ((-12) + z * 29))))))))))))))))))))))))))))))))))))))


def pow6_139 {R : Type*} [CommRing R] (z : R) : R := (40 + z * (101 + z * (26 + z * (11 + z * (7 + z * (135 + z * (89 + z * (129 + z * (14 + z * (135 + z * (13 + z * (52 + z * (21 + z * (43 + z * (42 + z * (50 + z * (103 + z * (62 + z * (67 + z * 28)))))))))))))))))))

def pow6_139_q {R : Type*} [CommRing R] (z : R) : R := (132 + z * (61 + z * (25 + z * (46 + z * (7 + z * (82 + z * (124 + z * (44 + z * (49 + z * (4 + z * (46 + z * (130 + z * (107 + z * (108 + z * (82 + z * (24 + z * (115 + z * (95 + z * 92))))))))))))))))))

def pow6_139_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-100) + z * ((-155) + z * ((-130) + z * ((-165) + z * ((-133) + z * ((-50) + z * ((-197) + z * ((-225) + z * ((-168) + z * ((-261) + z * ((-179) + z * ((-78) + z * ((-152) + z * ((-247) + z * ((-340) + z * ((-273) + z * ((-254) + z * ((-31) + z * ((-260) + z * ((-213) + z * ((-88) + z * ((-227) + z * ((-61) + z * (132 + z * ((-45) + z * ((-33) + z * ((-94) + z * (16 + z * (109 + z * ((-31) + z * ((-55) + z * ((-6) + z * (8 + z * ((-11) + z * ((-22) + z * ((-13) + z * ((-95) + z * ((-69) + z * 10))))))))))))))))))))))))))))))))))))))


abbrev u6 {R : Type*} [CommRing R] (z : R) : R := pow6_139 z

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Powers04
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139
def pow7_2 {R : Type*} [CommRing R] (z : R) : R := (26 + z * (98 + z * (47 + z * (78 + z * (15 + z * (135 + z * (52 + z * (87 + z * (82 + z * (19 + z * (8 + z * (41 + z * (82 + z * (109 + z * (41 + z * (89 + z * (65 + z * (123 + z * (87 + z * 45)))))))))))))))))))

def pow7_2_q {R : Type*} [CommRing R] (z : R) : R := (60 + z * (95 + z * (79 + z * (103 + z * (57 + z * (132 + z * (134 + z * (35 + z * (135 + z * (119 + z * (81 + z * (37 + z * (99 + z * (111 + z * (31 + z * (77 + z * (50 + z * (5 + z * 89))))))))))))))))))

def pow7_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-34) + z * ((-67) + z * ((-109) + z * ((-246) + z * ((-317) + z * ((-319) + z * ((-227) + z * ((-233) + z * ((-318) + z * ((-498) + z * ((-357) + z * ((-424) + z * ((-340) + z * ((-540) + z * ((-307) + z * ((-564) + z * ((-416) + z * ((-453) + z * ((-426) + z * ((-597) + z * ((-389) + z * ((-435) + z * ((-336) + z * ((-138) + z * ((-268) + z * ((-187) + z * ((-228) + z * ((-227) + z * ((-321) + z * ((-147) + z * ((-70) + z * ((-193) + z * ((-29) + z * (10 + z * ((-35) + z * (51 + z * ((-13) + z * ((-55) + z * 5))))))))))))))))))))))))))))))))))))))


def pow7_4 {R : Type*} [CommRing R] (z : R) : R := (131 + z * (67 + z * (3 + z * (11 + z * (5 + z * (0 + z * (86 + z * (81 + z * (99 + z * (136 + z * (105 + z * (107 + z * (127 + z * (86 + z * (38 + z * (54 + z * (13 + z * (107 + z * (131 + z * 77)))))))))))))))))))

def pow7_4_q {R : Type*} [CommRing R] (z : R) : R := (78 + z * (87 + z * (28 + z * (137 + z * (138 + z * (83 + z * (70 + z * (73 + z * (111 + z * (109 + z * (22 + z * (74 + z * (19 + z * (67 + z * (115 + z * (66 + z * (74 + z * (81 + z * 79))))))))))))))))))

def pow7_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-55) + z * ((-98) + z * ((-81) + z * ((-185) + z * ((-262) + z * ((-301) + z * ((-192) + z * ((-298) + z * ((-200) + z * ((-329) + z * ((-327) + z * ((-415) + z * ((-322) + z * ((-316) + z * ((-334) + z * ((-354) + z * ((-417) + z * ((-442) + z * ((-275) + z * ((-352) + z * ((-94) + z * ((-226) + z * ((-224) + z * ((-174) + z * ((-147) + z * ((-63) + z * ((-128) + z * ((-273) + z * ((-76) + z * (17 + z * (71 + z * (68 + z * (17 + z * ((-20) + z * (66 + z * (68 + z * (1 + z * ((-17) + z * 14))))))))))))))))))))))))))))))))))))))


def pow7_8 {R : Type*} [CommRing R] (z : R) : R := (116 + z * (41 + z * (114 + z * (46 + z * (104 + z * (68 + z * (75 + z * (42 + z * (25 + z * (104 + z * (36 + z * (97 + z * (10 + z * (135 + z * (17 + z * (18 + z * (86 + z * (93 + z * (55 + z * 65)))))))))))))))))))

def pow7_8_q {R : Type*} [CommRing R] (z : R) : R := (116 + z * (126 + z * (134 + z * (40 + z * (114 + z * (124 + z * (65 + z * (116 + z * (136 + z * (45 + z * (104 + z * (99 + z * (12 + z * (6 + z * (51 + z * (6 + z * (132 + z * (47 + z * 91))))))))))))))))))

def pow7_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (35 + z * ((-71) + z * ((-279) + z * ((-348) + z * ((-433) + z * ((-486) + z * ((-319) + z * ((-308) + z * ((-395) + z * ((-341) + z * ((-445) + z * ((-509) + z * ((-322) + z * ((-316) + z * ((-463) + z * ((-342) + z * ((-363) + z * ((-243) + z * ((-67) + z * ((-48) + z * ((-300) + z * ((-137) + z * (21 + z * ((-63) + z * (85 + z * (212 + z * (109 + z * (239 + z * (323 + z * (195 + z * (250 + z * (161 + z * (30 + z * (15 + z * ((-12) + z * (60 + z * (131 + z * (61 + z * 42))))))))))))))))))))))))))))))))))))))


def pow7_16 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (3 + z * (106 + z * (95 + z * (136 + z * (6 + z * (95 + z * (130 + z * (13 + z * (63 + z * (21 + z * (89 + z * (120 + z * (66 + z * (8 + z * (107 + z * (95 + z * (73 + z * (35 + z * 55)))))))))))))))))))

def pow7_16_q {R : Type*} [CommRing R] (z : R) : R := (103 + z * (94 + z * (88 + z * (95 + z * (34 + z * (108 + z * (21 + z * (109 + z * (2 + z * (0 + z * (126 + z * (62 + z * (33 + z * (89 + z * (36 + z * (36 + z * (12 + z * (110 + z * 55))))))))))))))))))

def pow7_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (19 + z * ((-93) + z * ((-40) + z * ((-188) + z * ((-65) + z * ((-135) + z * ((-14) + z * ((-127) + z * ((-102) + z * ((-29) + z * ((-209) + z * ((-45) + z * ((-207) + z * ((-4) + z * ((-281) + z * ((-86) + z * ((-178) + z * ((-55) + z * ((-94) + z * ((-112) + z * ((-197) + z * ((-134) + z * (126 + z * ((-124) + z * (27 + z * ((-87) + z * ((-96) + z * ((-3) + z * ((-2) + z * ((-29) + z * (46 + z * ((-70) + z * (5 + z * ((-42) + z * (59 + z * (62 + z * ((-33) + z * (0 + z * 30))))))))))))))))))))))))))))))))))))))


def pow7_17 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (92 + z * (3 + z * (136 + z * (57 + z * (82 + z * (71 + z * (34 + z * (85 + z * (46 + z * (36 + z * (102 + z * (33 + z * (132 + z * (96 + z * (69 + z * (8 + z * (75 + z * (1 + z * 5)))))))))))))))))))

def pow7_17_q {R : Type*} [CommRing R] (z : R) : R := (86 + z * (87 + z * (86 + z * (10 + z * (120 + z * (106 + z * (51 + z * (126 + z * (40 + z * (130 + z * (114 + z * (62 + z * (55 + z * (39 + z * (87 + z * (40 + z * (109 + z * (60 + z * 11))))))))))))))))))

def pow7_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-65) + z * ((-141) + z * ((-186) + z * ((-139) + z * ((-199) + z * ((-244) + z * ((-300) + z * ((-233) + z * ((-225) + z * ((-237) + z * ((-418) + z * ((-308) + z * ((-250) + z * ((-228) + z * ((-447) + z * ((-423) + z * ((-314) + z * ((-418) + z * ((-278) + z * ((-400) + z * ((-282) + z * ((-94) + z * ((-46) + z * ((-273) + z * ((-126) + z * ((-204) + z * ((-194) + z * ((-148) + z * ((-90) + z * ((-132) + z * ((-74) + z * ((-4) + z * ((-45) + z * (12 + z * (19 + z * ((-34) + z * ((-8) + z * (23 + z * 11))))))))))))))))))))))))))))))))))))))


def pow7_34 {R : Type*} [CommRing R] (z : R) : R := (55 + z * (107 + z * (40 + z * (56 + z * (34 + z * (22 + z * (135 + z * (0 + z * (20 + z * (34 + z * (120 + z * (13 + z * (119 + z * (66 + z * (3 + z * (44 + z * (115 + z * (33 + z * (76 + z * 2)))))))))))))))))))

def pow7_34_q {R : Type*} [CommRing R] (z : R) : R := (99 + z * (131 + z * (58 + z * (116 + z * (82 + z * (57 + z * (98 + z * (9 + z * (40 + z * (8 + z * (79 + z * (14 + z * (3 + z * (102 + z * (0 + z * (34 + z * (85 + z * (7 + z * 25))))))))))))))))))

def pow7_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-75) + z * ((-180) + z * ((-187) + z * ((-337) + z * ((-234) + z * ((-320) + z * ((-179) + z * ((-219) + z * ((-190) + z * ((-119) + z * ((-300) + z * ((-157) + z * ((-74) + z * ((-296) + z * ((-15) + z * ((-127) + z * ((-75) + z * ((-63) + z * (39 + z * ((-229) + z * ((-62) + z * ((-24) + z * ((-24) + z * ((-58) + z * (28 + z * (30 + z * (9 + z * (118 + z * (103 + z * ((-119) + z * (110 + z * ((-71) + z * ((-94) + z * ((-31) + z * ((-69) + z * ((-82) + z * ((-20) + z * ((-23) + z * 0))))))))))))))))))))))))))))))))))))))


def pow7_68 {R : Type*} [CommRing R] (z : R) : R := (124 + z * (89 + z * (12 + z * (60 + z * (68 + z * (22 + z * (61 + z * (89 + z * (122 + z * (32 + z * (81 + z * (90 + z * (12 + z * (87 + z * (25 + z * (92 + z * (73 + z * (135 + z * (19 + z * 66)))))))))))))))))))

def pow7_68_q {R : Type*} [CommRing R] (z : R) : R := (115 + z * (65 + z * (133 + z * (106 + z * (18 + z * (34 + z * (57 + z * (65 + z * (43 + z * (23 + z * (88 + z * (10 + z * (134 + z * (76 + z * (123 + z * (30 + z * (15 + z * (70 + z * 4))))))))))))))))))

def pow7_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-66) + z * ((-66) + z * ((-147) + z * ((-259) + z * ((-254) + z * ((-247) + z * ((-171) + z * ((-109) + z * ((-247) + z * ((-268) + z * ((-322) + z * ((-226) + z * ((-225) + z * ((-282) + z * ((-369) + z * ((-483) + z * ((-300) + z * ((-362) + z * ((-211) + z * ((-249) + z * ((-347) + z * ((-367) + z * ((-63) + z * ((-239) + z * ((-92) + z * ((-176) + z * ((-131) + z * ((-186) + z * (28 + z * ((-90) + z * ((-122) + z * ((-97) + z * ((-99) + z * ((-94) + z * (92 + z * ((-26) + z * ((-25) + z * ((-2) + z * 0))))))))))))))))))))))))))))))))))))))


def pow7_69 {R : Type*} [CommRing R] (z : R) : R := (107 + z * (90 + z * (125 + z * (80 + z * (53 + z * (20 + z * (54 + z * (40 + z * (43 + z * (47 + z * (134 + z * (69 + z * (110 + z * (103 + z * (135 + z * (43 + z * (62 + z * (71 + z * (55 + z * 74)))))))))))))))))))

def pow7_69_q {R : Type*} [CommRing R] (z : R) : R := (123 + z * (20 + z * (93 + z * (84 + z * (2 + z * (134 + z * (80 + z * (93 + z * (65 + z * (38 + z * (73 + z * (4 + z * (60 + z * (29 + z * (107 + z * (101 + z * (61 + z * (123 + z * 41))))))))))))))))))

def pow7_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-58) + z * ((-8) + z * ((-108) + z * ((-228) + z * ((-196) + z * ((-127) + z * ((-164) + z * ((-166) + z * ((-192) + z * ((-183) + z * ((-277) + z * ((-168) + z * ((-174) + z * ((-153) + z * ((-182) + z * ((-316) + z * ((-273) + z * ((-173) + z * ((-379) + z * ((-352) + z * ((-180) + z * ((-353) + z * (5 + z * ((-152) + z * ((-61) + z * ((-184) + z * ((-33) + z * ((-176) + z * ((-90) + z * ((-79) + z * ((-147) + z * ((-83) + z * ((-53) + z * ((-93) + z * ((-21) + z * ((-10) + z * ((-78) + z * ((-3) + z * 13))))))))))))))))))))))))))))))))))))))


def pow7_138 {R : Type*} [CommRing R] (z : R) : R := (50 + z * (102 + z * (112 + z * (11 + z * (42 + z * (65 + z * (49 + z * (48 + z * (115 + z * (33 + z * (65 + z * (95 + z * (37 + z * (64 + z * (31 + z * (77 + z * (28 + z * (116 + z * (133 + z * 8)))))))))))))))))))

def pow7_138_q {R : Type*} [CommRing R] (z : R) : R := (94 + z * (60 + z * (87 + z * (23 + z * (81 + z * (45 + z * (57 + z * (67 + z * (89 + z * (22 + z * (0 + z * (67 + z * (17 + z * (61 + z * (35 + z * (78 + z * (7 + z * (127 + z * 55))))))))))))))))))

def pow7_138_mul_t {R : Type*} [CommRing R] (z : R) : R := (11 + z * (10 + z * (47 + z * (48 + z * (7 + z * ((-41) + z * ((-46) + z * ((-107) + z * ((-149) + z * ((-162) + z * ((-20) + z * (7 + z * (205 + z * (199 + z * (274 + z * (114 + z * (184 + z * (41 + z * (4 + z * (92 + z * (103 + z * (48 + z * (160 + z * (141 + z * (175 + z * (184 + z * (170 + z * (134 + z * (274 + z * (280 + z * (111 + z * (140 + z * (96 + z * (10 + z * (8 + z * (22 + z * ((-60) + z * (7 + z * 39))))))))))))))))))))))))))))))))))))))


def pow7_139 {R : Type*} [CommRing R] (z : R) : R := (121 + z * (104 + z * (88 + z * (36 + z * (41 + z * (102 + z * (131 + z * (65 + z * (132 + z * (82 + z * (40 + z * (63 + z * (28 + z * (122 + z * (71 + z * (6 + z * (113 + z * (125 + z * (130 + z * 57)))))))))))))))))))

def pow7_139_q {R : Type*} [CommRing R] (z : R) : R := (96 + z * (79 + z * (27 + z * (31 + z * (6 + z * (68 + z * (69 + z * (118 + z * (105 + z * (110 + z * (99 + z * (36 + z * (84 + z * (40 + z * (37 + z * (38 + z * (109 + z * (52 + z * 85))))))))))))))))))

def pow7_139_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-59) + z * ((-79) + z * ((-61) + z * ((-102) + z * ((-155) + z * ((-88) + z * ((-19) + z * ((-44) + z * ((-165) + z * ((-235) + z * ((-363) + z * ((-234) + z * ((-256) + z * ((-238) + z * ((-253) + z * ((-237) + z * ((-329) + z * ((-197) + z * ((-236) + z * ((-335) + z * ((-273) + z * ((-297) + z * ((-150) + z * ((-113) + z * ((-49) + z * ((-256) + z * ((-218) + z * ((-127) + z * ((-211) + z * ((-91) + z * ((-82) + z * ((-113) + z * ((-57) + z * (32 + z * ((-4) + z * ((-12) + z * ((-20) + z * ((-48) + z * 1))))))))))))))))))))))))))))))))))))))


abbrev u7 {R : Type*} [CommRing R] (z : R) : R := pow7_139 z


def pow8_2 {R : Type*} [CommRing R] (z : R) : R := (49 + z * (22 + z * (135 + z * (107 + z * (117 + z * (129 + z * (71 + z * (42 + z * (102 + z * (136 + z * (79 + z * (21 + z * (98 + z * (126 + z * (111 + z * (104 + z * (41 + z * (62 + z * (47 + z * 10)))))))))))))))))))

def pow8_2_q {R : Type*} [CommRing R] (z : R) : R := (135 + z * (31 + z * (35 + z * (54 + z * (37 + z * (40 + z * (109 + z * (110 + z * (138 + z * (6 + z * (68 + z * (66 + z * (86 + z * (87 + z * (86 + z * (111 + z * (2 + z * (102 + z * 52))))))))))))))))))

def pow8_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (3 + z * (39 + z * (55 + z * ((-34) + z * ((-62) + z * (74 + z * (156 + z * (71 + z * (70 + z * (8 + z * ((-59) + z * (52 + z * (0 + z * (60 + z * (114 + z * ((-159) + z * ((-122) + z * (72 + z * (175 + z * (218 + z * (54 + z * ((-12) + z * (158 + z * (138 + z * (203 + z * (142 + z * (70 + z * (32 + z * ((-50) + z * (82 + z * (63 + z * (60 + z * (103 + z * ((-7) + z * (181 + z * (249 + z * (92 + z * (58 + z * 23))))))))))))))))))))))))))))))))))))))


def pow8_4 {R : Type*} [CommRing R] (z : R) : R := (55 + z * (17 + z * (61 + z * (92 + z * (21 + z * (62 + z * (24 + z * (133 + z * (87 + z * (87 + z * (14 + z * (6 + z * (80 + z * (91 + z * (119 + z * (117 + z * (16 + z * (119 + z * (118 + z * 19)))))))))))))))))))

def pow8_4_q {R : Type*} [CommRing R] (z : R) : R := (70 + z * (37 + z * (9 + z * (21 + z * (50 + z * (74 + z * (16 + z * (4 + z * (41 + z * (95 + z * (67 + z * (50 + z * (137 + z * (80 + z * (107 + z * (59 + z * (121 + z * (94 + z * 100))))))))))))))))))

def pow8_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-36) + z * ((-74) + z * ((-4) + z * ((-6) + z * (93 + z * (158 + z * (216 + z * (280 + z * (292 + z * (243 + z * (257 + z * (310 + z * (266 + z * (175 + z * (231 + z * (257 + z * (223 + z * (395 + z * (242 + z * (115 + z * (141 + z * (176 + z * (189 + z * (127 + z * ((-10) + z * ((-63) + z * ((-3) + z * ((-52) + z * ((-124) + z * ((-64) + z * ((-112) + z * ((-185) + z * ((-158) + z * ((-162) + z * ((-157) + z * ((-133) + z * ((-136) + z * ((-86) + z * 0))))))))))))))))))))))))))))))))))))))


def pow8_8 {R : Type*} [CommRing R] (z : R) : R := (114 + z * (31 + z * (127 + z * (92 + z * (92 + z * (14 + z * (94 + z * (54 + z * (18 + z * (80 + z * (18 + z * (83 + z * (131 + z * (123 + z * (122 + z * (65 + z * (54 + z * (47 + z * (109 + z * 94)))))))))))))))))))

def pow8_8_q {R : Type*} [CommRing R] (z : R) : R := (82 + z * (48 + z * (59 + z * (138 + z * (77 + z * (87 + z * (12 + z * (49 + z * (16 + z * (60 + z * (103 + z * (36 + z * (71 + z * (49 + z * (23 + z * (128 + z * (125 + z * (115 + z * 83))))))))))))))))))

def pow8_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-41) + z * ((-95) + z * ((-111) + z * ((-190) + z * ((-277) + z * ((-241) + z * ((-262) + z * ((-194) + z * ((-136) + z * ((-127) + z * ((-165) + z * ((-234) + z * ((-224) + z * ((-392) + z * ((-138) + z * ((-101) + z * ((-242) + z * ((-195) + z * ((-406) + z * ((-444) + z * ((-104) + z * (10 + z * (16 + z * ((-103) + z * ((-11) + z * ((-65) + z * (0 + z * (68 + z * ((-157) + z * ((-22) + z * (52 + z * ((-7) + z * (154 + z * ((-6) + z * ((-118) + z * (6 + z * ((-35) + z * ((-45) + z * 2))))))))))))))))))))))))))))))))))))))


def pow8_16 {R : Type*} [CommRing R] (z : R) : R := (104 + z * (88 + z * (123 + z * (69 + z * (24 + z * (29 + z * (86 + z * (65 + z * (53 + z * (103 + z * (68 + z * (79 + z * (3 + z * (133 + z * (1 + z * (38 + z * (68 + z * (118 + z * (119 + z * 133)))))))))))))))))))

def pow8_16_q {R : Type*} [CommRing R] (z : R) : R := (46 + z * (17 + z * (57 + z * (57 + z * (56 + z * (118 + z * (8 + z * (58 + z * (40 + z * (75 + z * (124 + z * (125 + z * (35 + z * (134 + z * (103 + z * (54 + z * (71 + z * (94 + z * 79))))))))))))))))))

def pow8_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (58 + z * ((-3) + z * (115 + z * (55 + z * (112 + z * ((-39) + z * (109 + z * ((-26) + z * ((-12) + z * (19 + z * ((-140) + z * ((-132) + z * ((-98) + z * ((-70) + z * ((-44) + z * (55 + z * (65 + z * ((-81) + z * ((-37) + z * ((-48) + z * ((-74) + z * ((-3) + z * (24 + z * ((-146) + z * ((-76) + z * (137 + z * ((-52) + z * (5 + z * (32 + z * ((-61) + z * (127 + z * (168 + z * (71 + z * (39 + z * (20 + z * (12 + z * (4 + z * (74 + z * 63))))))))))))))))))))))))))))))))))))))


def pow8_17 {R : Type*} [CommRing R] (z : R) : R := (39 + z * (119 + z * (26 + z * (19 + z * (100 + z * (69 + z * (70 + z * (121 + z * (10 + z * (12 + z * (11 + z * (18 + z * (114 + z * (12 + z * (42 + z * (2 + z * (27 + z * (119 + z * (106 + z * 43)))))))))))))))))))

def pow8_17_q {R : Type*} [CommRing R] (z : R) : R := (93 + z * (127 + z * (133 + z * (64 + z * (107 + z * (57 + z * (126 + z * (112 + z * (46 + z * (111 + z * (58 + z * (54 + z * (101 + z * (0 + z * (70 + z * (66 + z * (83 + z * (17 + z * 75))))))))))))))))))

def pow8_17_mul_t {R : Type*} [CommRing R] (z : R) : R := (20 + z * ((-24) + z * ((-57) + z * ((-133) + z * ((-247) + z * ((-228) + z * ((-149) + z * ((-147) + z * ((-102) + z * ((-182) + z * ((-265) + z * ((-205) + z * ((-274) + z * ((-153) + z * ((-190) + z * ((-217) + z * ((-282) + z * ((-120) + z * (11 + z * (43 + z * ((-109) + z * ((-57) + z * ((-97) + z * (72 + z * (154 + z * ((-3) + z * (195 + z * (166 + z * ((-19) + z * (143 + z * (86 + z * (73 + z * (164 + z * (91 + z * (103 + z * (264 + z * (208 + z * (104 + z * 54))))))))))))))))))))))))))))))))))))))


def pow8_34 {R : Type*} [CommRing R] (z : R) : R := (72 + z * (98 + z * (89 + z * (122 + z * (26 + z * (43 + z * (35 + z * (76 + z * (54 + z * (31 + z * (86 + z * (70 + z * (128 + z * (5 + z * (117 + z * (109 + z * (123 + z * (116 + z * (103 + z * 32)))))))))))))))))))

def pow8_34_q {R : Type*} [CommRing R] (z : R) : R := (125 + z * (113 + z * (44 + z * (113 + z * (138 + z * (62 + z * (100 + z * (67 + z * (137 + z * (87 + z * (59 + z * (0 + z * (9 + z * (95 + z * (2 + z * (65 + z * (85 + z * (126 + z * 42))))))))))))))))))

def pow8_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-84) + z * ((-129) + z * ((-129) + z * ((-290) + z * ((-355) + z * ((-221) + z * ((-276) + z * ((-295) + z * ((-272) + z * ((-478) + z * ((-561) + z * ((-401) + z * ((-341) + z * ((-381) + z * ((-454) + z * ((-505) + z * ((-618) + z * ((-614) + z * ((-417) + z * ((-486) + z * ((-539) + z * ((-337) + z * ((-371) + z * ((-272) + z * ((-75) + z * ((-234) + z * ((-349) + z * ((-371) + z * ((-232) + z * ((-47) + z * (8 + z * ((-117) + z * ((-178) + z * ((-107) + z * ((-13) + z * (27 + z * (7 + z * (26 + z * 13))))))))))))))))))))))))))))))))))))))


def pow8_68 {R : Type*} [CommRing R] (z : R) : R := (53 + z * (93 + z * (37 + z * (136 + z * (101 + z * (45 + z * (94 + z * (86 + z * (9 + z * (89 + z * (54 + z * (98 + z * (11 + z * (102 + z * (70 + z * (60 + z * (124 + z * (56 + z * (135 + z * 137)))))))))))))))))))

def pow8_68_q {R : Type*} [CommRing R] (z : R) : R := (123 + z * (74 + z * (133 + z * (13 + z * (43 + z * (81 + z * (19 + z * (46 + z * (44 + z * (127 + z * (74 + z * (114 + z * (54 + z * (10 + z * (33 + z * (97 + z * (52 + z * (64 + z * 51))))))))))))))))))

def pow8_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-56) + z * ((-63) + z * ((-115) + z * ((-59) + z * ((-75) + z * ((-95) + z * ((-69) + z * ((-81) + z * ((-73) + z * ((-213) + z * ((-209) + z * ((-244) + z * ((-168) + z * ((-116) + z * ((-71) + z * ((-48) + z * ((-37) + z * (185 + z * (24 + z * (89 + z * (4 + z * (22 + z * (153 + z * (54 + z * (53 + z * (19 + z * (239 + z * (107 + z * (187 + z * (251 + z * (194 + z * (208 + z * (327 + z * (233 + z * (159 + z * (133 + z * (33 + z * (0 + z * 7))))))))))))))))))))))))))))))))))))))


def pow8_69 {R : Type*} [CommRing R] (z : R) : R := (130 + z * (76 + z * (3 + z * (88 + z * (8 + z * (46 + z * (131 + z * (17 + z * (90 + z * (13 + z * (42 + z * (30 + z * (106 + z * (87 + z * (104 + z * (120 + z * (45 + z * (5 + z * (136 + z * 63)))))))))))))))))))

def pow8_69_q {R : Type*} [CommRing R] (z : R) : R := (130 + z * (86 + z * (127 + z * (99 + z * (102 + z * (100 + z * (111 + z * (43 + z * (20 + z * (72 + z * (116 + z * (75 + z * (44 + z * (84 + z * (41 + z * (105 + z * (31 + z * (65 + z * 25))))))))))))))))))

def pow8_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-53) + z * ((-59) + z * ((-153) + z * ((-169) + z * ((-209) + z * ((-205) + z * ((-185) + z * ((-155) + z * ((-121) + z * ((-74) + z * ((-223) + z * ((-108) + z * ((-157) + z * ((-276) + z * ((-173) + z * ((-231) + z * ((-179) + z * ((-15) + z * ((-73) + z * (31 + z * (92 + z * (92 + z * (146 + z * (127 + z * (207 + z * (99 + z * (139 + z * (270 + z * (43 + z * (108 + z * (120 + z * (131 + z * (268 + z * (132 + z * (166 + z * (259 + z * (194 + z * (160 + z * 56))))))))))))))))))))))))))))))))))))))


def pow8_138 {R : Type*} [CommRing R] (z : R) : R := (137 + z * (27 + z * (75 + z * (37 + z * (65 + z * (16 + z * (138 + z * (73 + z * (134 + z * (128 + z * (80 + z * (59 + z * (1 + z * (34 + z * (49 + z * (58 + z * (117 + z * (133 + z * (79 + z * 60)))))))))))))))))))

def pow8_138_q {R : Type*} [CommRing R] (z : R) : R := (18 + z * (77 + z * (66 + z * (19 + z * (51 + z * (24 + z * (36 + z * (116 + z * (106 + z * (130 + z * (73 + z * (48 + z * (93 + z * (54 + z * (43 + z * (99 + z * (29 + z * (52 + z * 77))))))))))))))))))

def pow8_138_mul_t {R : Type*} [CommRing R] (z : R) : R := (107 + z * (68 + z * ((-87) + z * (9 + z * ((-91) + z * ((-110) + z * (157 + z * ((-74) + z * ((-108) + z * ((-172) + z * ((-411) + z * ((-298) + z * ((-182) + z * ((-129) + z * ((-80) + z * ((-100) + z * ((-203) + z * ((-417) + z * ((-2) + z * ((-94) + z * ((-198) + z * ((-44) + z * ((-222) + z * ((-196) + z * (32 + z * ((-180) + z * ((-30) + z * ((-61) + z * ((-98) + z * (66 + z * (120 + z * (31 + z * (134 + z * (127 + z * (20 + z * ((-15) + z * (33 + z * (52 + z * 28))))))))))))))))))))))))))))))))))))))


def pow8_139 {R : Type*} [CommRing R] (z : R) : R := (123 + z * (122 + z * (58 + z * (6 + z * (73 + z * (55 + z * (45 + z * (68 + z * (87 + z * (137 + z * (102 + z * (39 + z * (90 + z * (70 + z * (61 + z * (46 + z * (83 + z * (124 + z * (34 + z * 84)))))))))))))))))))

def pow8_139_q {R : Type*} [CommRing R] (z : R) : R := (23 + z * (82 + z * (28 + z * (83 + z * (128 + z * (34 + z * (114 + z * (82 + z * (75 + z * (80 + z * (130 + z * (116 + z * (110 + z * (15 + z * (22 + z * (48 + z * (67 + z * (22 + z * 84))))))))))))))))))

def pow8_139_mul_t {R : Type*} [CommRing R] (z : R) : R := (101 + z * (43 + z * (58 + z * ((-42) + z * ((-112) + z * ((-97) + z * ((-11) + z * ((-80) + z * (65 + z * (38 + z * ((-86) + z * ((-138) + z * ((-210) + z * ((-189) + z * ((-120) + z * ((-28) + z * (16 + z * (107 + z * (86 + z * ((-75) + z * ((-138) + z * ((-33) + z * (33 + z * (130 + z * (200 + z * (80 + z * (98 + z * (119 + z * ((-28) + z * ((-8) + z * (11 + z * ((-6) + z * (170 + z * (194 + z * (156 + z * (214 + z * (100 + z * (11 + z * 24))))))))))))))))))))))))))))))))))))))


abbrev u8 {R : Type*} [CommRing R] (z : R) : R := pow8_139 z

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
def pow9_2 {R : Type*} [CommRing R] (z : R) : R := (73 + z * (45 + z * (77 + z * (120 + z * (43 + z * (71 + z * (112 + z * (119 + z * (118 + z * (35 + z * (137 + z * (58 + z * (86 + z * (110 + z * (56 + z * (137 + z * (97 + z * (6 + z * (76 + z * 50)))))))))))))))))))

def pow9_2_q {R : Type*} [CommRing R] (z : R) : R := (105 + z * (80 + z * (6 + z * (120 + z * (63 + z * (67 + z * (94 + z * (27 + z * (56 + z * (2 + z * (45 + z * (52 + z * (83 + z * (33 + z * (97 + z * (79 + z * (98 + z * (67 + z * 106))))))))))))))))))

def pow9_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (29 + z * (63 + z * (40 + z * ((-156) + z * ((-153) + z * ((-84) + z * ((-129) + z * ((-154) + z * ((-52) + z * (98 + z * (99 + z * (61 + z * (24 + z * ((-16) + z * ((-1) + z * ((-101) + z * ((-126) + z * (164 + z * (25 + z * ((-97) + z * ((-17) + z * ((-8) + z * ((-48) + z * (98 + z * (26 + z * (75 + z * (174 + z * (70 + z * (83 + z * (93 + z * ((-66) + z * ((-50) + z * ((-25) + z * ((-27) + z * ((-27) + z * (21 + z * (18 + z * ((-57) + z * 50))))))))))))))))))))))))))))))))))))))


def pow9_4 {R : Type*} [CommRing R] (z : R) : R := (87 + z * (104 + z * (2 + z * (138 + z * (117 + z * (20 + z * (2 + z * (120 + z * (57 + z * (10 + z * (38 + z * (10 + z * (59 + z * (73 + z * (44 + z * (101 + z * (117 + z * (92 + z * (81 + z * 38)))))))))))))))))))

def pow9_4_q {R : Type*} [CommRing R] (z : R) : R := (132 + z * (30 + z * (27 + z * (70 + z * (131 + z * (138 + z * (67 + z * (132 + z * (2 + z * (72 + z * (133 + z * (59 + z * (21 + z * (98 + z * (120 + z * (126 + z * (5 + z * (72 + z * 137))))))))))))))))))

def pow9_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-62) + z * ((-92) + z * ((-70) + z * ((-54) + z * ((-152) + z * ((-136) + z * ((-117) + z * ((-204) + z * ((-72) + z * ((-73) + z * ((-31) + z * ((-13) + z * (29 + z * ((-1) + z * ((-103) + z * (28 + z * (51 + z * ((-17) + z * (67 + z * ((-117) + z * ((-20) + z * (183 + z * (87 + z * ((-12) + z * ((-5) + z * (79 + z * (106 + z * ((-17) + z * ((-24) + z * (3 + z * (4 + z * (20 + z * ((-66) + z * ((-153) + z * ((-30) + z * (18 + z * ((-121) + z * ((-72) + z * 17))))))))))))))))))))))))))))))))))))))


def pow9_8 {R : Type*} [CommRing R] (z : R) : R := (118 + z * (38 + z * (115 + z * (109 + z * (64 + z * (70 + z * (13 + z * (6 + z * (72 + z * (55 + z * (135 + z * (85 + z * (87 + z * (60 + z * (123 + z * (30 + z * (125 + z * (37 + z * (123 + z * 4)))))))))))))))))))

def pow9_8_q {R : Type*} [CommRing R] (z : R) : R := (112 + z * (67 + z * (86 + z * (21 + z * (11 + z * (45 + z * (4 + z * (0 + z * (128 + z * (117 + z * (10 + z * (92 + z * (92 + z * (96 + z * (124 + z * (71 + z * (7 + z * (78 + z * 54))))))))))))))))))

def pow9_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-31) + z * ((-19) + z * ((-145) + z * ((-83) + z * (97 + z * ((-27) + z * ((-26) + z * (204 + z * (101 + z * ((-293) + z * ((-165) + z * ((-119) + z * ((-308) + z * ((-282) + z * ((-265) + z * ((-320) + z * ((-132) + z * ((-110) + z * ((-250) + z * (0 + z * (47 + z * ((-213) + z * ((-71) + z * ((-84) + z * ((-266) + z * ((-76) + z * ((-140) + z * ((-395) + z * ((-162) + z * ((-7) + z * ((-72) + z * (43 + z * (65 + z * (30 + z * (136 + z * (107 + z * ((-14) + z * ((-6) + z * 10))))))))))))))))))))))))))))))))))))))


def pow9_16 {R : Type*} [CommRing R] (z : R) : R := (37 + z * (89 + z * (42 + z * (101 + z * (79 + z * (11 + z * (91 + z * (58 + z * (137 + z * (115 + z * (48 + z * (120 + z * (93 + z * (90 + z * (107 + z * (61 + z * (29 + z * (20 + z * (100 + z * 47)))))))))))))))))))

def pow9_16_q {R : Type*} [CommRing R] (z : R) : R := (29 + z * (125 + z * (55 + z * (45 + z * (80 + z * (125 + z * (95 + z * (126 + z * (136 + z * (71 + z * (113 + z * (6 + z * (35 + z * (92 + z * (136 + z * (107 + z * (4 + z * (48 + z * 16))))))))))))))))))

def pow9_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (78 + z * ((-56) + z * (28 + z * (25 + z * ((-28) + z * ((-30) + z * ((-136) + z * ((-245) + z * ((-313) + z * ((-413) + z * ((-286) + z * ((-273) + z * ((-43) + z * ((-33) + z * ((-127) + z * ((-296) + z * ((-149) + z * ((-376) + z * ((-23) + z * ((-120) + z * ((-112) + z * ((-54) + z * ((-111) + z * ((-296) + z * ((-135) + z * ((-112) + z * (90 + z * (11 + z * (157 + z * (29 + z * (154 + z * (4 + z * (124 + z * ((-128) + z * (117 + z * (33 + z * (55 + z * ((-8) + z * 0))))))))))))))))))))))))))))))))))))))


def pow9_17 {R : Type*} [CommRing R] (z : R) : R := (81 + z * (56 + z * (36 + z * (60 + z * (15 + z * (77 + z * (75 + z * (21 + z * (33 + z * (95 + z * (113 + z * (45 + z * (76 + z * (98 + z * (0 + z * (104 + z * (131 + z * (39 + z * (72 + z * 120)))))))))))))))))))

def pow9_17_q {R : Type*} [CommRing R] (z : R) : R := (122 + z * (46 + z * (23 + z * (24 + z * (73 + z * (125 + z * (0 + z * (120 + z * (34 + z * (99 + z * (130 + z * (23 + z * (122 + z * (64 + z * (105 + z * (100 + z * (47 + z * (50 + z * 56))))))))))))))))))

def pow9_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-60) + z * ((-31) + z * ((-37) + z * ((-31) + z * ((-37) + z * ((-91) + z * ((-76) + z * ((-126) + z * ((-44) + z * ((-52) + z * ((-107) + z * ((-45) + z * ((-9) + z * ((-78) + z * ((-157) + z * ((-113) + z * ((-132) + z * ((-114) + z * ((-62) + z * ((-73) + z * (13 + z * (53 + z * (12 + z * ((-61) + z * ((-4) + z * ((-1) + z * (1 + z * (81 + z * ((-49) + z * ((-21) + z * (17 + z * ((-37) + z * ((-5) + z * ((-77) + z * ((-37) + z * (59 + z * ((-9) + z * (20 + z * 28))))))))))))))))))))))))))))))))))))))


def pow9_34 {R : Type*} [CommRing R] (z : R) : R := (125 + z * (102 + z * (62 + z * (20 + z * (37 + z * (26 + z * (51 + z * (71 + z * (124 + z * (4 + z * (113 + z * (89 + z * (34 + z * (60 + z * (138 + z * (113 + z * (54 + z * (118 + z * (69 + z * 124)))))))))))))))))))

def pow9_34_q {R : Type*} [CommRing R] (z : R) : R := (56 + z * (117 + z * (4 + z * (25 + z * (60 + z * (20 + z * (79 + z * (128 + z * (107 + z * (134 + z * (64 + z * (16 + z * (125 + z * (125 + z * (48 + z * (55 + z * (64 + z * (123 + z * 83))))))))))))))))))

def pow9_34_mul_t {R : Type*} [CommRing R] (z : R) : R := (4 + z * ((-73) + z * ((-92) + z * ((-82) + z * ((-151) + z * ((-70) + z * ((-30) + z * ((-196) + z * ((-274) + z * ((-314) + z * ((-342) + z * ((-291) + z * ((-217) + z * ((-298) + z * ((-407) + z * ((-235) + z * ((-325) + z * ((-465) + z * ((-220) + z * ((-286) + z * ((-343) + z * ((-110) + z * ((-208) + z * ((-245) + z * ((-47) + z * ((-83) + z * ((-195) + z * ((-190) + z * (45 + z * (131 + z * ((-55) + z * (6 + z * (33 + z * ((-60) + z * (159 + z * (117 + z * ((-70) + z * (47 + z * 103))))))))))))))))))))))))))))))))))))))


def pow9_68 {R : Type*} [CommRing R] (z : R) : R := (125 + z * (128 + z * (101 + z * (7 + z * (104 + z * (29 + z * (95 + z * (37 + z * (71 + z * (20 + z * (0 + z * (44 + z * (16 + z * (123 + z * (92 + z * (65 + z * (133 + z * (55 + z * (30 + z * 8)))))))))))))))))))

def pow9_68_q {R : Type*} [CommRing R] (z : R) : R := (2 + z * (5 + z * (129 + z * (101 + z * (62 + z * (125 + z * (64 + z * (120 + z * (117 + z * (74 + z * (20 + z * (114 + z * (28 + z * (36 + z * (105 + z * (41 + z * (101 + z * (127 + z * 86))))))))))))))))))

def pow9_68_mul_t {R : Type*} [CommRing R] (z : R) : R := (110 + z * (177 + z * (82 + z * ((-69) + z * ((-135) + z * ((-248) + z * ((-248) + z * ((-203) + z * ((-108) + z * ((-274) + z * ((-171) + z * ((-223) + z * ((-273) + z * ((-228) + z * ((-72) + z * ((-87) + z * ((-121) + z * ((-235) + z * ((-229) + z * ((-27) + z * ((-225) + z * ((-269) + z * ((-65) + z * ((-98) + z * ((-102) + z * (191 + z * ((-40) + z * (41 + z * (182 + z * (257 + z * (72 + z * (157 + z * (145 + z * (162 + z * (171 + z * (27 + z * (64 + z * (43 + z * 110))))))))))))))))))))))))))))))))))))))


def pow9_69 {R : Type*} [CommRing R] (z : R) : R := (125 + z * (64 + z * (125 + z * (82 + z * (16 + z * (100 + z * (42 + z * (46 + z * (76 + z * (58 + z * (18 + z * (81 + z * (57 + z * (127 + z * (130 + z * (132 + z * (22 + z * (121 + z * (96 + z * 22)))))))))))))))))))

def pow9_69_q {R : Type*} [CommRing R] (z : R) : R := (132 + z * (30 + z * (82 + z * (1 + z * (1 + z * (24 + z * (85 + z * (80 + z * (102 + z * (63 + z * (104 + z * (68 + z * (63 + z * (58 + z * (118 + z * (127 + z * (72 + z * (37 + z * 116))))))))))))))))))

def pow9_69_mul_t {R : Type*} [CommRing R] (z : R) : R := (10 + z * (84 + z * (46 + z * ((-72) + z * (4 + z * (79 + z * (91 + z * (12 + z * (0 + z * ((-74) + z * ((-149) + z * ((-123) + z * ((-115) + z * ((-41) + z * ((-17) + z * ((-216) + z * ((-202) + z * ((-55) + z * ((-247) + z * ((-297) + z * ((-204) + z * ((-195) + z * ((-160) + z * ((-59) + z * ((-226) + z * ((-150) + z * ((-191) + z * ((-221) + z * ((-226) + z * ((-151) + z * ((-58) + z * ((-128) + z * ((-3) + z * ((-71) + z * ((-126) + z * (31 + z * ((-72) + z * ((-87) + z * 4))))))))))))))))))))))))))))))))))))))


def pow9_138 {R : Type*} [CommRing R] (z : R) : R := (2 + z * (18 + z * (82 + z * (3 + z * (30 + z * (87 + z * (72 + z * (18 + z * (114 + z * (78 + z * (68 + z * (73 + z * (117 + z * (20 + z * (51 + z * (16 + z * (18 + z * (0 + z * (44 + z * 102)))))))))))))))))))

def pow9_138_q {R : Type*} [CommRing R] (z : R) : R := (27 + z * (52 + z * (5 + z * (5 + z * (8 + z * (138 + z * (44 + z * (19 + z * (62 + z * (109 + z * (33 + z * (67 + z * (63 + z * (119 + z * (66 + z * (7 + z * (5 + z * (96 + z * 67))))))))))))))))))

def pow9_138_mul_t {R : Type*} [CommRing R] (z : R) : R := (92 + z * (52 + z * (180 + z * (182 + z * (131 + z * (172 + z * (49 + z * (97 + z * (86 + z * ((-34) + z * (8 + z * (46 + z * ((-44) + z * (98 + z * (119 + z * (188 + z * (252 + z * (332 + z * (184 + z * (193 + z * (232 + z * ((-32) + z * (135 + z * (79 + z * ((-40) + z * (117 + z * (189 + z * (8 + z * (189 + z * (236 + z * (216 + z * (204 + z * (201 + z * (72 + z * (111 + z * (99 + z * ((-33) + z * ((-32) + z * 3))))))))))))))))))))))))))))))))))))))


def pow9_139 {R : Type*} [CommRing R] (z : R) : R := (94 + z * (83 + z * (71 + z * (34 + z * (63 + z * (64 + z * (52 + z * (63 + z * (11 + z * (126 + z * (79 + z * (8 + z * (46 + z * (113 + z * (77 + z * (134 + z * (121 + z * (128 + z * (31 + z * 60)))))))))))))))))))

def pow9_139_q {R : Type*} [CommRing R] (z : R) : R := (110 + z * (100 + z * (45 + z * (110 + z * (6 + z * (105 + z * (79 + z * (11 + z * (33 + z * (129 + z * (17 + z * (41 + z * (33 + z * (48 + z * (92 + z * (2 + z * (119 + z * (81 + z * 89))))))))))))))))))

def pow9_139_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-82) + z * ((-155) + z * ((-132) + z * ((-235) + z * ((-258) + z * ((-220) + z * ((-162) + z * ((-216) + z * ((-172) + z * ((-218) + z * ((-211) + z * ((-149) + z * ((-84) + z * ((-184) + z * ((-122) + z * ((-192) + z * ((-311) + z * ((-200) + z * ((-298) + z * ((-290) + z * ((-96) + z * ((-112) + z * ((-120) + z * (7 + z * ((-116) + z * ((-58) + z * ((-30) + z * ((-81) + z * (16 + z * ((-2) + z * ((-96) + z * ((-36) + z * ((-180) + z * ((-101) + z * ((-90) + z * ((-58) + z * ((-39) + z * ((-31) + z * 61))))))))))))))))))))))))))))))))))))))


abbrev u9 {R : Type*} [CommRing R] (z : R) : R := pow9_139 z

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


abbrev u18 {R : Type*} [CommRing R] (z : R) : R := pow18_139 z

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Powers10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139
def pow19_2 {R : Type*} [CommRing R] (z : R) : R := (3 + z * (51 + z * (73 + z * (77 + z * (15 + z * (121 + z * (90 + z * (94 + z * (69 + z * (21 + z * (21 + z * (113 + z * (100 + z * (101 + z * (52 + z * (54 + z * (135 + z * (127 + z * (126 + z * 87)))))))))))))))))))

def pow19_2_q {R : Type*} [CommRing R] (z : R) : R := (104 + z * (57 + z * (118 + z * (135 + z * (118 + z * (113 + z * (62 + z * (20 + z * (25 + z * (116 + z * (99 + z * (116 + z * (132 + z * (137 + z * (90 + z * (138 + z * (55 + z * (32 + z * 54))))))))))))))))))

def pow19_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (43 + z * ((-116) + z * ((-23) + z * ((-239) + z * ((-99) + z * ((-262) + z * ((-192) + z * ((-226) + z * ((-32) + z * ((-84) + z * ((-197) + z * ((-179) + z * ((-171) + z * ((-392) + z * ((-239) + z * ((-302) + z * ((-238) + z * ((-230) + z * ((-149) + z * ((-289) + z * ((-21) + z * ((-188) + z * ((-212) + z * ((-83) + z * ((-34) + z * ((-163) + z * (6 + z * (81 + z * ((-151) + z * ((-130) + z * (31 + z * ((-111) + z * ((-64) + z * (11 + z * (16 + z * (2 + z * (19 + z * (8 + z * 10))))))))))))))))))))))))))))))))))))))


def pow19_4 {R : Type*} [CommRing R] (z : R) : R := (48 + z * (47 + z * (66 + z * (32 + z * (126 + z * (130 + z * (110 + z * (31 + z * (27 + z * (78 + z * (103 + z * (47 + z * (110 + z * (28 + z * (1 + z * (8 + z * (25 + z * (44 + z * (97 + z * 117)))))))))))))))))))

def pow19_4_q {R : Type*} [CommRing R] (z : R) : R := (87 + z * (47 + z * (74 + z * (107 + z * (3 + z * (74 + z * (95 + z * (69 + z * (67 + z * (136 + z * (1 + z * (58 + z * (45 + z * (99 + z * (65 + z * (52 + z * (111 + z * (99 + z * 63))))))))))))))))))

def pow19_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-66) + z * ((-110) + z * ((-154) + z * ((-214) + z * ((-181) + z * ((-192) + z * ((-193) + z * ((-162) + z * ((-100) + z * ((-276) + z * ((-253) + z * ((-234) + z * ((-191) + z * ((-163) + z * ((-76) + z * ((-283) + z * ((-331) + z * ((-157) + z * ((-105) + z * ((-28) + z * (95 + z * (28 + z * (92 + z * (311 + z * (273 + z * (102 + z * (39 + z * (6 + z * (149 + z * (318 + z * (301 + z * (179 + z * (129 + z * (188 + z * (246 + z * (224 + z * (135 + z * (99 + z * 54))))))))))))))))))))))))))))))))))))))


def pow19_8 {R : Type*} [CommRing R] (z : R) : R := (57 + z * (70 + z * (106 + z * (96 + z * (65 + z * (15 + z * (27 + z * (60 + z * (95 + z * (137 + z * (111 + z * (126 + z * (100 + z * (2 + z * (63 + z * (82 + z * (78 + z * (41 + z * (112 + z * 62)))))))))))))))))))

def pow19_8_q {R : Type*} [CommRing R] (z : R) : R := (77 + z * (23 + z * (52 + z * (18 + z * (46 + z * (98 + z * (78 + z * (118 + z * (3 + z * (92 + z * (30 + z * (53 + z * (63 + z * (106 + z * (1 + z * (57 + z * (23 + z * (83 + z * 67))))))))))))))))))

def pow19_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-42) + z * ((-53) + z * ((-68) + z * ((-87) + z * ((-40) + z * ((-16) + z * (13 + z * ((-93) + z * ((-67) + z * ((-70) + z * (25 + z * (28 + z * ((-9) + z * ((-143) + z * ((-34) + z * ((-138) + z * ((-99) + z * ((-124) + z * ((-192) + z * ((-250) + z * ((-231) + z * ((-96) + z * ((-2) + z * (88 + z * (76 + z * ((-191) + z * ((-251) + z * ((-109) + z * ((-23) + z * (82 + z * (15 + z * ((-68) + z * ((-141) + z * ((-127) + z * ((-63) + z * (21 + z * (16 + z * (101 + z * 98))))))))))))))))))))))))))))))))))))))


def pow19_16 {R : Type*} [CommRing R] (z : R) : R := (61 + z * (23 + z * (52 + z * (49 + z * (30 + z * (134 + z * (23 + z * (90 + z * (87 + z * (124 + z * (96 + z * (67 + z * (20 + z * (64 + z * (126 + z * (48 + z * (96 + z * (15 + z * (136 + z * 134)))))))))))))))))))

def pow19_16_q {R : Type*} [CommRing R] (z : R) : R := (127 + z * (5 + z * (40 + z * (127 + z * (17 + z * (58 + z * (45 + z * (21 + z * (43 + z * (39 + z * (20 + z * (106 + z * (135 + z * (92 + z * (129 + z * (44 + z * (43 + z * (16 + z * 91))))))))))))))))))

def pow19_16_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-73) + z * ((-58) + z * ((-27) + z * ((-71) + z * ((-34) + z * ((-30) + z * ((-95) + z * ((-119) + z * ((-56) + z * ((-7) + z * (95 + z * (245 + z * (147 + z * ((-59) + z * ((-66) + z * ((-198) + z * ((-197) + z * (105 + z * (89 + z * (153 + z * (311 + z * (52 + z * (2 + z * (109 + z * (0 + z * (115 + z * (225 + z * (116 + z * (98 + z * (99 + z * (6 + z * ((-127) + z * ((-69) + z * (11 + z * (62 + z * (84 + z * (45 + z * (16 + z * 27))))))))))))))))))))))))))))))))))))))


def pow19_17 {R : Type*} [CommRing R] (z : R) : R := (130 + z * (46 + z * (3 + z * (138 + z * (110 + z * (38 + z * (135 + z * (86 + z * (46 + z * (90 + z * (57 + z * (5 + z * (98 + z * (36 + z * (14 + z * (94 + z * (79 + z * (81 + z * (15 + z * 52)))))))))))))))))))

def pow19_17_q {R : Type*} [CommRing R] (z : R) : R := (114 + z * (2 + z * (73 + z * (79 + z * (63 + z * (97 + z * (71 + z * (7 + z * (108 + z * (9 + z * (84 + z * (112 + z * (107 + z * (58 + z * (12 + z * (10 + z * (52 + z * (46 + z * 88))))))))))))))))))

def pow19_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-30) + z * ((-76) + z * ((-60) + z * ((-143) + z * ((-133) + z * ((-65) + z * ((-212) + z * ((-64) + z * ((-134) + z * (7 + z * ((-83) + z * ((-24) + z * ((-161) + z * ((-157) + z * ((-18) + z * ((-112) + z * (39 + z * (114 + z * (81 + z * (63 + z * (119 + z * (5 + z * (178 + z * (329 + z * (118 + z * (194 + z * (108 + z * (128 + z * (221 + z * (144 + z * (140 + z * (71 + z * (125 + z * (170 + z * (194 + z * (68 + z * (14 + z * (58 + z * 36))))))))))))))))))))))))))))))))))))))


def pow19_34 {R : Type*} [CommRing R] (z : R) : R := (128 + z * (104 + z * (104 + z * (74 + z * (66 + z * (16 + z * (1 + z * (86 + z * (109 + z * (51 + z * (24 + z * (66 + z * (105 + z * (50 + z * (129 + z * (80 + z * (17 + z * (32 + z * (50 + z * 108)))))))))))))))))))

def pow19_34_q {R : Type*} [CommRing R] (z : R) : R := (30 + z * (86 + z * (116 + z * (82 + z * (130 + z * (134 + z * (87 + z * (124 + z * (127 + z * (21 + z * (60 + z * (71 + z * (48 + z * (72 + z * (122 + z * (66 + z * (40 + z * (29 + z * 63))))))))))))))))))

def pow19_34_mul_t {R : Type*} [CommRing R] (z : R) : R := (98 + z * ((-6) + z * ((-170) + z * ((-10) + z * ((-83) + z * ((-326) + z * ((-86) + z * ((-90) + z * ((-331) + z * ((-102) + z * ((-100) + z * ((-372) + z * ((-79) + z * ((-125) + z * ((-517) + z * ((-255) + z * ((-210) + z * ((-471) + z * ((-315) + z * ((-118) + z * ((-372) + z * ((-302) + z * ((-135) + z * ((-297) + z * ((-248) + z * ((-93) + z * ((-255) + z * ((-209) + z * ((-94) + z * ((-114) + z * ((-158) + z * ((-45) + z * ((-50) + z * ((-103) + z * ((-9) + z * (18 + z * ((-11) + z * ((-47) + z * 19))))))))))))))))))))))))))))))))))))))


def pow19_68 {R : Type*} [CommRing R] (z : R) : R := (35 + z * (123 + z * (75 + z * (82 + z * (9 + z * (20 + z * (113 + z * (88 + z * (64 + z * (35 + z * (136 + z * (122 + z * (16 + z * (3 + z * (73 + z * (65 + z * (51 + z * (38 + z * (73 + z * 43)))))))))))))))))))

def pow19_68_q {R : Type*} [CommRing R] (z : R) : R := (22 + z * (64 + z * (66 + z * (37 + z * (126 + z * (129 + z * (50 + z * (79 + z * (133 + z * (122 + z * (1 + z * (5 + z * (123 + z * (22 + z * (68 + z * (49 + z * (104 + z * (104 + z * 127))))))))))))))))))

def pow19_68_mul_t {R : Type*} [CommRing R] (z : R) : R := (101 + z * (123 + z * (143 + z * (127 + z * (45 + z * ((-122) + z * ((-215) + z * ((-169) + z * ((-139) + z * ((-169) + z * ((-181) + z * ((-146) + z * ((-112) + z * ((-140) + z * ((-40) + z * (24 + z * ((-81) + z * ((-343) + z * ((-442) + z * ((-193) + z * ((-283) + z * ((-238) + z * ((-186) + z * ((-209) + z * ((-332) + z * ((-259) + z * ((-6) + z * ((-167) + z * ((-148) + z * (55 + z * ((-76) + z * ((-121) + z * ((-68) + z * ((-1) + z * ((-84) + z * ((-123) + z * ((-122) + z * ((-40) + z * 83))))))))))))))))))))))))))))))))))))))


def pow19_69 {R : Type*} [CommRing R] (z : R) : R := (121 + z * (109 + z * (120 + z * (83 + z * (96 + z * (23 + z * (17 + z * (113 + z * (97 + z * (28 + z * (15 + z * (82 + z * (12 + z * (14 + z * (15 + z * (53 + z * (85 + z * (74 + z * (115 + z * 70)))))))))))))))))))

def pow19_69_q {R : Type*} [CommRing R] (z : R) : R := (21 + z * (109 + z * (5 + z * (17 + z * (35 + z * (29 + z * (101 + z * (105 + z * (112 + z * (49 + z * (116 + z * (53 + z * (3 + z * (63 + z * (34 + z * (89 + z * (135 + z * (8 + z * 105))))))))))))))))))

def pow19_69_mul_t {R : Type*} [CommRing R] (z : R) : R := (16 + z * (16 + z * ((-12) + z * (59 + z * ((-10) + z * (87 + z * (99 + z * ((-17) + z * ((-115) + z * ((-118) + z * ((-28) + z * ((-34) + z * (70 + z * (14 + z * (3 + z * (80 + z * ((-97) + z * ((-154) + z * (17 + z * ((-54) + z * ((-128) + z * (26 + z * (40 + z * ((-72) + z * ((-96) + z * ((-106) + z * ((-79) + z * ((-14) + z * ((-78) + z * ((-68) + z * (58 + z * ((-127) + z * ((-64) + z * (21 + z * ((-114) + z * ((-49) + z * ((-15) + z * ((-44) + z * 11))))))))))))))))))))))))))))))))))))))


def pow19_138 {R : Type*} [CommRing R] (z : R) : R := (128 + z * (77 + z * (67 + z * (14 + z * (71 + z * (65 + z * (45 + z * (126 + z * (111 + z * (28 + z * (64 + z * (46 + z * (104 + z * (33 + z * (118 + z * (3 + z * (105 + z * (87 + z * (137 + z * 100)))))))))))))))))))

def pow19_138_q {R : Type*} [CommRing R] (z : R) : R := (76 + z * (2 + z * (58 + z * (42 + z * (70 + z * (116 + z * (34 + z * (86 + z * (17 + z * (23 + z * (23 + z * (77 + z * (65 + z * (76 + z * (75 + z * (45 + z * (78 + z * (83 + z * 35))))))))))))))))))

def pow19_138_mul_t {R : Type*} [CommRing R] (z : R) : R := (47 + z * (121 + z * (180 + z * (176 + z * (197 + z * (67 + z * ((-22) + z * (18 + z * (108 + z * (81 + z * (47 + z * (128 + z * ((-44) + z * ((-227) + z * ((-266) + z * ((-198) + z * ((-187) + z * ((-153) + z * (9 + z * (111 + z * ((-50) + z * ((-150) + z * ((-49) + z * ((-155) + z * ((-157) + z * ((-61) + z * ((-65) + z * ((-108) + z * ((-119) + z * ((-117) + z * ((-173) + z * ((-155) + z * ((-111) + z * ((-1) + z * (105 + z * (75 + z * (67 + z * (83 + z * 35))))))))))))))))))))))))))))))))))))))


abbrev pow19_139 {R : Type*} [CommRing R] (z : R) : R := u0 z

def pow19_139_q {R : Type*} [CommRing R] (z : R) : R := (132 + z * (113 + z * (84 + z * (90 + z * (97 + z * (114 + z * (3 + z * (97 + z * (33 + z * (100 + z * (76 + z * (99 + z * (94 + z * (13 + z * (49 + z * (96 + z * (82 + z * (60 + z * 47))))))))))))))))))

def pow19_139_mul_t {R : Type*} [CommRing R] (z : R) : R := (20 + z * ((-120) + z * ((-110) + z * ((-239) + z * ((-163) + z * ((-218) + z * ((-165) + z * ((-179) + z * ((-119) + z * ((-134) + z * ((-183) + z * ((-226) + z * ((-98) + z * ((-299) + z * ((-156) + z * ((-228) + z * (22 + z * ((-181) + z * ((-96) + z * ((-157) + z * ((-76) + z * ((-12) + z * (133 + z * (114 + z * ((-6) + z * ((-22) + z * (134 + z * (82 + z * (100 + z * (101 + z * (70 + z * (34 + z * (171 + z * (90 + z * (97 + z * (62 + z * (48 + z * (70 + z * 27))))))))))))))))))))))))))))))))))))))


abbrev u19 {R : Type*} [CommRing R] (z : R) : R := u0 z

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

def separable_bezout_t {R : Type*} [CommRing R] (z : R) : R := (126 + z * (163 + z * (282 + z * (341 + z * (498 + z * (474 + z * (548 + z * (570 + z * (721 + z * (835 + z * (915 + z * (1075 + z * (1033 + z * (1137 + z * (1325 + z * (1241 + z * (1352 + z * (1485 + z * (1571 + z * (1372 + z * (1481 + z * (1296 + z * (1184 + z * (1208 + z * (1034 + z * (914 + z * (902 + z * (984 + z * (703 + z * (675 + z * (539 + z * (476 + z * (493 + z * (354 + z * (269 + z * (155 + z * (178 + z * (149 + z * 13))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.SecretKey_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ZeroKey

section

open Matrix MeasureTheory ProbabilityTheory Filter

section

universe u

structure QuantumMemory where
  Carrier : Type u
  additive : AddCommGroup Carrier
  complexModule : Module ℂ Carrier
  unit : One Carrier
  order : LE Carrier

attribute [instance] QuantumMemory.additive QuantumMemory.complexModule QuantumMemory.unit QuantumMemory.order

end

open Matrix MeasureTheory ProbabilityTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

universe u

end

open Matrix MeasureTheory ProbabilityTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

universe u

end ZeroKey

end

end OAI
end


