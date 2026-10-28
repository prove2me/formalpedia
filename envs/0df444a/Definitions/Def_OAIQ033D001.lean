-- Prove2me | Definitions.Def_OAIQ033D001
-- name    : OAIQ033D001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T01:45:44.687158+00:00
-- url     : https://prove2.me/theorems/eee62099-2895-47c5-baf2-8daa35150745
-- title:
--   Definitions bundle OAIQ033D001 of the split of OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DimensionTen.main_pair`, carved from OpenAI's openai/math development (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 199 declarations of OpenAI's Lean: 197 definitions and 2 theorems. The definitions and types are `OAI.DimensionTen.Border.W0`, `OAI.DimensionTen.Border.W2`, `OAI.DimensionTen.Border.W20`, `OAI.DimensionTen.Mod41.a10`, `OAI.DimensionTen.Mod41.b10`, `OAI.DimensionTen.Mod41.bezout10_t`, `OAI.DimensionTen.Mod41.pow10_10`, `OAI.DimensionTen.Mod41.pow10_10_mul_t`, `OAI.DimensionTen.Mod41.pow10_10_q`, `OAI.DimensionTen.Mod41.pow10_2`, `OAI.DimensionTen.Mod41.pow10_20`, `OAI.DimensionTen.Mod41.pow10_20_mul_t`, `OAI.DimensionTen.Mod41.pow10_20_q`, `OAI.DimensionTen.Mod41.pow10_2_mul_t`, `OAI.DimensionTen.Mod41.pow10_2_q`, `OAI.DimensionTen.Mod41.pow10_4`, `OAI.DimensionTen.Mod41.pow10_40`, `OAI.DimensionTen.Mod41.pow10_40_mul_t`, `OAI.DimensionTen.Mod41.pow10_40_q`, `OAI.DimensionTen.Mod41.pow10_41`, `OAI.DimensionTen.Mod41.pow10_41_mul_t`, `OAI.DimensionTen.Mod41.pow10_41_q`, `OAI.DimensionTen.Mod41.pow10_4_mul_t`, `OAI.DimensionTen.Mod41.pow10_4_q`, `OAI.DimensionTen.Mod41.pow10_5`, `OAI.DimensionTen.Mod41.pow10_5_mul_t`, `OAI.DimensionTen.Mod41.pow10_5_q`, `OAI.DimensionTen.Mod41.pow11_10`, `OAI.DimensionTen.Mod41.pow11_10_mul_t`, `OAI.DimensionTen.Mod41.pow11_10_q`, `OAI.DimensionTen.Mod41.pow11_2`, `OAI.DimensionTen.Mod41.pow11_20`, `OAI.DimensionTen.Mod41.pow11_20_mul_t`, `OAI.DimensionTen.Mod41.pow11_20_q`, `OAI.DimensionTen.Mod41.pow11_2_mul_t`, `OAI.DimensionTen.Mod41.pow11_2_q`, `OAI.DimensionTen.Mod41.pow11_4`, `OAI.DimensionTen.Mod41.pow11_40`, `OAI.DimensionTen.Mod41.pow11_40_mul_t`, `OAI.DimensionTen.Mod41.pow11_40_q` and 157 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Quantum/DimensionTen, in whole or in part: [`Quantum_DimensionTen_Mod41Powers02`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod41Powers02.lean), [`Quantum_DimensionTen_Mod41Powers03`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod41Powers03.lean), [`Quantum_DimensionTen_Mod41Powers04`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod41Powers04.lean), [`Quantum_DimensionTen_Mod41Powers05`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod41Powers05.lean), [`Quantum_DimensionTen_Mod41Powers06`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod41Powers06.lean), [`Quantum_DimensionTen_Mod41Powers07`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod41Powers07.lean), [`Quantum_DimensionTen_Mod41Result`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod41Result.lean), [`Quantum_DimensionTen_PolynomialData`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/PolynomialData.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ033D010` and `OAIQ033D011`.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Quantum/DimensionTen at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod41Powers02
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41

def pow4_20_q {R : Type*} [CommRing R] (z : R) : R := (35 + z * (24 + z * (28 + z * (2 + z * (25 + z * (37 + z * (13 + z * (33 + z * (1 + z * (29 + z * (25 + z * (9 + z * (20 + z * (40 + z * (11 + z * (22 + z * (24 + z * (34 + z * 21))))))))))))))))))

def pow4_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-11) + z * (15 + z * ((-12) + z * (19 + z * ((-34) + z * ((-24) + z * ((-11) + z * ((-17) + z * (11 + z * ((-55) + z * (0 + z * ((-66) + z * (15 + z * ((-20) + z * ((-8) + z * ((-74) + z * ((-91) + z * ((-101) + z * ((-34) + z * ((-46) + z * ((-84) + z * ((-96) + z * ((-69) + z * ((-63) + z * ((-58) + z * ((-57) + z * ((-50) + z * ((-74) + z * ((-73) + z * ((-45) + z * ((-26) + z * ((-49) + z * ((-82) + z * ((-54) + z * ((-34) + z * ((-19) + z * ((-13) + z * ((-8) + z * 3))))))))))))))))))))))))))))))))))))))

def pow4_40_q {R : Type*} [CommRing R] (z : R) : R := (6 + z * (8 + z * (38 + z * (28 + z * (8 + z * (3 + z * (27 + z * (33 + z * (37 + z * (4 + z * (18 + z * (37 + z * (25 + z * (35 + z * (40 + z * (5 + z * (19 + z * (36 + z * 18))))))))))))))))))

def pow4_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (19 + z * (50 + z * (44 + z * (41 + z * (10 + z * (25 + z * (22 + z * (57 + z * (43 + z * (46 + z * (31 + z * (30 + z * (8 + z * ((-40) + z * ((-71) + z * ((-32) + z * ((-20) + z * ((-44) + z * ((-105) + z * ((-26) + z * ((-12) + z * ((-111) + z * ((-94) + z * ((-86) + z * ((-58) + z * ((-91) + z * ((-56) + z * ((-88) + z * ((-83) + z * ((-87) + z * ((-80) + z * ((-95) + z * ((-53) + z * ((-79) + z * (8 + z * ((-33) + z * (13 + z * ((-8) + z * 23))))))))))))))))))))))))))))))))))))))

def pow4_41_q {R : Type*} [CommRing R] (z : R) : R := (29 + z * (25 + z * (40 + z * (29 + z * (37 + z * (22 + z * (10 + z * (28 + z * (20 + z * (39 + z * (6 + z * (5 + z * (5 + z * (17 + z * (18 + z * (23 + z * (40 + z * (33 + z * 28))))))))))))))))))

def pow4_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-1) + z * (7 + z * ((-3) + z * (19 + z * ((-7) + z * (2 + z * (12 + z * (10 + z * (28 + z * (7 + z * (58 + z * (41 + z * (34 + z * (61 + z * (59 + z * (40 + z * ((-6) + z * (7 + z * ((-40) + z * (13 + z * ((-35) + z * (23 + z * ((-13) + z * ((-6) + z * ((-30) + z * ((-5) + z * (9 + z * (13 + z * ((-29) + z * (5 + z * ((-11) + z * ((-35) + z * ((-56) + z * ((-55) + z * ((-50) + z * ((-28) + z * ((-22) + z * ((-13) + z * 4))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod41Powers03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41
def pow5_2 {R : Type*} [CommRing R] (z : R) : R := (11 + z * (29 + z * (19 + z * (32 + z * (31 + z * (11 + z * (22 + z * (7 + z * (1 + z * (40 + z * (5 + z * (23 + z * (37 + z * (39 + z * (6 + z * (35 + z * (39 + z * (20 + z * (13 + z * 28)))))))))))))))))))

def pow5_2_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (38 + z * (39 + z * (10 + z * (19 + z * (27 + z * (29 + z * (4 + z * (14 + z * (13 + z * (28 + z * (38 + z * (23 + z * (3 + z * (35 + z * (7 + z * (15 + z * (23 + z * 33))))))))))))))))))

def pow5_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-31) + z * ((-40) + z * ((-70) + z * ((-38) + z * ((-57) + z * ((-34) + z * ((-28) + z * ((-17) + z * ((-20) + z * ((-2) + z * (8 + z * (28 + z * ((-5) + z * (6 + z * (19 + z * (24 + z * (14 + z * (32 + z * (14 + z * (59 + z * (76 + z * (105 + z * (145 + z * (165 + z * (143 + z * (85 + z * (79 + z * (68 + z * (72 + z * (74 + z * (65 + z * (63 + z * (70 + z * (48 + z * (56 + z * (49 + z * (39 + z * (15 + z * 11))))))))))))))))))))))))))))))))))))))


def pow5_4 {R : Type*} [CommRing R] (z : R) : R := (18 + z * (25 + z * (1 + z * (23 + z * (22 + z * (17 + z * (34 + z * (9 + z * (16 + z * (35 + z * (24 + z * (24 + z * (14 + z * (21 + z * (9 + z * (21 + z * (30 + z * (25 + z * (6 + z * 9)))))))))))))))))))

def pow5_4_q {R : Type*} [CommRing R] (z : R) : R := (4 + z * (19 + z * (35 + z * (5 + z * (5 + z * (28 + z * (34 + z * (0 + z * (1 + z * (39 + z * (17 + z * (39 + z * (33 + z * (36 + z * (2 + z * (13 + z * (18 + z * (4 + z * 5))))))))))))))))))

def pow5_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-1) + z * ((-3) + z * ((-9) + z * (14 + z * (35 + z * (33 + z * (8 + z * (50 + z * (22 + z * ((-17) + z * (21 + z * ((-19) + z * (25 + z * ((-9) + z * (56 + z * (82 + z * (61 + z * (42 + z * (102 + z * (91 + z * (36 + z * (59 + z * (96 + z * (13 + z * (43 + z * (66 + z * (28 + z * (20 + z * (88 + z * (47 + z * (45 + z * (77 + z * (72 + z * (43 + z * (59 + z * (48 + z * (26 + z * (14 + z * 19))))))))))))))))))))))))))))))))))))))


def pow5_5 {R : Type*} [CommRing R] (z : R) : R := (13 + z * (26 + z * (29 + z * (37 + z * (16 + z * (21 + z * (12 + z * (18 + z * (5 + z * (11 + z * (37 + z * (36 + z * (22 + z * (18 + z * (4 + z * (40 + z * (16 + z * (30 + z * (8 + z * 17)))))))))))))))))))

def pow5_5_q {R : Type*} [CommRing R] (z : R) : R := (25 + z * (28 + z * (1 + z * (8 + z * (17 + z * (8 + z * (5 + z * (3 + z * (3 + z * (32 + z * (24 + z * (33 + z * (32 + z * (17 + z * (2 + z * (16 + z * (12 + z * (19 + z * 34))))))))))))))))))

def pow5_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-17) + z * ((-21) + z * ((-20) + z * ((-12) + z * ((-5) + z * (1 + z * (44 + z * (32 + z * (21 + z * (43 + z * (44 + z * (27 + z * (31 + z * (27 + z * (81 + z * (61 + z * (61 + z * (72 + z * (59 + z * (63 + z * (70 + z * (126 + z * (100 + z * (101 + z * (84 + z * (37 + z * (27 + z * (41 + z * (15 + z * (7 + z * (24 + z * (22 + z * (13 + z * (15 + z * (15 + z * (13 + z * ((-2) + z * ((-14) + z * 4))))))))))))))))))))))))))))))))))))))


def pow5_10 {R : Type*} [CommRing R] (z : R) : R := (27 + z * (39 + z * (12 + z * (34 + z * (7 + z * (23 + z * (1 + z * (25 + z * (27 + z * (20 + z * (3 + z * (7 + z * (26 + z * (31 + z * (20 + z * (0 + z * (23 + z * (5 + z * (13 + z * 26)))))))))))))))))))

def pow5_10_q {R : Type*} [CommRing R] (z : R) : R := (29 + z * (30 + z * (34 + z * (33 + z * (27 + z * (9 + z * (17 + z * (0 + z * (28 + z * (7 + z * (37 + z * (26 + z * (33 + z * (25 + z * (1 + z * (13 + z * (20 + z * (7 + z * 2))))))))))))))))))

def pow5_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-22) + z * ((-20) + z * ((-26) + z * ((-3) + z * ((-5) + z * (17 + z * (21 + z * (18 + z * ((-15) + z * (0 + z * ((-35) + z * ((-2) + z * ((-4) + z * (41 + z * (28 + z * (5 + z * (14 + z * ((-2) + z * (32 + z * ((-16) + z * (31 + z * (35 + z * (56 + z * (1 + z * (5 + z * (19 + z * (31 + z * (5 + z * (29 + z * (6 + z * (33 + z * ((-6) + z * (31 + z * (17 + z * (38 + z * (6 + z * (20 + z * (5 + z * 7))))))))))))))))))))))))))))))))))))))


def pow5_20 {R : Type*} [CommRing R] (z : R) : R := (32 + z * (1 + z * (28 + z * (37 + z * (29 + z * (8 + z * (21 + z * (8 + z * (15 + z * (35 + z * (9 + z * (6 + z * (35 + z * (25 + z * (34 + z * (32 + z * (27 + z * (13 + z * (9 + z * 13)))))))))))))))))))

def pow5_20_q {R : Type*} [CommRing R] (z : R) : R := (0 + z * (30 + z * (27 + z * (23 + z * (17 + z * (8 + z * (28 + z * (28 + z * (39 + z * (31 + z * (6 + z * (18 + z * (24 + z * (29 + z * (21 + z * (32 + z * (23 + z * (35 + z * 20))))))))))))))))))

def pow5_20_mul_t {R : Type*} [CommRing R] (z : R) : R := (17 + z * (25 + z * (19 + z * (16 + z * (34 + z * (10 + z * (12 + z * ((-2) + z * (18 + z * ((-5) + z * (5 + z * ((-29) + z * ((-1) + z * ((-9) + z * (20 + z * ((-33) + z * ((-36) + z * ((-64) + z * ((-103) + z * ((-44) + z * ((-52) + z * ((-29) + z * ((-78) + z * ((-102) + z * ((-89) + z * ((-84) + z * ((-48) + z * ((-63) + z * ((-73) + z * ((-69) + z * ((-56) + z * ((-55) + z * ((-45) + z * ((-57) + z * ((-54) + z * ((-11) + z * ((-24) + z * (1 + z * 16))))))))))))))))))))))))))))))))))))))


def pow5_40 {R : Type*} [CommRing R] (z : R) : R := (14 + z * (4 + z * (21 + z * (27 + z * (36 + z * (31 + z * (32 + z * (22 + z * (1 + z * (40 + z * (32 + z * (14 + z * (14 + z * (17 + z * (8 + z * (39 + z * (30 + z * (19 + z * (34 + z * 15)))))))))))))))))))

def pow5_40_q {R : Type*} [CommRing R] (z : R) : R := (3 + z * (4 + z * (2 + z * (26 + z * (15 + z * (38 + z * (36 + z * (36 + z * (40 + z * (7 + z * (3 + z * (38 + z * (28 + z * (9 + z * (12 + z * (29 + z * (28 + z * (2 + z * 5))))))))))))))))))

def pow5_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (22 + z * ((-3) + z * (38 + z * (32 + z * (40 + z * (3 + z * (48 + z * ((-18) + z * ((-6) + z * (32 + z * ((-11) + z * (1 + z * (40 + z * (8 + z * (32 + z * (36 + z * (52 + z * (72 + z * (72 + z * (21 + z * ((-3) + z * (32 + z * ((-44) + z * ((-46) + z * ((-8) + z * (3 + z * ((-13) + z * (4 + z * (59 + z * (38 + z * (6 + z * (15 + z * (13 + z * (10 + z * ((-2) + z * ((-2) + z * (6 + z * (2 + z * 4))))))))))))))))))))))))))))))))))))))


def pow5_41 {R : Type*} [CommRing R] (z : R) : R := (23 + z * (27 + z * (33 + z * (10 + z * (7 + z * (20 + z * (9 + z * (5 + z * (10 + z * (21 + z * (32 + z * (35 + z * (17 + z * (32 + z * (1 + z * (24 + z * (30 + z * (12 + z * (4 + z * 21)))))))))))))))))))

def pow5_41_q {R : Type*} [CommRing R] (z : R) : R := (12 + z * (29 + z * (18 + z * (36 + z * (36 + z * (38 + z * (17 + z * (34 + z * (14 + z * (26 + z * (40 + z * (36 + z * (19 + z * (27 + z * (23 + z * (33 + z * (40 + z * (13 + z * 2))))))))))))))))))

def pow5_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-7) + z * ((-25) + z * ((-26) + z * ((-39) + z * ((-37) + z * ((-50) + z * ((-10) + z * ((-25) + z * (2 + z * (2 + z * (26 + z * ((-19) + z * ((-15) + z * ((-3) + z * ((-3) + z * (1 + z * ((-12) + z * ((-10) + z * ((-15) + z * (10 + z * (36 + z * (71 + z * (47 + z * (58 + z * (44 + z * (20 + z * (11 + z * (15 + z * (23 + z * (20 + z * (3 + z * (3 + z * (21 + z * (48 + z * (46 + z * (34 + z * (42 + z * (30 + z * 8))))))))))))))))))))))))))))))))))))))


abbrev u5 {R : Type*} [CommRing R] (z : R) : R := pow5_41 z


def pow6_2 {R : Type*} [CommRing R] (z : R) : R := (28 + z * (29 + z * (33 + z * (21 + z * (21 + z * (30 + z * (33 + z * (2 + z * (0 + z * (10 + z * (14 + z * (38 + z * (36 + z * (33 + z * (38 + z * (34 + z * (17 + z * (32 + z * (35 + z * 2)))))))))))))))))))

def pow6_2_q {R : Type*} [CommRing R] (z : R) : R := (31 + z * (2 + z * (19 + z * (17 + z * (12 + z * (33 + z * (34 + z * (31 + z * (32 + z * (1 + z * (13 + z * (11 + z * (19 + z * (37 + z * (1 + z * (38 + z * (16 + z * (17 + z * 31))))))))))))))))))

def pow6_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * (18 + z * (14 + z * (31 + z * ((-7) + z * ((-4) + z * ((-16) + z * ((-50) + z * ((-49) + z * ((-31) + z * ((-7) + z * (38 + z * (21 + z * (23 + z * ((-8) + z * ((-38) + z * ((-8) + z * ((-43) + z * ((-17) + z * ((-57) + z * ((-32) + z * (4 + z * ((-66) + z * ((-50) + z * ((-32) + z * ((-31) + z * (3 + z * ((-14) + z * (13 + z * ((-13) + z * ((-21) + z * ((-31) + z * ((-27) + z * ((-44) + z * ((-35) + z * ((-4) + z * ((-13) + z * ((-19) + z * 10))))))))))))))))))))))))))))))))))))))


def pow6_4 {R : Type*} [CommRing R] (z : R) : R := (22 + z * (6 + z * (3 + z * (6 + z * (26 + z * (35 + z * (21 + z * (3 + z * (40 + z * (10 + z * (16 + z * (28 + z * (7 + z * (26 + z * (2 + z * (11 + z * (10 + z * (11 + z * (5 + z * 32)))))))))))))))))))

def pow6_4_q {R : Type*} [CommRing R] (z : R) : R := (28 + z * (28 + z * (7 + z * (26 + z * (13 + z * (16 + z * (10 + z * (28 + z * (23 + z * (3 + z * (16 + z * (35 + z * (16 + z * (25 + z * (31 + z * (22 + z * (29 + z * (20 + z * 4))))))))))))))))))

def pow6_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-6) + z * (6 + z * (30 + z * (29 + z * (37 + z * (41 + z * (98 + z * (35 + z * (10 + z * (9 + z * (6 + z * (19 + z * (47 + z * (77 + z * (83 + z * (86 + z * (112 + z * (138 + z * (111 + z * (94 + z * (90 + z * (45 + z * (27 + z * (68 + z * (57 + z * (33 + z * (49 + z * (63 + z * (91 + z * (102 + z * (63 + z * (51 + z * (41 + z * (20 + z * (14 + z * (24 + z * (16 + z * (0 + z * 0))))))))))))))))))))))))))))))))))))))


def pow6_5 {R : Type*} [CommRing R] (z : R) : R := (1 + z * (19 + z * (23 + z * (15 + z * (7 + z * (30 + z * (31 + z * (21 + z * (9 + z * (20 + z * (11 + z * (1 + z * (17 + z * (19 + z * (12 + z * (8 + z * (17 + z * (31 + z * (11 + z * 40)))))))))))))))))))

def pow6_5_q {R : Type*} [CommRing R] (z : R) : R := (22 + z * (13 + z * (20 + z * (10 + z * (27 + z * (7 + z * (10 + z * (10 + z * (40 + z * (37 + z * (5 + z * (9 + z * (23 + z * (19 + z * (17 + z * (39 + z * (24 + z * (40 + z * 16))))))))))))))))))

def pow6_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-7) + z * ((-1) + z * ((-15) + z * ((-10) + z * ((-33) + z * (18 + z * (16 + z * (10 + z * ((-26) + z * ((-18) + z * (12 + z * ((-8) + z * ((-26) + z * (8 + z * (0 + z * ((-31) + z * ((-46) + z * ((-59) + z * ((-38) + z * ((-61) + z * ((-29) + z * (19 + z * ((-41) + z * ((-54) + z * ((-37) + z * ((-68) + z * ((-51) + z * ((-55) + z * ((-54) + z * ((-30) + z * ((-33) + z * ((-76) + z * ((-52) + z * ((-72) + z * ((-42) + z * ((-13) + z * ((-21) + z * ((-7) + z * 16))))))))))))))))))))))))))))))))))))))


def pow6_10 {R : Type*} [CommRing R] (z : R) : R := (40 + z * (33 + z * (7 + z * (33 + z * (11 + z * (34 + z * (8 + z * (18 + z * (23 + z * (39 + z * (27 + z * (5 + z * (29 + z * (22 + z * (9 + z * (24 + z * (14 + z * (15 + z * (32 + z * 29)))))))))))))))))))

def pow6_10_q {R : Type*} [CommRing R] (z : R) : R := (16 + z * (16 + z * (33 + z * (19 + z * (26 + z * (20 + z * (12 + z * (9 + z * (16 + z * (0 + z * (4 + z * (16 + z * (1 + z * (14 + z * (0 + z * (25 + z * (3 + z * (30 + z * 1))))))))))))))))))

def pow6_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * ((-19) + z * ((-36) + z * ((-18) + z * ((-39) + z * ((-31) + z * ((-22) + z * (9 + z * (7 + z * ((-5) + z * (7 + z * (10 + z * ((-1) + z * ((-16) + z * (20 + z * ((-28) + z * ((-21) + z * ((-63) + z * (2 + z * ((-20) + z * (25 + z * (16 + z * (39 + z * (37 + z * (50 + z * (57 + z * (42 + z * (5 + z * (19 + z * (20 + z * (2 + z * (20 + z * (9 + z * (16 + z * (11 + z * (34 + z * (41 + z * (20 + z * 39))))))))))))))))))))))))))))))))))))))


def pow6_20 {R : Type*} [CommRing R] (z : R) : R := (38 + z * (17 + z * (9 + z * (12 + z * (33 + z * (1 + z * (35 + z * (28 + z * (34 + z * (27 + z * (2 + z * (9 + z * (21 + z * (19 + z * (23 + z * (23 + z * (17 + z * (22 + z * (24 + z * 2)))))))))))))))))))

def pow6_20_q {R : Type*} [CommRing R] (z : R) : R := (32 + z * (26 + z * (30 + z * (16 + z * (30 + z * (7 + z * (1 + z * (17 + z * (4 + z * (24 + z * (31 + z * (4 + z * (0 + z * (25 + z * (34 + z * (27 + z * (17 + z * (37 + z * 21))))))))))))))))))

def pow6_20_mul_t {R : Type*} [CommRing R] (z : R) : R := (10 + z * (31 + z * ((-18) + z * (32 + z * ((-4) + z * (43 + z * (47 + z * (13 + z * (61 + z * (60 + z * (98 + z * (8 + z * (84 + z * (100 + z * (28 + z * (46 + z * (24 + z * ((-2) + z * (56 + z * (72 + z * (51 + z * (28 + z * (75 + z * (54 + z * (36 + z * (5 + z * (20 + z * (64 + z * (27 + z * ((-30) + z * ((-4) + z * (6 + z * ((-39) + z * ((-34) + z * ((-4) + z * (3 + z * (10 + z * (29 + z * 20))))))))))))))))))))))))))))))))))))))


def pow6_40 {R : Type*} [CommRing R] (z : R) : R := (6 + z * (32 + z * (4 + z * (29 + z * (16 + z * (36 + z * (33 + z * (13 + z * (13 + z * (22 + z * (24 + z * (31 + z * (27 + z * (24 + z * (16 + z * (4 + z * (29 + z * (37 + z * (39 + z * 37)))))))))))))))))))

def pow6_40_q {R : Type*} [CommRing R] (z : R) : R := (24 + z * (40 + z * (5 + z * (20 + z * (0 + z * (27 + z * (37 + z * (38 + z * (23 + z * (20 + z * (1 + z * (9 + z * (29 + z * (7 + z * (28 + z * (8 + z * (4 + z * (17 + z * 4))))))))))))))))))

def pow6_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (14 + z * ((-12) + z * ((-11) + z * ((-20) + z * (43 + z * ((-39) + z * (32 + z * ((-1) + z * (22 + z * (7 + z * (18 + z * ((-6) + z * (28 + z * (37 + z * (8 + z * (50 + z * ((-9) + z * (10 + z * (33 + z * ((-6) + z * (16 + z * (29 + z * (13 + z * (6 + z * (13 + z * (4 + z * (15 + z * (8 + z * ((-18) + z * (9 + z * (19 + z * (7 + z * (18 + z * (4 + z * (13 + z * (15 + z * (2 + z * ((-1) + z * 0))))))))))))))))))))))))))))))))))))))


def pow6_41 {R : Type*} [CommRing R] (z : R) : R := (31 + z * (37 + z * (38 + z * (22 + z * (29 + z * (11 + z * (22 + z * (17 + z * (6 + z * (17 + z * (3 + z * (35 + z * (14 + z * (6 + z * (30 + z * (1 + z * (28 + z * (6 + z * (2 + z * 36)))))))))))))))))))

def pow6_41_q {R : Type*} [CommRing R] (z : R) : R := (36 + z * (28 + z * (0 + z * (31 + z * (18 + z * (12 + z * (31 + z * (39 + z * (9 + z * (9 + z * (19 + z * (23 + z * (36 + z * (5 + z * (0 + z * (29 + z * (39 + z * (2 + z * 39))))))))))))))))))

def pow6_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-29) + z * ((-15) + z * ((-8) + z * ((-3) + z * ((-15) + z * ((-2) + z * (30 + z * ((-31) + z * ((-27) + z * ((-5) + z * ((-5) + z * ((-14) + z * (6 + z * (35 + z * (12 + z * ((-19) + z * (1 + z * (7 + z * ((-5) + z * (20 + z * (16 + z * (70 + z * ((-6) + z * ((-13) + z * (37 + z * ((-6) + z * ((-17) + z * (26 + z * (58 + z * (48 + z * (19 + z * ((-7) + z * (10 + z * ((-2) + z * ((-4) + z * (5 + z * (15 + z * ((-5) + z * 18))))))))))))))))))))))))))))))))))))))


abbrev u6 {R : Type*} [CommRing R] (z : R) : R := pow6_41 z

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod41Powers04
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41
def pow7_2 {R : Type*} [CommRing R] (z : R) : R := (9 + z * (18 + z * (33 + z * (3 + z * (19 + z * (30 + z * (10 + z * (1 + z * (12 + z * (31 + z * (13 + z * (37 + z * (15 + z * (37 + z * (15 + z * (24 + z * (27 + z * (39 + z * (32 + z * 38)))))))))))))))))))

def pow7_2_q {R : Type*} [CommRing R] (z : R) : R := (31 + z * (19 + z * (30 + z * (36 + z * (14 + z * (9 + z * (33 + z * (30 + z * (31 + z * (12 + z * (1 + z * (29 + z * (11 + z * (32 + z * (9 + z * (21 + z * (28 + z * (9 + z * 25))))))))))))))))))

def pow7_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-4) + z * (29 + z * (35 + z * (46 + z * (48 + z * (51 + z * (49 + z * (16 + z * (5 + z * (12 + z * ((-17) + z * (1 + z * (29 + z * ((-2) + z * (9 + z * ((-31) + z * ((-11) + z * ((-43) + z * ((-55) + z * ((-48) + z * ((-8) + z * ((-21) + z * ((-68) + z * ((-29) + z * ((-82) + z * ((-21) + z * ((-62) + z * ((-51) + z * ((-16) + z * ((-70) + z * (9 + z * ((-43) + z * ((-52) + z * (0 + z * ((-47) + z * (11 + z * ((-7) + z * ((-15) + z * 31))))))))))))))))))))))))))))))))))))))


def pow7_4 {R : Type*} [CommRing R] (z : R) : R := (27 + z * (26 + z * (13 + z * (34 + z * (5 + z * (36 + z * (19 + z * (32 + z * (7 + z * (7 + z * (18 + z * (29 + z * (24 + z * (35 + z * (3 + z * (34 + z * (18 + z * (39 + z * (18 + z * 12)))))))))))))))))))

def pow7_4_q {R : Type*} [CommRing R] (z : R) : R := (22 + z * (14 + z * (12 + z * (1 + z * (18 + z * (29 + z * (24 + z * (25 + z * (36 + z * (22 + z * (24 + z * (37 + z * (12 + z * (9 + z * (15 + z * (36 + z * (24 + z * (30 + z * 9))))))))))))))))))

def pow7_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-18) + z * ((-12) + z * ((-9) + z * (14 + z * ((-5) + z * ((-12) + z * (6 + z * ((-12) + z * ((-59) + z * ((-42) + z * ((-13) + z * ((-26) + z * ((-48) + z * (19 + z * (17 + z * ((-24) + z * ((-33) + z * ((-11) + z * (23 + z * (15 + z * (62 + z * (50 + z * (32 + z * (14 + z * (30 + z * ((-15) + z * (24 + z * (47 + z * (102 + z * (73 + z * (92 + z * (54 + z * (71 + z * (45 + z * (63 + z * (75 + z * (71 + z * (52 + z * 35))))))))))))))))))))))))))))))))))))))


def pow7_5 {R : Type*} [CommRing R] (z : R) : R := (22 + z * (30 + z * (3 + z * (37 + z * (35 + z * (28 + z * (36 + z * (17 + z * (37 + z * (21 + z * (33 + z * (23 + z * (40 + z * (30 + z * (33 + z * (13 + z * (12 + z * (14 + z * 30))))))))))))))))))

def pow7_5_q {R : Type*} [CommRing R] (z : R) : R := (1 + z * (33 + z * (16 + z * (1 + z * (32 + z * (8 + z * (0 + z * (19 + z * (18 + z * (38 + z * (16 + z * (28 + z * (14 + z * (12 + z * (19 + z * (39 + z * (40 + z * (12 + z * 22))))))))))))))))))

def pow7_5_mul_t {R : Type*} [CommRing R] (z : R) : R := (19 + z * (14 + z * (33 + z * (45 + z * (37 + z * (51 + z * (57 + z * (102 + z * (30 + z * (24 + z * (38 + z * (16 + z * (46 + z * (45 + z * (87 + z * (9 + z * (7 + z * (58 + z * ((-2) + z * (63 + z * ((-22) + z * (43 + z * (8 + z * ((-48) + z * (3 + z * ((-56) + z * ((-35) + z * ((-43) + z * ((-40) + z * ((-8) + z * ((-47) + z * ((-22) + z * ((-31) + z * ((-39) + z * ((-21) + z * ((-19) + z * (18 + z * (0 + z * 10))))))))))))))))))))))))))))))))))))))


def pow7_10 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (24 + z * (28 + z * (2 + z * (32 + z * (11 + z * (33 + z * (17 + z * (11 + z * (2 + z * (30 + z * (22 + z * (25 + z * (37 + z * (28 + z * (3 + z * (39 + z * (1 + z * (26 + z * 8)))))))))))))))))))

def pow7_10_q {R : Type*} [CommRing R] (z : R) : R := (19 + z * (28 + z * (27 + z * (12 + z * (24 + z * (23 + z * (31 + z * (9 + z * (39 + z * (12 + z * (11 + z * (1 + z * (10 + z * (6 + z * (26 + z * (39 + z * 39))))))))))))))))

def pow7_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-5) + z * (1 + z * ((-22) + z * (4 + z * (31 + z * (25 + z * (40 + z * (74 + z * (37 + z * (100 + z * (75 + z * (138 + z * (116 + z * (165 + z * (168 + z * (128 + z * (98 + z * (130 + z * (168 + z * (122 + z * (102 + z * (135 + z * (124 + z * (63 + z * (94 + z * (62 + z * (89 + z * (40 + z * (69 + z * (27 + z * (15 + z * ((-16) + z * ((-8) + z * ((-30) + z * ((-23) + z * ((-9) + z * 21))))))))))))))))))))))))))))))))))))


def pow7_20 {R : Type*} [CommRing R] (z : R) : R := (13 + z * (32 + z * (8 + z * (34 + z * (27 + z * (11 + z * (5 + z * (13 + z * (10 + z * (39 + z * (20 + z * (26 + z * (31 + z * (31 + z * (20 + z * (33 + z * (37 + z * (8 + z * (35 + z * 36)))))))))))))))))))

def pow7_20_q {R : Type*} [CommRing R] (z : R) : R := (14 + z * (3 + z * (37 + z * (15 + z * (10 + z * (4 + z * (24 + z * (6 + z * (40 + z * (11 + z * (9 + z * (30 + z * (4 + z * (8 + z * (10 + z * (13 + z * (34 + z * (13 + z * 23))))))))))))))))))

def pow7_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-12) + z * ((-2) + z * ((-23) + z * (5 + z * ((-23) + z * (20 + z * (5 + z * (17 + z * (19 + z * ((-11) + z * ((-16) + z * (5 + z * (40 + z * (2 + z * (80 + z * (27 + z * (25 + z * (47 + z * (24 + z * (6 + z * (80 + z * ((-5) + z * (40 + z * (19 + z * (53 + z * ((-9) + z * (43 + z * ((-10) + z * (34 + z * (43 + z * (17 + z * ((-1) + z * (17 + z * ((-46) + z * (1 + z * ((-27) + z * ((-3) + z * ((-7) + z * 1))))))))))))))))))))))))))))))))))))))


def pow7_40 {R : Type*} [CommRing R] (z : R) : R := (20 + z * (39 + z * (21 + z * (34 + z * (21 + z * (3 + z * (2 + z * (30 + z * (12 + z * (29 + z * (0 + z * (20 + z * (34 + z * (29 + z * (9 + z * (18 + z * (12 + z * (29 + z * (17 + z * 29)))))))))))))))))))

def pow7_40_q {R : Type*} [CommRing R] (z : R) : R := (3 + z * (5 + z * (2 + z * (34 + z * (12 + z * (22 + z * (23 + z * (5 + z * (22 + z * (33 + z * (15 + z * (6 + z * (13 + z * (37 + z * (3 + z * (22 + z * (18 + z * (7 + z * 25))))))))))))))))))

def pow7_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (1 + z * (14 + z * (24 + z * ((-1) + z * (46 + z * (10 + z * (20 + z * (7 + z * (7 + z * (3 + z * (17 + z * (26 + z * (71 + z * (52 + z * (75 + z * (60 + z * (102 + z * (54 + z * (85 + z * (133 + z * (70 + z * (98 + z * (107 + z * (83 + z * (56 + z * (81 + z * (85 + z * (111 + z * (125 + z * (88 + z * (100 + z * (106 + z * (58 + z * (56 + z * (75 + z * (48 + z * (28 + z * (43 + z * 31))))))))))))))))))))))))))))))))))))))


def pow7_41 {R : Type*} [CommRing R] (z : R) : R := (26 + z * (28 + z * (6 + z * (7 + z * (30 + z * (2 + z * (32 + z * (18 + z * (16 + z * (25 + z * (39 + z * (7 + z * (0 + z * (39 + z * (6 + z * (27 + z * (28 + z * (15 + z * (9 + z * 3)))))))))))))))))))

def pow7_41_q {R : Type*} [CommRing R] (z : R) : R := (37 + z * (40 + z * (27 + z * (3 + z * (18 + z * (36 + z * (19 + z * (18 + z * (2 + z * (17 + z * (17 + z * (8 + z * (24 + z * (11 + z * (26 + z * (20 + z * (20 + z * (18 + z * 19))))))))))))))))))

def pow7_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-18) + z * (0 + z * (6 + z * (50 + z * (34 + z * (21 + z * (9 + z * (12 + z * (6 + z * ((-1) + z * (19 + z * (6 + z * (5 + z * (40 + z * (21 + z * (20 + z * ((-56) + z * ((-20) + z * ((-2) + z * (7 + z * (11 + z * ((-9) + z * ((-7) + z * (22 + z * ((-35) + z * ((-26) + z * (0 + z * ((-12) + z * (4 + z * ((-30) + z * ((-9) + z * ((-6) + z * ((-20) + z * ((-18) + z * ((-16) + z * (1 + z * (9 + z * (2 + z * 25))))))))))))))))))))))))))))))))))))))


abbrev u7 {R : Type*} [CommRing R] (z : R) : R := pow7_41 z


def pow8_2 {R : Type*} [CommRing R] (z : R) : R := (13 + z * (32 + z * (30 + z * (4 + z * (27 + z * (25 + z * (10 + z * (33 + z * (5 + z * (30 + z * (5 + z * (39 + z * (14 + z * (10 + z * (40 + z * (30 + z * (40 + z * (38 + z * (2 + z * 20)))))))))))))))))))

def pow8_2_q {R : Type*} [CommRing R] (z : R) : R := (15 + z * (33 + z * (20 + z * (40 + z * (0 + z * (36 + z * (11 + z * (23 + z * (14 + z * (40 + z * (37 + z * (3 + z * (31 + z * (13 + z * (22 + z * (23 + z * (20 + z * (30 + z * 9))))))))))))))))))

def pow8_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (3 + z * (1 + z * ((-13) + z * ((-49) + z * (8 + z * ((-44) + z * (11 + z * ((-20) + z * (9 + z * ((-50) + z * (16 + z * ((-9) + z * ((-68) + z * (3 + z * ((-11) + z * ((-14) + z * ((-27) + z * ((-35) + z * ((-78) + z * ((-24) + z * ((-54) + z * ((-69) + z * ((-28) + z * (8 + z * ((-75) + z * ((-43) + z * ((-16) + z * ((-63) + z * ((-55) + z * ((-41) + z * ((-26) + z * ((-38) + z * ((-33) + z * ((-36) + z * ((-28) + z * ((-22) + z * ((-22) + z * ((-6) + z * 0))))))))))))))))))))))))))))))))))))))


def pow8_4 {R : Type*} [CommRing R] (z : R) : R := (22 + z * (29 + z * (10 + z * (10 + z * (23 + z * (26 + z * (7 + z * (22 + z * (37 + z * (17 + z * (29 + z * (15 + z * (15 + z * (6 + z * (19 + z * (3 + z * (15 + z * (23 + z * (1 + z * 36)))))))))))))))))))

def pow8_4_q {R : Type*} [CommRing R] (z : R) : R := (28 + z * (27 + z * (27 + z * (40 + z * (18 + z * (32 + z * (2 + z * (11 + z * (38 + z * (1 + z * (22 + z * (15 + z * (10 + z * (30 + z * (31 + z * (30 + z * (11 + z * (11 + z * 31))))))))))))))))))

def pow8_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-21) + z * ((-13) + z * ((-9) + z * ((-15) + z * ((-26) + z * ((-25) + z * (34 + z * ((-14) + z * ((-3) + z * (18 + z * ((-25) + z * (29 + z * ((-14) + z * (30 + z * ((-8) + z * ((-15) + z * (74 + z * (8 + z * (69 + z * ((-4) + z * (37 + z * (76 + z * (0 + z * (72 + z * (35 + z * (34 + z * (63 + z * (17 + z * (82 + z * ((-14) + z * (55 + z * (64 + z * (19 + z * (38 + z * (10 + z * (12 + z * (16 + z * ((-21) + z * 9))))))))))))))))))))))))))))))))))))))


def pow8_5 {R : Type*} [CommRing R] (z : R) : R := (19 + z * (8 + z * (15 + z * (37 + z * (15 + z * (31 + z * (10 + z * (32 + z * (19 + z * (36 + z * (32 + z * (33 + z * (34 + z * (36 + z * (27 + z * (15 + z * (12 + z * (37 + z * (17 + z * 3)))))))))))))))))))

def pow8_5_q {R : Type*} [CommRing R] (z : R) : R := (37 + z * (37 + z * (23 + z * (0 + z * (25 + z * (8 + z * (35 + z * (35 + z * (40 + z * (35 + z * (26 + z * (24 + z * (7 + z * (12 + z * (37 + z * (27 + z * (31 + z * (39 + z * 26))))))))))))))))))

def pow8_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-19) + z * ((-11) + z * ((-30) + z * ((-15) + z * ((-25) + z * (8 + z * ((-22) + z * ((-16) + z * ((-50) + z * ((-29) + z * ((-18) + z * ((-30) + z * ((-37) + z * ((-28) + z * ((-7) + z * ((-77) + z * ((-92) + z * ((-75) + z * ((-86) + z * ((-97) + z * ((-44) + z * ((-74) + z * ((-98) + z * ((-49) + z * ((-97) + z * ((-101) + z * ((-80) + z * ((-57) + z * ((-84) + z * ((-54) + z * ((-64) + z * ((-83) + z * ((-49) + z * ((-81) + z * ((-40) + z * ((-23) + z * ((-25) + z * ((-12) + z * 2))))))))))))))))))))))))))))))))))))))


def pow8_10 {R : Type*} [CommRing R] (z : R) : R := (6 + z * (15 + z * (33 + z * (17 + z * (18 + z * (6 + z * (27 + z * (36 + z * (15 + z * (36 + z * (15 + z * (4 + z * (24 + z * (39 + z * (22 + z * (7 + z * (27 + z * (19 + z * (16 + z * 6)))))))))))))))))))

def pow8_10_q {R : Type*} [CommRing R] (z : R) : R := (11 + z * (20 + z * (6 + z * (17 + z * (12 + z * (15 + z * (35 + z * (35 + z * (38 + z * (13 + z * (12 + z * (2 + z * (34 + z * (17 + z * (23 + z * (12 + z * (27 + z * (37 + z * 9))))))))))))))))))

def pow8_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-1) + z * ((-14) + z * ((-5) + z * (8 + z * (4 + z * (15 + z * (13 + z * (6 + z * ((-5) + z * (23 + z * (47 + z * (59 + z * (79 + z * (97 + z * (94 + z * (97 + z * (85 + z * (97 + z * (100 + z * (88 + z * (130 + z * (100 + z * (105 + z * (62 + z * (62 + z * (60 + z * (79 + z * (55 + z * (40 + z * (40 + z * (39 + z * ((-10) + z * ((-31) + z * ((-37) + z * ((-3) + z * ((-8) + z * ((-19) + z * ((-5) + z * 0))))))))))))))))))))))))))))))))))))))


def pow8_20 {R : Type*} [CommRing R] (z : R) : R := (21 + z * (29 + z * (1 + z * (12 + z * (12 + z * (3 + z * (38 + z * (20 + z * (21 + z * (20 + z * (31 + z * (22 + z * (27 + z * (13 + z * (16 + z * (23 + z * (6 + z * (13 + z * (36 + z * 1)))))))))))))))))))

def pow8_20_q {R : Type*} [CommRing R] (z : R) : R := (38 + z * (3 + z * (38 + z * (11 + z * (25 + z * (30 + z * (38 + z * (9 + z * (21 + z * (37 + z * (31 + z * (23 + z * (16 + z * (21 + z * (4 + z * (29 + z * (26 + z * (14 + z * 36))))))))))))))))))

def pow8_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-33) + z * ((-11) + z * ((-47) + z * (4 + z * ((-39) + z * ((-8) + z * ((-45) + z * ((-32) + z * ((-6) + z * ((-9) + z * ((-22) + z * ((-14) + z * ((-27) + z * ((-34) + z * (12 + z * (10 + z * ((-6) + z * ((-66) + z * ((-32) + z * ((-15) + z * ((-25) + z * ((-22) + z * ((-14) + z * ((-15) + z * ((-45) + z * ((-29) + z * ((-10) + z * ((-37) + z * ((-42) + z * ((-28) + z * ((-9) + z * ((-17) + z * ((-36) + z * ((-36) + z * ((-37) + z * ((-23) + z * ((-14) + z * ((-22) + z * 0))))))))))))))))))))))))))))))))))))))


def pow8_40 {R : Type*} [CommRing R] (z : R) : R := (10 + z * (16 + z * (24 + z * (21 + z * (19 + z * (1 + z * (34 + z * (28 + z * (40 + z * (21 + z * (18 + z * (3 + z * (40 + z * (21 + z * (10 + z * (2 + z * (5 + z * (12 + z * (10 + z * 38)))))))))))))))))))

def pow8_40_q {R : Type*} [CommRing R] (z : R) : R := (4 + z * (16 + z * (25 + z * (29 + z * (26 + z * (20 + z * (18 + z * (29 + z * (26 + z * (6 + z * (2 + z * (31 + z * (28 + z * (8 + z * (7 + z * (9 + z * (4 + z * (1 + z * 1))))))))))))))))))

def pow8_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (7 + z * (14 + z * ((-9) + z * ((-32) + z * ((-25) + z * ((-40) + z * ((-17) + z * (5 + z * ((-29) + z * ((-9) + z * (13 + z * ((-12) + z * (2 + z * (8 + z * (3 + z * (2 + z * (23 + z * (14 + z * (41 + z * (10 + z * ((-8) + z * (28 + z * ((-10) + z * ((-9) + z * (69 + z * (41 + z * (15 + z * (17 + z * (37 + z * (29 + z * (19 + z * (1 + z * (25 + z * (32 + z * (6 + z * (19 + z * (31 + z * (1 + z * 0))))))))))))))))))))))))))))))))))))))


def pow8_41 {R : Type*} [CommRing R] (z : R) : R := (21 + z * (7 + z * (26 + z * (28 + z * (4 + z * (30 + z * (16 + z * (39 + z * (9 + z * (24 + z * (8 + z * (22 + z * (31 + z * (17 + z * (27 + z * (40 + z * (17 + z * (32 + z * (35 + z * 1)))))))))))))))))))

def pow8_41_q {R : Type*} [CommRing R] (z : R) : R := (26 + z * (20 + z * (36 + z * (5 + z * (7 + z * (27 + z * (5 + z * (36 + z * (12 + z * (34 + z * (12 + z * (12 + z * (22 + z * (24 + z * (25 + z * (38 + z * (39 + z * (27 + z * 32))))))))))))))))))

def pow8_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-17) + z * ((-9) + z * ((-30) + z * (2 + z * ((-15) + z * ((-17) + z * (5 + z * ((-6) + z * (32 + z * ((-37) + z * (39 + z * ((-19) + z * (26 + z * (18 + z * (0 + z * ((-36) + z * ((-45) + z * ((-52) + z * ((-51) + z * ((-19) + z * ((-51) + z * ((-34) + z * ((-23) + z * ((-19) + z * ((-82) + z * ((-32) + z * ((-71) + z * ((-51) + z * ((-57) + z * ((-51) + z * ((-81) + z * ((-100) + z * ((-71) + z * ((-83) + z * ((-48) + z * ((-26) + z * ((-17) + z * ((-15) + z * 2))))))))))))))))))))))))))))))))))))))


abbrev u8 {R : Type*} [CommRing R] (z : R) : R := pow8_41 z

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod41Powers05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41
def pow9_2 {R : Type*} [CommRing R] (z : R) : R := (3 + z * (11 + z * (14 + z * (3 + z * (7 + z * (33 + z * (2 + z * (37 + z * (0 + z * (38 + z * (40 + z * (16 + z * (21 + z * (28 + z * (8 + z * (29 + z * (16 + z * (37 + z * (27 + z * 9)))))))))))))))))))

def pow9_2_q {R : Type*} [CommRing R] (z : R) : R := (19 + z * (1 + z * (6 + z * (5 + z * (7 + z * (19 + z * (39 + z * (3 + z * (25 + z * (36 + z * (14 + z * (6 + z * (13 + z * (1 + z * (34 + z * (26 + z * (31 + z * (40 + z * 1))))))))))))))))))

def pow9_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-6) + z * (0 + z * (8 + z * (30 + z * (3 + z * (41 + z * (0 + z * (39 + z * (16 + z * (35 + z * (16 + z * (30 + z * (72 + z * (21 + z * (81 + z * (59 + z * (15 + z * (56 + z * (101 + z * (64 + z * (112 + z * (57 + z * (69 + z * (54 + z * (31 + z * (16 + z * (40 + z * (44 + z * (12 + z * (66 + z * (55 + z * (4 + z * (26 + z * (10 + z * (0 + z * (15 + z * (1 + z * (0 + z * 0))))))))))))))))))))))))))))))))))))))


def pow9_4 {R : Type*} [CommRing R] (z : R) : R := (2 + z * (10 + z * (23 + z * (32 + z * (32 + z * (26 + z * (5 + z * (15 + z * (10 + z * (37 + z * (25 + z * (29 + z * (34 + z * (35 + z * (28 + z * (39 + z * (0 + z * (21 + z * (40 + z * 37)))))))))))))))))))

def pow9_4_q {R : Type*} [CommRing R] (z : R) : R := (15 + z * (36 + z * (16 + z * (5 + z * (2 + z * (5 + z * (29 + z * (33 + z * (30 + z * (5 + z * (19 + z * (31 + z * (26 + z * (8 + z * (36 + z * (1 + z * (36 + z * (24 + z * 40))))))))))))))))))

def pow9_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-13) + z * ((-35) + z * ((-32) + z * ((-29) + z * ((-21) + z * ((-29) + z * ((-23) + z * ((-31) + z * ((-70) + z * ((-36) + z * ((-33) + z * ((-35) + z * ((-16) + z * ((-54) + z * (3 + z * ((-33) + z * ((-47) + z * ((-9) + z * ((-74) + z * (18 + z * (28 + z * ((-26) + z * (49 + z * (8 + z * (40 + z * ((-9) + z * (14 + z * (34 + z * (31 + z * ((-15) + z * (4 + z * ((-14) + z * ((-15) + z * ((-31) + z * (5 + z * ((-3) + z * ((-1) + z * ((-18) + z * 1))))))))))))))))))))))))))))))))))))))


def pow9_5 {R : Type*} [CommRing R] (z : R) : R := (24 + z * (27 + z * (1 + z * (19 + z * (20 + z * (9 + z * (16 + z * (11 + z * (21 + z * (15 + z * (32 + z * (11 + z * (38 + z * (25 + z * (28 + z * (40 + z * (25 + z * (32 + z * (6 + z * 29)))))))))))))))))))

def pow9_5_q {R : Type*} [CommRing R] (z : R) : R := (21 + z * (7 + z * (7 + z * (27 + z * (35 + z * (25 + z * (24 + z * (36 + z * (22 + z * (1 + z * (8 + z * (6 + z * (17 + z * (15 + z * (8 + z * (25 + z * (23 + z * (20 + z * 37))))))))))))))))))

def pow9_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-18) + z * ((-8) + z * ((-9) + z * ((-4) + z * ((-18) + z * ((-4) + z * ((-3) + z * ((-25) + z * ((-22) + z * (23 + z * (27 + z * (16 + z * (34 + z * (42 + z * (43 + z * (33 + z * (65 + z * (63 + z * (58 + z * (54 + z * (92 + z * (102 + z * (50 + z * (32 + z * (92 + z * (74 + z * (97 + z * (101 + z * (88 + z * (73 + z * (87 + z * (45 + z * (30 + z * (28 + z * (1 + z * (18 + z * (33 + z * (5 + z * 0))))))))))))))))))))))))))))))))))))))


def pow9_10 {R : Type*} [CommRing R] (z : R) : R := (39 + z * (20 + z * (17 + z * (33 + z * (24 + z * (16 + z * (35 + z * (20 + z * (27 + z * (12 + z * (34 + z * (13 + z * (4 + z * (33 + z * (31 + z * (8 + z * (25 + z * (3 + z * (25 + z * 19)))))))))))))))))))

def pow9_10_q {R : Type*} [CommRing R] (z : R) : R := (32 + z * (33 + z * (11 + z * (30 + z * (12 + z * (35 + z * (4 + z * (25 + z * (40 + z * (25 + z * (3 + z * (24 + z * (7 + z * (2 + z * (0 + z * (19 + z * (32 + z * (5 + z * 21))))))))))))))))))

def pow9_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * ((-8) + z * ((-25) + z * ((-32) + z * ((-6) + z * ((-49) + z * (2 + z * ((-48) + z * ((-45) + z * ((-47) + z * ((-13) + z * ((-33) + z * ((-27) + z * (35 + z * (34 + z * (2 + z * (4 + z * (25 + z * (12 + z * (0 + z * (36 + z * (53 + z * (41 + z * (41 + z * (51 + z * (90 + z * (58 + z * (99 + z * (95 + z * (140 + z * (73 + z * (97 + z * (66 + z * (42 + z * (42 + z * (7 + z * (33 + z * ((-7) + z * 20))))))))))))))))))))))))))))))))))))))


def pow9_20 {R : Type*} [CommRing R] (z : R) : R := (36 + z * (17 + z * (29 + z * (39 + z * (19 + z * (7 + z * (1 + z * (21 + z * (40 + z * (33 + z * (11 + z * (28 + z * (4 + z * (14 + z * (11 + z * (38 + z * (17 + z * (1 + z * (31 + z * 12)))))))))))))))))))

def pow9_20_q {R : Type*} [CommRing R] (z : R) : R := (31 + z * (18 + z * (0 + z * (37 + z * (24 + z * (12 + z * (13 + z * (26 + z * (26 + z * (7 + z * (9 + z * (23 + z * (37 + z * (30 + z * (14 + z * (25 + z * (25 + z * (1 + z * 33))))))))))))))))))

def pow9_20_mul_t {R : Type*} [CommRing R] (z : R) : R := (9 + z * (12 + z * (13 + z * (32 + z * (27 + z * (18 + z * (92 + z * (33 + z * (45 + z * (76 + z * (90 + z * (43 + z * (19 + z * (89 + z * (73 + z * ((-12) + z * (69 + z * (44 + z * (19 + z * (35 + z * (16 + z * (61 + z * ((-6) + z * ((-10) + z * (44 + z * ((-18) + z * ((-6) + z * ((-24) + z * ((-17) + z * ((-18) + z * ((-48) + z * ((-38) + z * (1 + z * ((-23) + z * ((-18) + z * ((-11) + z * (3 + z * ((-1) + z * 8))))))))))))))))))))))))))))))))))))))


def pow9_40 {R : Type*} [CommRing R] (z : R) : R := (28 + z * (9 + z * (19 + z * (6 + z * (14 + z * (7 + z * (3 + z * (30 + z * (25 + z * (35 + z * (3 + z * (40 + z * (40 + z * (0 + z * (36 + z * (15 + z * (32 + z * (2 + z * (31 + z * 19)))))))))))))))))))

def pow9_40_q {R : Type*} [CommRing R] (z : R) : R := (17 + z * (39 + z * (27 + z * (1 + z * (28 + z * (6 + z * (18 + z * (12 + z * (7 + z * (37 + z * (0 + z * (20 + z * (30 + z * (36 + z * (22 + z * (14 + z * (37 + z * (32 + z * 21))))))))))))))))))

def pow9_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (16 + z * ((-10) + z * (9 + z * (54 + z * (27 + z * (35 + z * (7 + z * (43 + z * (25 + z * (31 + z * (82 + z * (86 + z * (47 + z * ((-14) + z * (8 + z * (29 + z * ((-12) + z * ((-11) + z * (51 + z * (18 + z * ((-53) + z * ((-15) + z * (26 + z * ((-16) + z * ((-28) + z * ((-46) + z * (17 + z * ((-27) + z * ((-85) + z * ((-35) + z * ((-45) + z * ((-61) + z * ((-81) + z * ((-23) + z * ((-13) + z * ((-41) + z * ((-9) + z * (2 + z * 3))))))))))))))))))))))))))))))))))))))


def pow9_41 {R : Type*} [CommRing R] (z : R) : R := (24 + z * (6 + z * (36 + z * (24 + z * (2 + z * (8 + z * (20 + z * (7 + z * (9 + z * (9 + z * (30 + z * (24 + z * (12 + z * (29 + z * (12 + z * (26 + z * (24 + z * (16 + z * (26 + z * 1)))))))))))))))))))

def pow9_41_q {R : Type*} [CommRing R] (z : R) : R := (2 + z * (36 + z * (6 + z * (6 + z * (30 + z * (12 + z * (20 + z * (28 + z * (31 + z * (34 + z * (4 + z * (31 + z * (11 + z * (19 + z * (33 + z * (25 + z * (11 + z * (3 + z * 19))))))))))))))))))

def pow9_41_mul_t {R : Type*} [CommRing R] (z : R) : R := (12 + z * ((-23) + z * (10 + z * ((-3) + z * ((-6) + z * ((-9) + z * ((-18) + z * (26 + z * ((-53) + z * ((-4) + z * (1 + z * ((-12) + z * (14 + z * ((-14) + z * (70 + z * ((-23) + z * (13 + z * (33 + z * (23 + z * (38 + z * ((-6) + z * (65 + z * ((-12) + z * (34 + z * (29 + z * (28 + z * (46 + z * (40 + z * (16 + z * (46 + z * (20 + z * (25 + z * (21 + z * (22 + z * (20 + z * (14 + z * (31 + z * (3 + z * 0))))))))))))))))))))))))))))))))))))))


abbrev u9 {R : Type*} [CommRing R] (z : R) : R := pow9_41 z


def pow10_2 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (32 + z * (11 + z * (32 + z * (36 + z * (37 + z * (7 + z * (11 + z * (14 + z * (13 + z * (10 + z * (25 + z * (20 + z * (18 + z * (28 + z * (3 + z * (7 + z * (24 + z * (28 + z * 19)))))))))))))))))))

def pow10_2_q {R : Type*} [CommRing R] (z : R) : R := (16 + z * (15 + z * (14 + z * (16 + z * (17 + z * (32 + z * (8 + z * (38 + z * (27 + z * (29 + z * (0 + z * (33 + z * (26 + z * (38 + z * (1 + z * (4 + z * (31 + z * (22 + z * 1))))))))))))))))))

def pow10_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * ((-12) + z * (14 + z * (8 + z * ((-3) + z * ((-8) + z * (0 + z * ((-57) + z * ((-21) + z * ((-63) + z * ((-5) + z * ((-54) + z * ((-23) + z * ((-18) + z * ((-28) + z * ((-32) + z * ((-36) + z * ((-34) + z * ((-14) + z * ((-49) + z * ((-52) + z * ((-31) + z * ((-59) + z * ((-68) + z * ((-65) + z * ((-24) + z * ((-16) + z * ((-43) + z * ((-12) + z * (14 + z * ((-14) + z * ((-3) + z * ((-25) + z * (13 + z * (9 + z * ((-11) + z * (0 + z * (0 + z * 0))))))))))))))))))))))))))))))))))))))


def pow10_4 {R : Type*} [CommRing R] (z : R) : R := (10 + z * (9 + z * (0 + z * (30 + z * (19 + z * (11 + z * (37 + z * (27 + z * (32 + z * (2 + z * (25 + z * (7 + z * (26 + z * (39 + z * (15 + z * (10 + z * (0 + z * (30 + z * (12 + z * 32)))))))))))))))))))

def pow10_4_q {R : Type*} [CommRing R] (z : R) : R := (2 + z * (7 + z * (14 + z * (26 + z * (31 + z * (23 + z * (27 + z * (5 + z * (14 + z * (6 + z * (10 + z * (32 + z * (15 + z * (40 + z * (38 + z * (40 + z * (22 + z * (33 + z * 33))))))))))))))))))

def pow10_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-2) + z * ((-7) + z * (9 + z * ((-16) + z * (5 + z * (18 + z * (35 + z * (32 + z * (41 + z * (52 + z * (14 + z * ((-13) + z * (15 + z * ((-23) + z * ((-2) + z * ((-15) + z * ((-5) + z * ((-39) + z * ((-45) + z * ((-33) + z * ((-46) + z * ((-30) + z * ((-24) + z * ((-10) + z * ((-49) + z * ((-76) + z * ((-55) + z * ((-61) + z * ((-65) + z * ((-82) + z * ((-67) + z * ((-50) + z * ((-75) + z * ((-75) + z * ((-58) + z * ((-10) + z * (3 + z * (1 + z * 8))))))))))))))))))))))))))))))))))))))


def pow10_5 {R : Type*} [CommRing R] (z : R) : R := (29 + z * (39 + z * (35 + z * (10 + z * (11 + z * (33 + z * (28 + z * (30 + z * (7 + z * (18 + z * (5 + z * (19 + z * (14 + z * (39 + z * (5 + z * (28 + z * (27 + z * (31 + z * (25 + z * 17)))))))))))))))))))

def pow10_5_q {R : Type*} [CommRing R] (z : R) : R := (7 + z * (20 + z * (10 + z * (32 + z * (28 + z * (7 + z * (20 + z * (38 + z * (28 + z * (22 + z * (39 + z * (32 + z * (37 + z * (36 + z * (28 + z * (17 + z * (18 + z * (7 + z * 32))))))))))))))))))

def pow10_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-1) + z * ((-14) + z * ((-11) + z * ((-15) + z * ((-27) + z * ((-18) + z * (12 + z * ((-29) + z * ((-25) + z * ((-12) + z * ((-32) + z * ((-79) + z * ((-63) + z * ((-33) + z * ((-71) + z * ((-63) + z * ((-38) + z * ((-60) + z * ((-99) + z * ((-35) + z * ((-76) + z * ((-30) + z * ((-88) + z * ((-51) + z * ((-49) + z * ((-78) + z * ((-86) + z * ((-79) + z * ((-52) + z * ((-67) + z * ((-30) + z * ((-34) + z * ((-29) + z * ((-31) + z * ((-11) + z * (8 + z * (2 + z * ((-3) + z * 0))))))))))))))))))))))))))))))))))))))


def pow10_10 {R : Type*} [CommRing R] (z : R) : R := (24 + z * (21 + z * (15 + z * (28 + z * (26 + z * (26 + z * (23 + z * (32 + z * (12 + z * (12 + z * (16 + z * (9 + z * (4 + z * (27 + z * (8 + z * (39 + z * (40 + z * (3 + z * (17 + z * 13)))))))))))))))))))

def pow10_10_q {R : Type*} [CommRing R] (z : R) : R := (17 + z * (6 + z * (9 + z * (5 + z * (39 + z * (16 + z * (7 + z * (17 + z * (39 + z * (0 + z * (12 + z * (17 + z * (36 + z * (40 + z * (2 + z * (13 + z * (3 + z * (11 + z * 2))))))))))))))))))

def pow10_10_mul_t {R : Type*} [CommRing R] (z : R) : R := (5 + z * (44 + z * (64 + z * (68 + z * (8 + z * (47 + z * (75 + z * (108 + z * (44 + z * (64 + z * (45 + z * (46 + z * (19 + z * (76 + z * (72 + z * (19 + z * (74 + z * (103 + z * (163 + z * (80 + z * (94 + z * (55 + z * (69 + z * (21 + z * (59 + z * (43 + z * (36 + z * ((-28) + z * (29 + z * (23 + z * (50 + z * (39 + z * (47 + z * (59 + z * (61 + z * (52 + z * (32 + z * (19 + z * 7))))))))))))))))))))))))))))))))))))))


def pow10_20 {R : Type*} [CommRing R] (z : R) : R := (40 + z * (14 + z * (35 + z * (11 + z * (4 + z * (29 + z * (39 + z * (37 + z * (36 + z * (19 + z * (21 + z * (6 + z * (21 + z * (38 + z * (1 + z * (32 + z * (32 + z * (4 + z * (37 + z * 36)))))))))))))))))))

def pow10_20_q {R : Type*} [CommRing R] (z : R) : R := (24 + z * (3 + z * (25 + z * (15 + z * (11 + z * (4 + z * (36 + z * (9 + z * (30 + z * (34 + z * (0 + z * (29 + z * (20 + z * (23 + z * (35 + z * (16 + z * (9 + z * (5 + z * 5))))))))))))))))))

def pow10_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-8) + z * (14 + z * ((-13) + z * (24 + z * (13 + z * (53 + z * (29 + z * (58 + z * (34 + z * (34 + z * (33 + z * (17 + z * (25 + z * ((-12) + z * (3 + z * ((-4) + z * (23 + z * (19 + z * (22 + z * (45 + z * (52 + z * (20 + z * (25 + z * (11 + z * ((-27) + z * ((-39) + z * ((-12) + z * ((-57) + z * ((-28) + z * ((-4) + z * ((-27) + z * (33 + z * (13 + z * ((-3) + z * (35 + z * (16 + z * (3 + z * (7 + z * 4))))))))))))))))))))))))))))))))))))))


def pow10_40 {R : Type*} [CommRing R] (z : R) : R := (33 + z * (33 + z * (13 + z * (13 + z * (40 + z * (25 + z * (19 + z * (35 + z * (1 + z * (15 + z * (0 + z * (28 + z * (5 + z * (22 + z * (22 + z * (37 + z * (25 + z * (16 + z * (4 + z * 16)))))))))))))))))))

def pow10_40_q {R : Type*} [CommRing R] (z : R) : R := (31 + z * (19 + z * (16 + z * (22 + z * (1 + z * (24 + z * (10 + z * (30 + z * (30 + z * (37 + z * (6 + z * (38 + z * (14 + z * (1 + z * (18 + z * (39 + z * (23 + z * (28 + z * 25))))))))))))))))))

def pow10_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (11 + z * (0 + z * (30 + z * (6 + z * (0 + z * (21 + z * (72 + z * (58 + z * (100 + z * (37 + z * (71 + z * (5 + z * (74 + z * (116 + z * (82 + z * (98 + z * (33 + z * (22 + z * (93 + z * (53 + z * (98 + z * (133 + z * (21 + z * (66 + z * (75 + z * (78 + z * (46 + z * (10 + z * (45 + z * (11 + z * ((-28) + z * (61 + z * (11 + z * ((-21) + z * (40 + z * (20 + z * (9 + z * (46 + z * 31))))))))))))))))))))))))))))))))))))))


def pow10_41 {R : Type*} [CommRing R] (z : R) : R := (32 + z * (1 + z * (13 + z * (12 + z * (15 + z * (31 + z * (3 + z * (30 + z * (19 + z * (21 + z * (6 + z * (8 + z * (4 + z * (23 + z * (19 + z * (4 + z * (0 + z * (11 + z * (10 + z * 5)))))))))))))))))))

def pow10_41_q {R : Type*} [CommRing R] (z : R) : R := (12 + z * (22 + z * (30 + z * (36 + z * (8 + z * (20 + z * (7 + z * (18 + z * (8 + z * (9 + z * (16 + z * (7 + z * (40 + z * (19 + z * (15 + z * (17 + z * (18 + z * (22 + z * 16))))))))))))))))))

def pow10_41_mul_t {R : Type*} [CommRing R] (z : R) : R := (8 + z * (1 + z * ((-1) + z * (0 + z * (7 + z * ((-19) + z * (35 + z * (18 + z * (7 + z * (3 + z * (0 + z * (21 + z * ((-33) + z * (17 + z * ((-8) + z * (39 + z * (7 + z * (24 + z * (4 + z * ((-12) + z * ((-23) + z * ((-10) + z * (4 + z * ((-14) + z * ((-10) + z * (5 + z * ((-11) + z * ((-13) + z * ((-23) + z * ((-5) + z * ((-2) + z * ((-19) + z * ((-8) + z * ((-10) + z * ((-10) + z * ((-10) + z * ((-14) + z * ((-2) + z * 0))))))))))))))))))))))))))))))))))))))


abbrev u10 {R : Type*} [CommRing R] (z : R) : R := pow10_41 z

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod41Powers06
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41
def pow11_2 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (2 + z * (21 + z * (15 + z * (17 + z * (22 + z * (33 + z * (23 + z * (12 + z * (35 + z * (25 + z * (38 + z * (19 + z * (29 + z * (3 + z * (20 + z * (26 + z * (11 + z * (0 + z * 12)))))))))))))))))))

def pow11_2_q {R : Type*} [CommRing R] (z : R) : R := (33 + z * (16 + z * (28 + z * (36 + z * (11 + z * (15 + z * (40 + z * (29 + z * (9 + z * (7 + z * (23 + z * (12 + z * (27 + z * (5 + z * (36 + z * (36 + z * (15 + z * (6 + z * 25))))))))))))))))))

def pow11_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-4) + z * ((-23) + z * ((-34) + z * ((-34) + z * ((-40) + z * ((-4) + z * ((-55) + z * ((-33) + z * ((-33) + z * ((-8) + z * ((-57) + z * ((-53) + z * ((-35) + z * ((-25) + z * ((-84) + z * ((-92) + z * ((-105) + z * ((-112) + z * ((-117) + z * ((-130) + z * ((-100) + z * ((-106) + z * ((-123) + z * ((-94) + z * ((-78) + z * ((-115) + z * ((-89) + z * ((-58) + z * ((-69) + z * ((-107) + z * ((-86) + z * ((-70) + z * ((-55) + z * ((-70) + z * ((-53) + z * ((-23) + z * ((-10) + z * ((-16) + z * 0))))))))))))))))))))))))))))))))))))))


def pow11_4 {R : Type*} [CommRing R] (z : R) : R := (32 + z * (5 + z * (8 + z * (17 + z * (26 + z * (16 + z * (11 + z * (10 + z * (38 + z * (27 + z * (26 + z * (25 + z * (38 + z * (31 + z * (39 + z * (3 + z * (1 + z * (0 + z * (13 + z * 15)))))))))))))))))))

def pow11_4_q {R : Type*} [CommRing R] (z : R) : R := (31 + z * (16 + z * (7 + z * (25 + z * (25 + z * (33 + z * (39 + z * (40 + z * (4 + z * (18 + z * (31 + z * (28 + z * (12 + z * (14 + z * (40 + z * (18 + z * (29 + z * (26 + z * 21))))))))))))))))))

def pow11_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-28) + z * ((-24) + z * ((-34) + z * ((-35) + z * ((-48) + z * ((-55) + z * ((-47) + z * ((-80) + z * ((-38) + z * ((-32) + z * ((-40) + z * ((-47) + z * ((-7) + z * (5 + z * ((-48) + z * ((-4) + z * ((-31) + z * ((-26) + z * ((-46) + z * ((-20) + z * ((-21) + z * ((-42) + z * ((-19) + z * ((-32) + z * ((-35) + z * ((-61) + z * ((-32) + z * ((-29) + z * ((-35) + z * ((-64) + z * ((-60) + z * ((-59) + z * ((-52) + z * ((-77) + z * ((-43) + z * ((-29) + z * ((-22) + z * ((-16) + z * 3))))))))))))))))))))))))))))))))))))))


def pow11_5 {R : Type*} [CommRing R] (z : R) : R := (29 + z * (33 + z * (13 + z * (11 + z * (16 + z * (27 + z * (33 + z * (14 + z * (24 + z * (30 + z * (15 + z * (6 + z * (21 + z * (15 + z * (32 + z * (30 + z * (9 + z * (11 + z * (19 + z * 5)))))))))))))))))))

def pow11_5_q {R : Type*} [CommRing R] (z : R) : R := (6 + z * (33 + z * (30 + z * (30 + z * (24 + z * (21 + z * (9 + z * (25 + z * (14 + z * (40 + z * (21 + z * (18 + z * (8 + z * (6 + z * (19 + z * (27 + z * (5 + z * (15 + z * 34))))))))))))))))))

def pow11_5_mul_t {R : Type*} [CommRing R] (z : R) : R := (19 + z * ((-27) + z * ((-25) + z * ((-36) + z * ((-22) + z * ((-29) + z * ((-30) + z * ((-17) + z * ((-1) + z * ((-41) + z * ((-25) + z * ((-41) + z * ((-12) + z * (6 + z * (1 + z * ((-33) + z * ((-46) + z * ((-41) + z * ((-71) + z * ((-61) + z * ((-95) + z * ((-39) + z * ((-69) + z * ((-41) + z * ((-67) + z * ((-79) + z * ((-58) + z * ((-23) + z * ((-53) + z * ((-68) + z * ((-51) + z * ((-29) + z * ((-37) + z * ((-56) + z * ((-56) + z * ((-26) + z * ((-18) + z * ((-20) + z * 1))))))))))))))))))))))))))))))))))))))


def pow11_10 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (2 + z * (0 + z * (22 + z * (10 + z * (31 + z * (7 + z * (24 + z * (15 + z * (1 + z * (3 + z * (38 + z * (1 + z * (19 + z * (30 + z * (28 + z * (36 + z * (19 + z * (21 + z * 25)))))))))))))))))))

def pow11_10_q {R : Type*} [CommRing R] (z : R) : R := (7 + z * (13 + z * (27 + z * (27 + z * (40 + z * (24 + z * (27 + z * (3 + z * (21 + z * (33 + z * (1 + z * (7 + z * (30 + z * (26 + z * (5 + z * (9 + z * (36 + z * (14 + z * 25))))))))))))))))))

def pow11_10_mul_t {R : Type*} [CommRing R] (z : R) : R := (14 + z * (33 + z * (12 + z * ((-6) + z * ((-25) + z * (5 + z * (19 + z * (38 + z * (9 + z * (36 + z * (43 + z * (18 + z * (13 + z * ((-2) + z * (67 + z * (75 + z * ((-9) + z * ((-8) + z * (9 + z * ((-4) + z * ((-51) + z * ((-1) + z * ((-6) + z * ((-17) + z * ((-5) + z * ((-29) + z * ((-2) + z * ((-22) + z * ((-32) + z * ((-8) + z * ((-12) + z * ((-38) + z * ((-32) + z * ((-21) + z * ((-31) + z * ((-34) + z * ((-10) + z * ((-14) + z * 0))))))))))))))))))))))))))))))))))))))


def pow11_20 {R : Type*} [CommRing R] (z : R) : R := (34 + z * (6 + z * (37 + z * (18 + z * (28 + z * (32 + z * (21 + z * (36 + z * (39 + z * (29 + z * (36 + z * (12 + z * (7 + z * (13 + z * (34 + z * (32 + z * (25 + z * (29 + z * (23 + z * 34)))))))))))))))))))

def pow11_20_q {R : Type*} [CommRing R] (z : R) : R := (11 + z * (26 + z * (9 + z * (4 + z * (27 + z * (12 + z * (22 + z * (33 + z * (7 + z * (28 + z * (22 + z * (9 + z * (1 + z * (37 + z * (26 + z * (32 + z * (0 + z * (12 + z * 10))))))))))))))))))

def pow11_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-5) + z * ((-25) + z * ((-25) + z * ((-10) + z * ((-32) + z * ((-21) + z * ((-34) + z * ((-31) + z * ((-33) + z * ((-63) + z * ((-18) + z * ((-42) + z * ((-31) + z * ((-65) + z * ((-38) + z * ((-90) + z * ((-17) + z * ((-95) + z * ((-10) + z * (12 + z * ((-35) + z * ((-3) + z * (20 + z * ((-13) + z * ((-4) + z * ((-30) + z * ((-4) + z * (35 + z * ((-13) + z * (13 + z * (54 + z * (32 + z * (39 + z * (47 + z * (41 + z * (52 + z * (21 + z * (18 + z * 15))))))))))))))))))))))))))))))))))))))


def pow11_40 {R : Type*} [CommRing R] (z : R) : R := (30 + z * (26 + z * (18 + z * (2 + z * (0 + z * (19 + z * (30 + z * (25 + z * (18 + z * (32 + z * (4 + z * (13 + z * (39 + z * (0 + z * (39 + z * (33 + z * (2 + z * (19 + z * (29 + z * 19)))))))))))))))))))

def pow11_40_q {R : Type*} [CommRing R] (z : R) : R := (29 + z * (40 + z * (9 + z * (18 + z * (23 + z * (34 + z * (39 + z * (22 + z * (34 + z * (27 + z * (13 + z * (17 + z * (39 + z * (31 + z * (9 + z * (19 + z * (37 + z * (12 + z * 8))))))))))))))))))

def pow11_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (2 + z * ((-35) + z * (20 + z * ((-8) + z * (29 + z * (8 + z * (27 + z * (51 + z * (27 + z * (70 + z * (103 + z * (70 + z * (58 + z * (50 + z * (92 + z * (68 + z * (39 + z * (83 + z * (106 + z * (113 + z * (38 + z * (127 + z * (101 + z * (83 + z * (100 + z * (92 + z * (84 + z * (42 + z * (35 + z * (52 + z * (15 + z * (10 + z * (37 + z * (75 + z * (59 + z * (37 + z * (48 + z * (32 + z * 28))))))))))))))))))))))))))))))))))))))


def pow11_41 {R : Type*} [CommRing R] (z : R) : R := (25 + z * (7 + z * (1 + z * (10 + z * (0 + z * (39 + z * (15 + z * (38 + z * (3 + z * (36 + z * (16 + z * (14 + z * (19 + z * (23 + z * (6 + z * (39 + z * (22 + z * (28 + z * (38 + z * 7)))))))))))))))))))

def pow11_41_q {R : Type*} [CommRing R] (z : R) : R := (18 + z * (7 + z * (10 + z * (16 + z * (35 + z * (6 + z * (12 + z * (40 + z * (1 + z * (13 + z * (5 + z * (20 + z * (36 + z * (37 + z * (10 + z * (38 + z * (14 + z * (27 + z * 13))))))))))))))))))

def pow11_41_mul_t {R : Type*} [CommRing R] (z : R) : R := (7 + z * (9 + z * (0 + z * ((-4) + z * ((-33) + z * (16 + z * (5 + z * ((-9) + z * ((-1) + z * (22 + z * (22 + z * ((-38) + z * (5 + z * ((-24) + z * (13 + z * ((-45) + z * ((-32) + z * ((-51) + z * ((-44) + z * ((-35) + z * ((-42) + z * ((-42) + z * ((-51) + z * ((-52) + z * ((-48) + z * ((-33) + z * ((-55) + z * ((-52) + z * ((-64) + z * ((-71) + z * ((-77) + z * ((-67) + z * ((-52) + z * ((-40) + z * ((-48) + z * ((-17) + z * ((-11) + z * ((-2) + z * 2))))))))))))))))))))))))))))))))))))))


abbrev u11 {R : Type*} [CommRing R] (z : R) : R := pow11_41 z


def pow12_2 {R : Type*} [CommRing R] (z : R) : R := (36 + z * (12 + z * (30 + z * (18 + z * (29 + z * (30 + z * (27 + z * (14 + z * (20 + z * (0 + z * (2 + z * (36 + z * (1 + z * (9 + z * (21 + z * (22 + z * (9 + z * (33 + z * (10 + z * 35)))))))))))))))))))

def pow12_2_q {R : Type*} [CommRing R] (z : R) : R := (38 + z * (23 + z * (28 + z * (29 + z * (26 + z * (28 + z * (23 + z * (13 + z * (27 + z * (10 + z * (31 + z * (39 + z * (17 + z * (25 + z * (3 + z * (29 + z * (33 + z * (5 + z * 8))))))))))))))))))

def pow12_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-19) + z * ((-24) + z * ((-58) + z * ((-40) + z * ((-80) + z * ((-30) + z * ((-41) + z * ((-44) + z * ((-71) + z * ((-43) + z * ((-42) + z * ((-92) + z * ((-33) + z * ((-77) + z * ((-19) + z * ((-84) + z * ((-39) + z * ((-87) + z * ((-20) + z * ((-94) + z * ((-37) + z * ((-24) + z * (24 + z * (13 + z * (46 + z * (35 + z * ((-11) + z * (5 + z * (23 + z * ((-9) + z * (13 + z * (17 + z * (12 + z * (60 + z * (29 + z * (28 + z * (37 + z * (7 + z * 1))))))))))))))))))))))))))))))))))))))


def pow12_4 {R : Type*} [CommRing R] (z : R) : R := (38 + z * (40 + z * (1 + z * (1 + z * (24 + z * (39 + z * (18 + z * (20 + z * (23 + z * (23 + z * (22 + z * (1 + z * (31 + z * (19 + z * (0 + z * (37 + z * (2 + z * (9 + z * (19 + z * 32)))))))))))))))))))

def pow12_4_q {R : Type*} [CommRing R] (z : R) : R := (19 + z * (24 + z * (11 + z * (3 + z * (13 + z * (13 + z * (23 + z * (28 + z * (35 + z * (15 + z * (36 + z * (0 + z * (14 + z * (9 + z * (28 + z * (31 + z * (37 + z * (30 + z * 36))))))))))))))))))

def pow12_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (14 + z * ((-7) + z * (25 + z * (25 + z * (47 + z * (56 + z * (69 + z * (48 + z * (33 + z * (15 + z * (1 + z * (55 + z * ((-25) + z * (39 + z * ((-23) + z * ((-13) + z * ((-44) + z * ((-15) + z * ((-59) + z * (52 + z * ((-32) + z * (12 + z * ((-1) + z * ((-30) + z * ((-58) + z * ((-59) + z * ((-79) + z * ((-71) + z * ((-37) + z * ((-80) + z * ((-4) + z * ((-62) + z * ((-51) + z * ((-49) + z * ((-16) + z * ((-29) + z * (21 + z * ((-10) + z * 29))))))))))))))))))))))))))))))))))))))


def pow12_5 {R : Type*} [CommRing R] (z : R) : R := (21 + z * (2 + z * (22 + z * (11 + z * (33 + z * (30 + z * (16 + z * (33 + z * (18 + z * (6 + z * (33 + z * (35 + z * (33 + z * (22 + z * (23 + z * (21 + z * (11 + z * (18 + z * (12 + z * 15)))))))))))))))))))

def pow12_5_q {R : Type*} [CommRing R] (z : R) : R := (11 + z * (30 + z * (6 + z * (3 + z * (40 + z * (10 + z * (9 + z * (6 + z * (7 + z * (32 + z * (2 + z * (16 + z * (35 + z * (19 + z * (9 + z * (21 + z * (5 + z * (0 + z * 19))))))))))))))))))

def pow12_5_mul_t {R : Type*} [CommRing R] (z : R) : R := (13 + z * (1 + z * ((-15) + z * ((-16) + z * ((-26) + z * (15 + z * (21 + z * (43 + z * ((-8) + z * (13 + z * (75 + z * ((-6) + z * (19 + z * (26 + z * (38 + z * (40 + z * (10 + z * (60 + z * (69 + z * (39 + z * (5 + z * (44 + z * (71 + z * (18 + z * (83 + z * (49 + z * (25 + z * (21 + z * (24 + z * ((-14) + z * (30 + z * (8 + z * (13 + z * (28 + z * (22 + z * (24 + z * (33 + z * (19 + z * 5))))))))))))))))))))))))))))))))))))))


def pow12_10 {R : Type*} [CommRing R] (z : R) : R := (12 + z * (13 + z * (37 + z * (18 + z * (11 + z * (31 + z * (22 + z * (20 + z * (7 + z * (16 + z * (24 + z * (22 + z * (25 + z * (32 + z * (9 + z * (24 + z * (0 + z * (27 + z * (8 + z * 2)))))))))))))))))))

def pow12_10_q {R : Type*} [CommRing R] (z : R) : R := (29 + z * (12 + z * (27 + z * (17 + z * (30 + z * (37 + z * (18 + z * (24 + z * (19 + z * (29 + z * (1 + z * (30 + z * (10 + z * (16 + z * (37 + z * (36 + z * (0 + z * (6 + z * 20))))))))))))))))))

def pow12_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * ((-18) + z * ((-27) + z * ((-20) + z * ((-28) + z * ((-23) + z * ((-16) + z * ((-10) + z * ((-7) + z * ((-18) + z * (34 + z * ((-5) + z * (43 + z * (1 + z * (41 + z * (12 + z * (10 + z * (56 + z * (23 + z * (13 + z * (15 + z * (31 + z * (13 + z * (35 + z * (38 + z * (14 + z * (13 + z * (27 + z * (6 + z * (5 + z * ((-17) + z * ((-3) + z * ((-14) + z * ((-26) + z * ((-17) + z * (4 + z * (4 + z * ((-6) + z * 5))))))))))))))))))))))))))))))))))))))


def pow12_20 {R : Type*} [CommRing R] (z : R) : R := (18 + z * (22 + z * (36 + z * (34 + z * (39 + z * (33 + z * (0 + z * (24 + z * (28 + z * (33 + z * (12 + z * (3 + z * (18 + z * (4 + z * (26 + z * (5 + z * (1 + z * (0 + z * (24 + z * 38)))))))))))))))))))

def pow12_20_q {R : Type*} [CommRing R] (z : R) : R := (24 + z * (29 + z * (7 + z * (7 + z * (4 + z * (19 + z * (28 + z * (29 + z * (3 + z * (37 + z * (26 + z * (1 + z * (27 + z * (14 + z * (10 + z * (40 + z * (38 + z * (35 + z * 4))))))))))))))))))

def pow12_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-18) + z * ((-26) + z * ((-8) + z * (3 + z * (20 + z * (8 + z * (17 + z * (16 + z * (14 + z * ((-12) + z * (2 + z * (7 + z * (29 + z * (29 + z * (15 + z * (41 + z * ((-42) + z * ((-38) + z * (5 + z * ((-9) + z * ((-16) + z * ((-41) + z * ((-3) + z * ((-38) + z * ((-57) + z * ((-54) + z * ((-56) + z * ((-42) + z * ((-47) + z * ((-47) + z * ((-26) + z * ((-92) + z * ((-63) + z * ((-67) + z * ((-48) + z * ((-35) + z * ((-24) + z * ((-3) + z * 0))))))))))))))))))))))))))))))))))))))


def pow12_40 {R : Type*} [CommRing R] (z : R) : R := (36 + z * (14 + z * (10 + z * (15 + z * (29 + z * (23 + z * (1 + z * (40 + z * (36 + z * (3 + z * (13 + z * (30 + z * (11 + z * (35 + z * (15 + z * (3 + z * (14 + z * (40 + z * (20 + z * 7)))))))))))))))))))

def pow12_40_q {R : Type*} [CommRing R] (z : R) : R := (8 + z * (21 + z * (11 + z * (24 + z * (31 + z * (25 + z * (12 + z * (34 + z * (17 + z * (23 + z * (23 + z * (30 + z * (12 + z * (8 + z * (37 + z * (6 + z * (10 + z * (37 + z * 9))))))))))))))))))

def pow12_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * ((-2) + z * (21 + z * (28 + z * (52 + z * (63 + z * (79 + z * (63 + z * (58 + z * (68 + z * (74 + z * (32 + z * (67 + z * (45 + z * (6 + z * ((-19) + z * ((-2) + z * ((-17) + z * ((-70) + z * ((-31) + z * ((-32) + z * ((-19) + z * ((-3) + z * (20 + z * ((-62) + z * ((-113) + z * ((-32) + z * ((-7) + z * ((-25) + z * ((-68) + z * ((-54) + z * ((-33) + z * ((-33) + z * ((-19) + z * ((-27) + z * ((-26) + z * ((-17) + z * (37 + z * 35))))))))))))))))))))))))))))))))))))))


def pow12_41 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (14 + z * (10 + z * (18 + z * (38 + z * (35 + z * (4 + z * (22 + z * (4 + z * (37 + z * (23 + z * (29 + z * (12 + z * (14 + z * (17 + z * (26 + z * (12 + z * (36 + z * (5 + z * 25)))))))))))))))))))

def pow12_41_q {R : Type*} [CommRing R] (z : R) : R := (26 + z * (32 + z * (25 + z * (20 + z * (6 + z * (1 + z * (16 + z * (30 + z * (21 + z * (20 + z * (5 + z * (2 + z * (21 + z * (33 + z * (35 + z * (24 + z * (15 + z * (2 + z * 8))))))))))))))))))

def pow12_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-1) + z * ((-22) + z * ((-42) + z * ((-30) + z * ((-28) + z * (9 + z * ((-8) + z * (7 + z * ((-18) + z * ((-8) + z * (6 + z * ((-4) + z * (18 + z * (27 + z * ((-13) + z * ((-28) + z * ((-19) + z * (10 + z * (30 + z * (8 + z * (35 + z * (5 + z * (54 + z * (49 + z * (28 + z * (26 + z * (49 + z * (2 + z * (11 + z * (9 + z * ((-4) + z * ((-4) + z * (3 + z * (3 + z * (26 + z * (40 + z * (25 + z * (4 + z * 1))))))))))))))))))))))))))))))))))))))


abbrev u12 {R : Type*} [CommRing R] (z : R) : R := pow12_41 z

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod41Powers07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41


def pow13_4 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (17 + z * (26 + z * (40 + z * (18 + z * (13 + z * (17 + z * (16 + z * (37 + z * (8 + z * (13 + z * (34 + z * (18 + z * (16 + z * (6 + z * (18 + z * (11 + z * (20 + z * (21 + z * 29)))))))))))))))))))


def pow13_5 {R : Type*} [CommRing R] (z : R) : R := (33 + z * (11 + z * (39 + z * (36 + z * (26 + z * (0 + z * (12 + z * (37 + z * (11 + z * (26 + z * (30 + z * (17 + z * (28 + z * (19 + z * (4 + z * (1 + z * (15 + z * (3 + z * (40 + z * 38)))))))))))))))))))


def pow13_10 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (15 + z * (18 + z * (2 + z * (12 + z * (21 + z * (5 + z * (27 + z * (23 + z * (32 + z * (37 + z * (16 + z * (15 + z * (20 + z * (23 + z * (29 + z * (18 + z * (4 + z * (12 + z * 40)))))))))))))))))))

def pow13_10_q {R : Type*} [CommRing R] (z : R) : R := (21 + z * (19 + z * (9 + z * (20 + z * (23 + z * (5 + z * (4 + z * (21 + z * (29 + z * (21 + z * (4 + z * (17 + z * (29 + z * (28 + z * (22 + z * (14 + z * (1 + z * (23 + z * 9))))))))))))))))))

def pow13_10_mul_t {R : Type*} [CommRing R] (z : R) : R := (8 + z * ((-6) + z * (36 + z * (44 + z * (48 + z * (38 + z * (68 + z * (53 + z * ((-5) + z * (66 + z * (93 + z * (56 + z * (69 + z * (82 + z * (58 + z * ((-2) + z * (29 + z * ((-18) + z * (35 + z * (52 + z * (79 + z * (97 + z * (68 + z * (3 + z * ((-48) + z * (32 + z * (22 + z * ((-16) + z * (19 + z * (15 + z * (14 + z * (17 + z * ((-16) + z * ((-38) + z * (0 + z * (18 + z * (24 + z * (67 + z * 35))))))))))))))))))))))))))))))))))))))


def pow13_20 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (10 + z * (38 + z * (33 + z * (33 + z * (15 + z * (28 + z * (16 + z * (30 + z * (23 + z * (31 + z * (17 + z * (13 + z * (3 + z * (4 + z * (22 + z * (26 + z * (0 + z * (37 + z * 28)))))))))))))))))))


def pow13_40 {R : Type*} [CommRing R] (z : R) : R := (6 + z * (9 + z * (25 + z * (3 + z * (6 + z * (37 + z * (40 + z * (17 + z * (3 + z * (31 + z * (13 + z * (6 + z * (20 + z * (4 + z * (11 + z * (29 + z * (32 + z * (4 + z * (36 + z * 27)))))))))))))))))))


def pow13_41 {R : Type*} [CommRing R] (z : R) : R := (30 + z * (23 + z * (8 + z * (32 + z * (34 + z * (36 + z * (32 + z * (30 + z * (33 + z * (23 + z * (36 + z * (1 + z * (27 + z * (2 + z * (6 + z * (12 + z * (14 + z * (15 + z * (1 + z * 4)))))))))))))))))))


abbrev u13 {R : Type*} [CommRing R] (z : R) : R := pow13_41 z

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod41Result
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41

def a10 {R : Type*} [CommRing R] (z : R) : R := (34 + z * (34 + z * (21 + z * (14 + z * (25 + z * (8 + z * (3 + z * (0 + z * (6 + z * (24 + z * (2 + z * (20 + z * (8 + z * (21 + z * (6 + z * (7 + z * (7 + z * (17 + z * 25))))))))))))))))))

def b10 {R : Type*} [CommRing R] (z : R) : R := (22 + z * (12 + z * (14 + z * (36 + z * (37 + z * (27 + z * (33 + z * (1 + z * (34 + z * (22 + z * (1 + z * (20 + z * (31 + z * (28 + z * (26 + z * (30 + z * (33 + z * (11 + z * (37 + z * 36)))))))))))))))))))

def bezout10_t {R : Type*} [CommRing R] (z : R) : R := (47 + z * (50 + z * (72 + z * (83 + z * (114 + z * (114 + z * (109 + z * (110 + z * (179 + z * (170 + z * (150 + z * (224 + z * (196 + z * (246 + z * (196 + z * (250 + z * (275 + z * (281 + z * (306 + z * (307 + z * (281 + z * (245 + z * (231 + z * (218 + z * (185 + z * (189 + z * (179 + z * (160 + z * (153 + z * (129 + z * (109 + z * (95 + z * (114 + z * (87 + z * (56 + z * (43 + z * (43 + z * (32 + z * 5))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod41

section
noncomputable section
open Polynomial
namespace DimensionTen.Mod41
lemma map_u10 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (z : R) :
    φ (u10 z) = u10 (φ z) := by simp only [u10, pow10_41, map_add, map_mul, map_ofNat, map_one, map_zero]

end DimensionTen.Mod41

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
def W0 : Fin 20 → ℤ :=
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def W2 : Fin 20 → ℤ :=
  ![-70575490389691608208970825963579579734790687104242531156794252400, 0, 0, -54650416258965825405642793201387333702389773392798003780754049600, 0, 0, 0, 0, 0, 6744457721418750809199279043857213239225855299715806239501267600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def W20 : Fin 20 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

lemma W20_eq : W20 = 0 := by decide +kernel

end DimensionTen.Border

end
end

end OAI
end


