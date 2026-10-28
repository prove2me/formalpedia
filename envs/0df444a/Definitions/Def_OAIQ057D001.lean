-- Prove2me | Definitions.Def_OAIQ057D001
-- name    : OAIQ057D001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T20:45:09.475633+00:00
-- url     : https://prove2.me/theorems/d5a3a058-e4d8-474b-b02b-4d452dedb3da
-- title:
--   Definitions bundle OAIQ057D001 of the split of OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DimensionTen.exists_channel_fin21`, carved from OpenAI's openai/math development (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 272 declarations of OpenAI's Lean: 148 definitions and 124 theorems. The definitions and types are `OAI.DimensionTen.Border.W1`, `OAI.DimensionTen.Mod41.a10`, `OAI.DimensionTen.Mod41.b10`, `OAI.DimensionTen.Mod41.bezout10_t`, `OAI.DimensionTen.Mod41.f`, `OAI.DimensionTen.Mod41.pow10_41`, `OAI.DimensionTen.Mod41.pow2_10_mul_t`, `OAI.DimensionTen.Mod41.pow2_10_q`, `OAI.DimensionTen.Mod41.pow2_2`, `OAI.DimensionTen.Mod41.pow2_20_mul_t`, `OAI.DimensionTen.Mod41.pow2_20_q`, `OAI.DimensionTen.Mod41.pow2_2_mul_t`, `OAI.DimensionTen.Mod41.pow2_2_q`, `OAI.DimensionTen.Mod41.pow2_4`, `OAI.DimensionTen.Mod41.pow2_40_mul_t`, `OAI.DimensionTen.Mod41.pow2_40_q`, `OAI.DimensionTen.Mod41.pow2_41_mul_t`, `OAI.DimensionTen.Mod41.pow2_41_q`, `OAI.DimensionTen.Mod41.pow2_4_mul_t`, `OAI.DimensionTen.Mod41.pow2_4_q`, `OAI.DimensionTen.Mod41.pow2_5`, `OAI.DimensionTen.Mod41.pow2_5_mul_t`, `OAI.DimensionTen.Mod41.pow2_5_q`, `OAI.DimensionTen.Mod41.pow3_10`, `OAI.DimensionTen.Mod41.pow3_10_mul_t`, `OAI.DimensionTen.Mod41.pow3_10_q`, `OAI.DimensionTen.Mod41.pow3_2`, `OAI.DimensionTen.Mod41.pow3_20`, `OAI.DimensionTen.Mod41.pow3_20_mul_t`, `OAI.DimensionTen.Mod41.pow3_20_q`, `OAI.DimensionTen.Mod41.pow3_2_mul_t`, `OAI.DimensionTen.Mod41.pow3_2_q`, `OAI.DimensionTen.Mod41.pow3_4`, `OAI.DimensionTen.Mod41.pow3_40`, `OAI.DimensionTen.Mod41.pow3_40_mul_t`, `OAI.DimensionTen.Mod41.pow3_40_q`, `OAI.DimensionTen.Mod41.pow3_41`, `OAI.DimensionTen.Mod41.pow3_41_mul_t`, `OAI.DimensionTen.Mod41.pow3_41_q`, `OAI.DimensionTen.Mod41.pow3_4_mul_t` and 108 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, lean/OAI/InformationTheory, in whole or in part: [`Quantum_DimensionTen_Mod41Model`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod41Model.lean), [`Quantum_DimensionTen_Mod41Powers01`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod41Powers01.lean), [`Quantum_DimensionTen_Mod41Powers02`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod41Powers02.lean), [`Quantum_DimensionTen_Mod41Powers03`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod41Powers03.lean), [`Quantum_DimensionTen_Mod41Powers04`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod41Powers04.lean), [`Quantum_DimensionTen_Mod41Powers05`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod41Powers05.lean), [`Quantum_DimensionTen_Mod41Result`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod41Result.lean), [`Quantum_DimensionTen_PolynomialData`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/PolynomialData.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ057D008` and `OAIQ057D009`; the statements `OAI_DimensionTen_root_action_full_symmetric` and `OAI.DimensionTen.root_action_full_symmetric_s2`.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis, lean/OAI/InformationTheory at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41
def f {R : Type*} [CommRing R] (z : R) : R := (36 + z * (13 + z * (30 + z * (1 + z * (32 + z * (5 + z * (1 + z * (33 + z * (20 + z * (11 + z * (15 + z * (31 + z * (14 + z * (7 + z * (25 + z * (36 + z * (33 + z * (23 + z * (17 + z * (30 + z * 1))))))))))))))))))))

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Powers01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41


def pow2_2 {R : Type*} [CommRing R] (z : R) : R := (36 + z * (16 + z * (13 + z * (19 + z * (39 + z * (9 + z * (15 + z * (38 + z * (38 + z * (18 + z * (4 + z * (38 + z * (29 + z * (20 + z * (28 + z * (2 + z * (33 + z * (20 + z * (6 + z * 25)))))))))))))))))))

def pow2_2_q {R : Type*} [CommRing R] (z : R) : R := (31 + z * (16 + z * (16 + z * (15 + z * (9 + z * (37 + z * (39 + z * (12 + z * (2 + z * (24 + z * (1 + z * (19 + z * (40 + z * (14 + z * (20 + z * (10 + z * (28 + z * (9 + z * 8))))))))))))))))))

def pow2_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (9 + z * (29 + z * ((-23) + z * (24 + z * (62 + z * (61 + z * (61 + z * (75 + z * (112 + z * (102 + z * (102 + z * (113 + z * (151 + z * (125 + z * (84 + z * (74 + z * (41 + z * (122 + z * (112 + z * (35 + z * (44 + z * (33 + z * (39 + z * ((-1) + z * (40 + z * (20 + z * (19 + z * ((-55) + z * ((-35) + z * ((-9) + z * (3 + z * ((-48) + z * ((-33) + z * ((-39) + z * (1 + z * ((-13) + z * (3 + z * ((-3) + z * 1))))))))))))))))))))))))))))))))))))))


def pow2_4 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (19 + z * (32 + z * (36 + z * (19 + z * (27 + z * (18 + z * (26 + z * (35 + z * (11 + z * (22 + z * (22 + z * (22 + z * (37 + z * (21 + z * (14 + z * (3 + z * (17 + z * (22 + z * 33)))))))))))))))))))

def pow2_4_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (6 + z * (34 + z * (4 + z * (39 + z * (24 + z * (0 + z * (30 + z * (10 + z * (11 + z * (6 + z * (37 + z * (15 + z * (26 + z * (35 + z * (34 + z * (5 + z * (0 + z * 10))))))))))))))))))

def pow2_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-3) + z * (10 + z * ((-32) + z * (23 + z * ((-4) + z * (11 + z * (2 + z * (36 + z * (76 + z * (17 + z * (54 + z * (54 + z * (83 + z * (40 + z * (55 + z * (26 + z * (70 + z * (59 + z * (33 + z * (59 + z * (103 + z * (41 + z * (19 + z * (68 + z * (66 + z * (61 + z * (7 + z * (48 + z * (29 + z * ((-30) + z * (7 + z * ((-4) + z * ((-2) + z * (15 + z * ((-14) + z * (36 + z * (21 + z * (0 + z * 15))))))))))))))))))))))))))))))))))))))

theorem pow2_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_2 z * pow2_2 z = pow2_4_q z * f z + pow2_4 z + (41 : R) * pow2_4_mul_t z := by
  simp only [pow2_2, pow2_4_q, f, pow2_4, pow2_4_mul_t]
  
  ring

theorem pow2_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow2_2 z * pow2_2 z = pow2_4_q z * f z + pow2_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow2_4_mul_integer z


theorem pow2_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow2_2 z * pow2_2 z = pow2_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_4_mul z


def pow2_5 {R : Type*} [CommRing R] (z : R) : R := (1 + z * (8 + z * (2 + z * (23 + z * (11 + z * (4 + z * (32 + z * (4 + z * (29 + z * (24 + z * (22 + z * (16 + z * (36 + z * (25 + z * (30 + z * (5 + z * (5 + z * (8 + z * (20 + z * 8)))))))))))))))))))

def pow2_5_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (2 + z * (23 + z * (21 + z * (2 + z * (26 + z * (40 + z * (21 + z * (1 + z * (33 + z * (35 + z * (24 + z * (36 + z * (36 + z * (6 + z * (11 + z * (2 + z * (40 + z * 26))))))))))))))))))

def pow2_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * (14 + z * ((-6) + z * (38 + z * (14 + z * (47 + z * (54 + z * (40 + z * (107 + z * (68 + z * (46 + z * (63 + z * (75 + z * (56 + z * (68 + z * (84 + z * (56 + z * (2 + z * (57 + z * (55 + z * (43 + z * ((-14) + z * (17 + z * (34 + z * ((-9) + z * ((-15) + z * ((-5) + z * ((-32) + z * ((-75) + z * ((-64) + z * (12 + z * ((-6) + z * ((-29) + z * ((-47) + z * ((-28) + z * ((-8) + z * ((-5) + z * ((-9) + z * 5))))))))))))))))))))))))))))))))))))))

def pow2_10_q {R : Type*} [CommRing R] (z : R) : R := (30 + z * (25 + z * (12 + z * (35 + z * (26 + z * (22 + z * (37 + z * (34 + z * (23 + z * (21 + z * (18 + z * (24 + z * (31 + z * (9 + z * (0 + z * (3 + z * (3 + z * (40 + z * 23))))))))))))))))))

def pow2_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-27) + z * ((-32) + z * ((-39) + z * ((-52) + z * ((-58) + z * ((-70) + z * ((-56) + z * ((-87) + z * ((-105) + z * ((-52) + z * ((-89) + z * ((-95) + z * ((-67) + z * ((-73) + z * ((-63) + z * ((-49) + z * ((-52) + z * ((-82) + z * ((-69) + z * ((-110) + z * ((-41) + z * ((-51) + z * ((-43) + z * ((-37) + z * ((-25) + z * ((-44) + z * ((-12) + z * ((-20) + z * ((-36) + z * ((-30) + z * (4 + z * ((-9) + z * ((-19) + z * ((-37) + z * ((-36) + z * ((-22) + z * ((-26) + z * ((-10) + z * 1))))))))))))))))))))))))))))))))))))))

def pow2_20_q {R : Type*} [CommRing R] (z : R) : R := (22 + z * (39 + z * (40 + z * (4 + z * (29 + z * (29 + z * (28 + z * (28 + z * (37 + z * (21 + z * (0 + z * (38 + z * (10 + z * (39 + z * (30 + z * (7 + z * (16 + z * (24 + z * 2))))))))))))))))))

def pow2_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-1) + z * (10 + z * ((-15) + z * ((-8) + z * (3 + z * (7 + z * ((-28) + z * (22 + z * ((-21) + z * ((-56) + z * (5 + z * ((-43) + z * ((-32) + z * ((-42) + z * (2 + z * ((-82) + z * ((-102) + z * ((-88) + z * ((-47) + z * ((-44) + z * ((-66) + z * ((-85) + z * ((-54) + z * ((-75) + z * ((-77) + z * ((-46) + z * ((-33) + z * ((-60) + z * ((-66) + z * ((-45) + z * ((-35) + z * ((-8) + z * ((-27) + z * ((-30) + z * ((-14) + z * (3 + z * (15 + z * (22 + z * 7))))))))))))))))))))))))))))))))))))))

def pow2_40_q {R : Type*} [CommRing R] (z : R) : R := (23 + z * (38 + z * (10 + z * (17 + z * (37 + z * (35 + z * (32 + z * (27 + z * (30 + z * (10 + z * (22 + z * (0 + z * (9 + z * (7 + z * (38 + z * (8 + z * (16 + z * (9 + z * 10))))))))))))))))))

def pow2_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (6 + z * (4 + z * (0 + z * ((-5) + z * ((-10) + z * ((-32) + z * ((-25) + z * ((-40) + z * ((-59) + z * ((-29) + z * ((-24) + z * ((-24) + z * ((-64) + z * (22 + z * (12 + z * (9 + z * ((-3) + z * (32 + z * ((-4) + z * (14 + z * ((-7) + z * ((-21) + z * ((-12) + z * (4 + z * (10 + z * (3 + z * (43 + z * (83 + z * (73 + z * (82 + z * (90 + z * (64 + z * (73 + z * (44 + z * (40 + z * (27 + z * (23 + z * (1 + z * 15))))))))))))))))))))))))))))))))))))))

def pow2_41_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (30 + z * (30 + z * (17 + z * (40 + z * (18 + z * (29 + z * (37 + z * (32 + z * (25 + z * (40 + z * (34 + z * (7 + z * (35 + z * (28 + z * (35 + z * (15 + z * (6 + z * 29))))))))))))))))))

def pow2_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * ((-13) + z * ((-23) + z * (11 + z * ((-39) + z * (24 + z * (32 + z * (16 + z * ((-12) + z * (29 + z * (21 + z * ((-24) + z * (22 + z * (7 + z * (15 + z * ((-38) + z * ((-25) + z * ((-36) + z * ((-47) + z * ((-50) + z * ((-49) + z * ((-59) + z * ((-64) + z * ((-50) + z * ((-53) + z * ((-106) + z * ((-84) + z * ((-67) + z * ((-54) + z * ((-78) + z * ((-70) + z * ((-40) + z * ((-57) + z * ((-55) + z * ((-32) + z * ((-22) + z * ((-4) + z * ((-19) + z * 1))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Powers02
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41
def pow3_2 {R : Type*} [CommRing R] (z : R) : R := (25 + z * (38 + z * (8 + z * (30 + z * (6 + z * (18 + z * (2 + z * (5 + z * (28 + z * (0 + z * (23 + z * (12 + z * (18 + z * (16 + z * (30 + z * (4 + z * (1 + z * (6 + z * (13 + z * 22)))))))))))))))))))

def pow3_2_q {R : Type*} [CommRing R] (z : R) : R := (13 + z * (38 + z * (24 + z * (39 + z * (39 + z * (8 + z * (37 + z * (39 + z * (19 + z * (14 + z * (18 + z * (36 + z * (19 + z * (23 + z * (15 + z * (5 + z * (30 + z * (30 + z * 21))))))))))))))))))

def pow3_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-12) + z * ((-37) + z * ((-21) + z * ((-31) + z * ((-12) + z * (12 + z * ((-3) + z * (18 + z * ((-2) + z * (29 + z * (52 + z * (0 + z * (23 + z * (31 + z * (8 + z * (15 + z * (44 + z * (12 + z * (5 + z * (81 + z * (76 + z * (80 + z * (83 + z * (59 + z * (62 + z * (70 + z * (49 + z * (42 + z * (49 + z * (32 + z * (36 + z * (58 + z * (37 + z * (40 + z * (61 + z * (48 + z * (35 + z * (32 + z * 20))))))))))))))))))))))))))))))))))))))


def pow3_4 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (4 + z * (24 + z * (10 + z * (10 + z * (28 + z * (34 + z * (11 + z * (3 + z * (0 + z * (25 + z * (22 + z * (4 + z * (38 + z * (6 + z * (17 + z * (33 + z * (32 + z * (15 + z * 35)))))))))))))))))))

def pow3_4_q {R : Type*} [CommRing R] (z : R) : R := (1 + z * (17 + z * (6 + z * (18 + z * (25 + z * (29 + z * (20 + z * (15 + z * (31 + z * (39 + z * (11 + z * (18 + z * (10 + z * (40 + z * (14 + z * (30 + z * (30 + z * (33 + z * 33))))))))))))))))))

def pow3_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (14 + z * (31 + z * (33 + z * (21 + z * (31 + z * ((-16) + z * (7 + z * ((-32) + z * ((-12) + z * ((-33) + z * ((-33) + z * (0 + z * ((-40) + z * ((-25) + z * ((-4) + z * ((-39) + z * ((-88) + z * ((-114) + z * ((-97) + z * ((-89) + z * ((-121) + z * ((-101) + z * ((-81) + z * ((-130) + z * ((-122) + z * ((-129) + z * ((-88) + z * ((-85) + z * ((-104) + z * ((-82) + z * ((-82) + z * ((-70) + z * ((-88) + z * ((-61) + z * ((-74) + z * ((-50) + z * ((-28) + z * ((-11) + z * 11))))))))))))))))))))))))))))))))))))))

theorem pow3_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_2 z * pow3_2 z = pow3_4_q z * f z + pow3_4 z + (41 : R) * pow3_4_mul_t z := by
  simp only [pow3_2, pow3_4_q, f, pow3_4, pow3_4_mul_t]
  
  ring

theorem pow3_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow3_2 z * pow3_2 z = pow3_4_q z * f z + pow3_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow3_4_mul_integer z


theorem pow3_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow3_2 z * pow3_2 z = pow3_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_4_mul z


def pow3_5 {R : Type*} [CommRing R] (z : R) : R := (39 + z * (3 + z * (23 + z * (32 + z * (2 + z * (19 + z * (2 + z * (32 + z * (4 + z * (37 + z * (35 + z * (7 + z * (1 + z * (23 + z * (32 + z * (11 + z * (31 + z * (19 + z * (17 + z * 3)))))))))))))))))))

def pow3_5_q {R : Type*} [CommRing R] (z : R) : R := (13 + z * (4 + z * (25 + z * (39 + z * (38 + z * (17 + z * (11 + z * (4 + z * (38 + z * (29 + z * (21 + z * (30 + z * (1 + z * (37 + z * (28 + z * (5 + z * (30 + z * (39 + z * 31))))))))))))))))))

def pow3_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-12) + z * (3 + z * ((-20) + z * ((-15) + z * ((-35) + z * ((-22) + z * (5 + z * (12 + z * (4 + z * (14 + z * ((-34) + z * ((-31) + z * (2 + z * ((-37) + z * (15 + z * ((-29) + z * ((-19) + z * ((-20) + z * ((-52) + z * (12 + z * (14 + z * (6 + z * (30 + z * (43 + z * ((-17) + z * ((-2) + z * (13 + z * ((-30) + z * ((-12) + z * (13 + z * (2 + z * (26 + z * ((-1) + z * ((-7) + z * (31 + z * (34 + z * (16 + z * (16 + z * 24))))))))))))))))))))))))))))))))))))))


def pow3_10 {R : Type*} [CommRing R] (z : R) : R := (40 + z * (18 + z * (12 + z * (7 + z * (13 + z * (23 + z * (10 + z * (35 + z * (16 + z * (32 + z * (29 + z * (8 + z * (6 + z * (29 + z * (26 + z * (12 + z * (6 + z * (2 + z * (21 + z * 32)))))))))))))))))))

def pow3_10_q {R : Type*} [CommRing R] (z : R) : R := (40 + z * (28 + z * (12 + z * (18 + z * (19 + z * (20 + z * (40 + z * (28 + z * (9 + z * (30 + z * (30 + z * (14 + z * (0 + z * (34 + z * (24 + z * (7 + z * (1 + z * (37 + z * 9))))))))))))))))))

def pow3_10_mul_t {R : Type*} [CommRing R] (z : R) : R := (1 + z * ((-32) + z * ((-5) + z * (23 + z * ((-42) + z * (8 + z * ((-36) + z * ((-16) + z * ((-62) + z * (8 + z * (15 + z * ((-68) + z * (22 + z * ((-29) + z * ((-22) + z * ((-72) + z * (37 + z * ((-55) + z * ((-26) + z * ((-3) + z * ((-32) + z * ((-71) + z * ((-64) + z * (37 + z * ((-46) + z * ((-46) + z * (1 + z * (19 + z * ((-40) + z * ((-37) + z * (9 + z * (7 + z * ((-14) + z * ((-17) + z * (2 + z * ((-1) + z * ((-21) + z * ((-5) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow3_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_5 z * pow3_5 z = pow3_10_q z * f z + pow3_10 z + (41 : R) * pow3_10_mul_t z := by
  simp only [pow3_5, pow3_10_q, f, pow3_10, pow3_10_mul_t]
  
  ring

theorem pow3_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow3_5 z * pow3_5 z = pow3_10_q z * f z + pow3_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow3_10_mul_integer z


theorem pow3_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow3_5 z * pow3_5 z = pow3_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_10_mul z


def pow3_20 {R : Type*} [CommRing R] (z : R) : R := (24 + z * (13 + z * (8 + z * (35 + z * (3 + z * (0 + z * (35 + z * (4 + z * (32 + z * (19 + z * (18 + z * (34 + z * (11 + z * (2 + z * (7 + z * (38 + z * (22 + z * (24 + z * (15 + z * 39)))))))))))))))))))

def pow3_20_q {R : Type*} [CommRing R] (z : R) : R := (21 + z * (7 + z * (12 + z * (9 + z * (2 + z * (34 + z * (29 + z * (23 + z * (26 + z * (8 + z * (23 + z * (32 + z * (3 + z * (0 + z * (14 + z * (19 + z * (38 + z * (21 + z * 40))))))))))))))))))

def pow3_20_mul_t {R : Type*} [CommRing R] (z : R) : R := (20 + z * (22 + z * (3 + z * (6 + z * (5 + z * (15 + z * ((-1) + z * (15 + z * (8 + z * (36 + z * (33 + z * (6 + z * ((-3) + z * (38 + z * (72 + z * (14 + z * ((-16) + z * ((-23) + z * ((-31) + z * (36 + z * ((-6) + z * ((-24) + z * ((-52) + z * (4 + z * ((-23) + z * ((-65) + z * ((-24) + z * ((-17) + z * (24 + z * ((-22) + z * ((-61) + z * ((-34) + z * ((-16) + z * ((-38) + z * ((-49) + z * ((-48) + z * ((-19) + z * (3 + z * 24))))))))))))))))))))))))))))))))))))))

theorem pow3_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_10 z * pow3_10 z = pow3_20_q z * f z + pow3_20 z + (41 : R) * pow3_20_mul_t z := by
  simp only [pow3_10, pow3_20_q, f, pow3_20, pow3_20_mul_t]
  
  ring

theorem pow3_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow3_10 z * pow3_10 z = pow3_20_q z * f z + pow3_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow3_20_mul_integer z


theorem pow3_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow3_10 z * pow3_10 z = pow3_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_20_mul z


def pow3_40 {R : Type*} [CommRing R] (z : R) : R := (7 + z * (20 + z * (9 + z * (9 + z * (34 + z * (36 + z * (15 + z * (22 + z * (30 + z * (8 + z * (1 + z * (28 + z * (36 + z * (2 + z * (35 + z * (7 + z * (21 + z * (15 + z * (0 + z * 32)))))))))))))))))))

def pow3_40_q {R : Type*} [CommRing R] (z : R) : R := (1 + z * (13 + z * (13 + z * (15 + z * (24 + z * (4 + z * (27 + z * (33 + z * (0 + z * (38 + z * (6 + z * (19 + z * (19 + z * (14 + z * (14 + z * (39 + z * (8 + z * (25 + z * 4))))))))))))))))))

def pow3_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (13 + z * (3 + z * ((-3) + z * (19 + z * ((-10) + z * ((-18) + z * (17 + z * ((-24) + z * ((-9) + z * (22 + z * ((-5) + z * (2 + z * (41 + z * ((-50) + z * (20 + z * ((-13) + z * ((-14) + z * (0 + z * (29 + z * (25 + z * (4 + z * (8 + z * (12 + z * ((-5) + z * ((-18) + z * (42 + z * (12 + z * (61 + z * ((-1) + z * (3 + z * (32 + z * ((-11) + z * ((-4) + z * (12 + z * (53 + z * (40 + z * (31 + z * (25 + z * 37))))))))))))))))))))))))))))))))))))))

theorem pow3_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_20 z * pow3_20 z = pow3_40_q z * f z + pow3_40 z + (41 : R) * pow3_40_mul_t z := by
  simp only [pow3_20, pow3_40_q, f, pow3_40, pow3_40_mul_t]
  
  ring

theorem pow3_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow3_20 z * pow3_20 z = pow3_40_q z * f z + pow3_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow3_40_mul_integer z


theorem pow3_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow3_20 z * pow3_20 z = pow3_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_40_mul z


def pow3_41 {R : Type*} [CommRing R] (z : R) : R := (35 + z * (35 + z * (24 + z * (19 + z * (15 + z * (18 + z * (10 + z * (35 + z * (35 + z * (6 + z * (11 + z * (30 + z * (0 + z * (27 + z * (14 + z * (18 + z * (19 + z * (32 + z * (4 + z * 12)))))))))))))))))))

def pow3_41_q {R : Type*} [CommRing R] (z : R) : R := (22 + z * (36 + z * (1 + z * (5 + z * (11 + z * (38 + z * (25 + z * (0 + z * (36 + z * (15 + z * (27 + z * (19 + z * (6 + z * (8 + z * (14 + z * (9 + z * (22 + z * (21 + z * 26))))))))))))))))))

def pow3_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * ((-34) + z * ((-10) + z * ((-7) + z * (4 + z * ((-15) + z * (25 + z * (32 + z * (8 + z * (34 + z * (20 + z * (43 + z * ((-3) + z * (54 + z * (71 + z * (36 + z * (6 + z * (38 + z * (52 + z * (22 + z * (70 + z * (83 + z * (53 + z * (90 + z * (28 + z * (10 + z * (42 + z * (16 + z * (31 + z * (25 + z * (42 + z * (36 + z * (12 + z * (5 + z * (3 + z * (15 + z * (5 + z * (7 + z * 22))))))))))))))))))))))))))))))))))))))


abbrev u3 {R : Type*} [CommRing R] (z : R) : R := pow3_41 z


def pow4_2 {R : Type*} [CommRing R] (z : R) : R := (17 + z * (10 + z * (26 + z * (3 + z * (18 + z * (24 + z * (20 + z * (23 + z * (24 + z * (34 + z * (24 + z * (31 + z * (4 + z * (0 + z * (23 + z * (32 + z * (18 + z * (2 + z * (2 + z * 23)))))))))))))))))))

def pow4_2_q {R : Type*} [CommRing R] (z : R) : R := (29 + z * (22 + z * (8 + z * (0 + z * (3 + z * (7 + z * (3 + z * (39 + z * (19 + z * (15 + z * (10 + z * (33 + z * (33 + z * (3 + z * (4 + z * (25 + z * (6 + z * (40 + z * 21))))))))))))))))))

def pow4_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (4 + z * (31 + z * (35 + z * (54 + z * (40 + z * (50 + z * (57 + z * (46 + z * (87 + z * (54 + z * (65 + z * (34 + z * (25 + z * (66 + z * (58 + z * (46 + z * (43 + z * (41 + z * (58 + z * ((-2) + z * (39 + z * (38 + z * ((-5) + z * ((-15) + z * (26 + z * ((-24) + z * ((-55) + z * ((-33) + z * ((-29) + z * ((-42) + z * ((-2) + z * ((-38) + z * ((-16) + z * ((-26) + z * ((-21) + z * ((-16) + z * ((-19) + z * ((-14) + z * 3))))))))))))))))))))))))))))))))))))))

theorem pow4_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u3 z * u3 z = pow4_2_q z * f z + pow4_2 z + (41 : R) * pow4_2_mul_t z := by
  simp only [u3, pow4_2_q, f, pow4_2, pow4_2_mul_t]
  simp only [pow3_41]
  ring

theorem pow4_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u3 z * u3 z = pow4_2_q z * f z + pow4_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow4_2_mul_integer z


theorem pow4_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u3 z * u3 z = pow4_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_2_mul z


theorem pow4_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u3 z ^ 2 = pow4_2 z := by
  calc
    _ = u3 z ^ 1 * u3 z ^ 1 := by ring
    _ = u3 z * u3 z := by simp only [pow_one]
    _ = _ := pow4_2_root z hz


def pow4_4 {R : Type*} [CommRing R] (z : R) : R := (10 + z * (35 + z * (20 + z * (16 + z * (24 + z * (35 + z * (27 + z * (10 + z * (6 + z * (4 + z * (28 + z * (7 + z * (32 + z * (6 + z * (37 + z * (28 + z * (23 + z * (23 + z * (22 + z * 2)))))))))))))))))))

def pow4_4_q {R : Type*} [CommRing R] (z : R) : R := (18 + z * (35 + z * (39 + z * (38 + z * (18 + z * (11 + z * (25 + z * (37 + z * (1 + z * (33 + z * (39 + z * (34 + z * (32 + z * (12 + z * (17 + z * (16 + z * (36 + z * (7 + z * 37))))))))))))))))))

def pow4_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-9) + z * ((-29) + z * ((-35) + z * ((-57) + z * ((-39) + z * ((-42) + z * ((-24) + z * ((-37) + z * ((-20) + z * ((-29) + z * ((-32) + z * ((-41) + z * ((-38) + z * ((-37) + z * ((-63) + z * ((-8) + z * ((-41) + z * ((-71) + z * ((-129) + z * ((-57) + z * ((-81) + z * ((-49) + z * ((-91) + z * ((-50) + z * ((-21) + z * ((-58) + z * ((-75) + z * ((-82) + z * ((-80) + z * ((-66) + z * ((-29) + z * ((-59) + z * ((-70) + z * ((-47) + z * ((-23) + z * ((-30) + z * ((-19) + z * ((-25) + z * 12))))))))))))))))))))))))))))))))))))))

theorem pow4_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_2 z * pow4_2 z = pow4_4_q z * f z + pow4_4 z + (41 : R) * pow4_4_mul_t z := by
  simp only [pow4_2, pow4_4_q, f, pow4_4, pow4_4_mul_t]
  
  ring

theorem pow4_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow4_2 z * pow4_2 z = pow4_4_q z * f z + pow4_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow4_4_mul_integer z


theorem pow4_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow4_2 z * pow4_2 z = pow4_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_4_mul z


theorem pow4_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u3 z ^ 4 = pow4_4 z := by
  calc
    _ = u3 z ^ 2 * u3 z ^ 2 := by ring
    _ = pow4_2 z * pow4_2 z := by rw [pow4_2_pow z hz]
    _ = _ := pow4_4_root z hz


def pow4_5 {R : Type*} [CommRing R] (z : R) : R := (2 + z * (24 + z * (18 + z * (11 + z * (37 + z * (8 + z * (24 + z * (2 + z * (33 + z * (23 + z * (40 + z * (34 + z * (22 + z * (40 + z * (7 + z * (19 + z * (13 + z * (14 + z * (33 + z * 6)))))))))))))))))))

def pow4_5_q {R : Type*} [CommRing R] (z : R) : R := (37 + z * (32 + z * (7 + z * (16 + z * (33 + z * (15 + z * (38 + z * (40 + z * (21 + z * (34 + z * (14 + z * (8 + z * (23 + z * (22 + z * (38 + z * (24 + z * (12 + z * (3 + z * 24))))))))))))))))))

def pow4_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-24) + z * ((-2) + z * (9 + z * (15 + z * ((-4) + z * (21 + z * (26 + z * ((-8) + z * ((-27) + z * ((-12) + z * ((-6) + z * ((-37) + z * (20 + z * ((-1) + z * ((-29) + z * ((-31) + z * ((-46) + z * (0 + z * ((-10) + z * ((-19) + z * ((-40) + z * ((-20) + z * ((-50) + z * ((-40) + z * ((-57) + z * ((-46) + z * ((-54) + z * ((-14) + z * ((-35) + z * ((-20) + z * ((-32) + z * (1 + z * ((-16) + z * ((-16) + z * ((-5) + z * (3 + z * ((-2) + z * ((-11) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow4_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_4 z * u3 z = pow4_5_q z * f z + pow4_5 z + (41 : R) * pow4_5_mul_t z := by
  simp only [pow4_4, u3, pow4_5_q, f, pow4_5, pow4_5_mul_t]
  simp only [pow3_41]
  ring

theorem pow4_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow4_4 z * u3 z = pow4_5_q z * f z + pow4_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow4_5_mul_integer z


theorem pow4_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow4_4 z * u3 z = pow4_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_5_mul z


theorem pow4_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u3 z ^ 5 = pow4_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow4_4_pow z hz]
  exact pow4_5_root z hz


def pow4_10 {R : Type*} [CommRing R] (z : R) : R := (29 + z * (34 + z * (13 + z * (19 + z * (1 + z * (20 + z * (10 + z * (34 + z * (6 + z * (21 + z * (2 + z * (21 + z * (36 + z * (18 + z * (12 + z * (4 + z * (10 + z * (28 + z * (14 + z * 12)))))))))))))))))))

def pow4_10_q {R : Type*} [CommRing R] (z : R) : R := (5 + z * (17 + z * (21 + z * (29 + z * (37 + z * (17 + z * (7 + z * (7 + z * (38 + z * (24 + z * (27 + z * (15 + z * (5 + z * (4 + z * (6 + z * (7 + z * (9 + z * (13 + z * 36))))))))))))))))))

def pow4_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-5) + z * ((-15) + z * ((-12) + z * ((-23) + z * ((-37) + z * ((-9) + z * ((-11) + z * (3 + z * ((-26) + z * ((-14) + z * ((-2) + z * ((-6) + z * (41 + z * (40 + z * (107 + z * (39 + z * (54 + z * (58 + z * ((-5) + z * (68 + z * (26 + z * (98 + z * (65 + z * (70 + z * (61 + z * (10 + z * (68 + z * (33 + z * (70 + z * (38 + z * (39 + z * (51 + z * ((-10) + z * ((-13) + z * ((-14) + z * ((-6) + z * (6 + z * ((-17) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow4_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_5 z * pow4_5 z = pow4_10_q z * f z + pow4_10 z + (41 : R) * pow4_10_mul_t z := by
  simp only [pow4_5, pow4_10_q, f, pow4_10, pow4_10_mul_t]
  
  ring

theorem pow4_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow4_5 z * pow4_5 z = pow4_10_q z * f z + pow4_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow4_10_mul_integer z


theorem pow4_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow4_5 z * pow4_5 z = pow4_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_10_mul z


theorem pow4_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u3 z ^ 10 = pow4_10 z := by
  calc
    _ = u3 z ^ 5 * u3 z ^ 5 := by ring
    _ = pow4_5 z * pow4_5 z := by rw [pow4_5_pow z hz]
    _ = _ := pow4_10_root z hz


def pow4_20 {R : Type*} [CommRing R] (z : R) : R := (32 + z * (38 + z * (32 + z * (16 + z * (3 + z * (18 + z * (26 + z * (32 + z * (8 + z * (25 + z * (31 + z * (6 + z * (0 + z * (12 + z * (3 + z * (21 + z * (0 + z * (31 + z * (4 + z * 31)))))))))))))))))))

def pow4_20_q {R : Type*} [CommRing R] (z : R) : R := (35 + z * (24 + z * (28 + z * (2 + z * (25 + z * (37 + z * (13 + z * (33 + z * (1 + z * (29 + z * (25 + z * (9 + z * (20 + z * (40 + z * (11 + z * (22 + z * (24 + z * (34 + z * 21))))))))))))))))))

def pow4_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-11) + z * (15 + z * ((-12) + z * (19 + z * ((-34) + z * ((-24) + z * ((-11) + z * ((-17) + z * (11 + z * ((-55) + z * (0 + z * ((-66) + z * (15 + z * ((-20) + z * ((-8) + z * ((-74) + z * ((-91) + z * ((-101) + z * ((-34) + z * ((-46) + z * ((-84) + z * ((-96) + z * ((-69) + z * ((-63) + z * ((-58) + z * ((-57) + z * ((-50) + z * ((-74) + z * ((-73) + z * ((-45) + z * ((-26) + z * ((-49) + z * ((-82) + z * ((-54) + z * ((-34) + z * ((-19) + z * ((-13) + z * ((-8) + z * 3))))))))))))))))))))))))))))))))))))))

theorem pow4_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_10 z * pow4_10 z = pow4_20_q z * f z + pow4_20 z + (41 : R) * pow4_20_mul_t z := by
  simp only [pow4_10, pow4_20_q, f, pow4_20, pow4_20_mul_t]
  
  ring

theorem pow4_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow4_10 z * pow4_10 z = pow4_20_q z * f z + pow4_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow4_20_mul_integer z


theorem pow4_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow4_10 z * pow4_10 z = pow4_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_20_mul z


theorem pow4_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u3 z ^ 20 = pow4_20 z := by
  calc
    _ = u3 z ^ 10 * u3 z ^ 10 := by ring
    _ = pow4_10 z * pow4_10 z := by rw [pow4_10_pow z hz]
    _ = _ := pow4_20_root z hz


def pow4_40 {R : Type*} [CommRing R] (z : R) : R := (29 + z * (16 + z * (36 + z * (27 + z * (30 + z * (3 + z * (37 + z * (6 + z * (38 + z * (24 + z * (37 + z * (29 + z * (18 + z * (36 + z * (30 + z * (18 + z * (20 + z * (0 + z * (23 + z * 16)))))))))))))))))))

def pow4_40_q {R : Type*} [CommRing R] (z : R) : R := (6 + z * (8 + z * (38 + z * (28 + z * (8 + z * (3 + z * (27 + z * (33 + z * (37 + z * (4 + z * (18 + z * (37 + z * (25 + z * (35 + z * (40 + z * (5 + z * (19 + z * (36 + z * 18))))))))))))))))))

def pow4_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (19 + z * (50 + z * (44 + z * (41 + z * (10 + z * (25 + z * (22 + z * (57 + z * (43 + z * (46 + z * (31 + z * (30 + z * (8 + z * ((-40) + z * ((-71) + z * ((-32) + z * ((-20) + z * ((-44) + z * ((-105) + z * ((-26) + z * ((-12) + z * ((-111) + z * ((-94) + z * ((-86) + z * ((-58) + z * ((-91) + z * ((-56) + z * ((-88) + z * ((-83) + z * ((-87) + z * ((-80) + z * ((-95) + z * ((-53) + z * ((-79) + z * (8 + z * ((-33) + z * (13 + z * ((-8) + z * 23))))))))))))))))))))))))))))))))))))))

theorem pow4_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_20 z * pow4_20 z = pow4_40_q z * f z + pow4_40 z + (41 : R) * pow4_40_mul_t z := by
  simp only [pow4_20, pow4_40_q, f, pow4_40, pow4_40_mul_t]
  
  ring

theorem pow4_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow4_20 z * pow4_20 z = pow4_40_q z * f z + pow4_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow4_40_mul_integer z


theorem pow4_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow4_20 z * pow4_20 z = pow4_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_40_mul z


theorem pow4_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u3 z ^ 40 = pow4_40 z := by
  calc
    _ = u3 z ^ 20 * u3 z ^ 20 := by ring
    _ = pow4_20 z * pow4_20 z := by rw [pow4_20_pow z hz]
    _ = _ := pow4_40_root z hz


def pow4_41_q {R : Type*} [CommRing R] (z : R) : R := (29 + z * (25 + z * (40 + z * (29 + z * (37 + z * (22 + z * (10 + z * (28 + z * (20 + z * (39 + z * (6 + z * (5 + z * (5 + z * (17 + z * (18 + z * (23 + z * (40 + z * (33 + z * 28))))))))))))))))))

def pow4_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-1) + z * (7 + z * ((-3) + z * (19 + z * ((-7) + z * (2 + z * (12 + z * (10 + z * (28 + z * (7 + z * (58 + z * (41 + z * (34 + z * (61 + z * (59 + z * (40 + z * ((-6) + z * (7 + z * ((-40) + z * (13 + z * ((-35) + z * (23 + z * ((-13) + z * ((-6) + z * ((-30) + z * ((-5) + z * (9 + z * (13 + z * ((-29) + z * (5 + z * ((-11) + z * ((-35) + z * ((-56) + z * ((-55) + z * ((-50) + z * ((-28) + z * ((-22) + z * ((-13) + z * 4))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Powers03
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

theorem pow5_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_2 z * pow5_2 z = pow5_4_q z * f z + pow5_4 z + (41 : R) * pow5_4_mul_t z := by
  simp only [pow5_2, pow5_4_q, f, pow5_4, pow5_4_mul_t]
  
  ring

theorem pow5_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow5_2 z * pow5_2 z = pow5_4_q z * f z + pow5_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow5_4_mul_integer z


theorem pow5_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow5_2 z * pow5_2 z = pow5_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_4_mul z


def pow5_5 {R : Type*} [CommRing R] (z : R) : R := (13 + z * (26 + z * (29 + z * (37 + z * (16 + z * (21 + z * (12 + z * (18 + z * (5 + z * (11 + z * (37 + z * (36 + z * (22 + z * (18 + z * (4 + z * (40 + z * (16 + z * (30 + z * (8 + z * 17)))))))))))))))))))

def pow5_5_q {R : Type*} [CommRing R] (z : R) : R := (25 + z * (28 + z * (1 + z * (8 + z * (17 + z * (8 + z * (5 + z * (3 + z * (3 + z * (32 + z * (24 + z * (33 + z * (32 + z * (17 + z * (2 + z * (16 + z * (12 + z * (19 + z * 34))))))))))))))))))

def pow5_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-17) + z * ((-21) + z * ((-20) + z * ((-12) + z * ((-5) + z * (1 + z * (44 + z * (32 + z * (21 + z * (43 + z * (44 + z * (27 + z * (31 + z * (27 + z * (81 + z * (61 + z * (61 + z * (72 + z * (59 + z * (63 + z * (70 + z * (126 + z * (100 + z * (101 + z * (84 + z * (37 + z * (27 + z * (41 + z * (15 + z * (7 + z * (24 + z * (22 + z * (13 + z * (15 + z * (15 + z * (13 + z * ((-2) + z * ((-14) + z * 4))))))))))))))))))))))))))))))))))))))


def pow5_10 {R : Type*} [CommRing R] (z : R) : R := (27 + z * (39 + z * (12 + z * (34 + z * (7 + z * (23 + z * (1 + z * (25 + z * (27 + z * (20 + z * (3 + z * (7 + z * (26 + z * (31 + z * (20 + z * (0 + z * (23 + z * (5 + z * (13 + z * 26)))))))))))))))))))

def pow5_10_q {R : Type*} [CommRing R] (z : R) : R := (29 + z * (30 + z * (34 + z * (33 + z * (27 + z * (9 + z * (17 + z * (0 + z * (28 + z * (7 + z * (37 + z * (26 + z * (33 + z * (25 + z * (1 + z * (13 + z * (20 + z * (7 + z * 2))))))))))))))))))

def pow5_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-22) + z * ((-20) + z * ((-26) + z * ((-3) + z * ((-5) + z * (17 + z * (21 + z * (18 + z * ((-15) + z * (0 + z * ((-35) + z * ((-2) + z * ((-4) + z * (41 + z * (28 + z * (5 + z * (14 + z * ((-2) + z * (32 + z * ((-16) + z * (31 + z * (35 + z * (56 + z * (1 + z * (5 + z * (19 + z * (31 + z * (5 + z * (29 + z * (6 + z * (33 + z * ((-6) + z * (31 + z * (17 + z * (38 + z * (6 + z * (20 + z * (5 + z * 7))))))))))))))))))))))))))))))))))))))

theorem pow5_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_5 z * pow5_5 z = pow5_10_q z * f z + pow5_10 z + (41 : R) * pow5_10_mul_t z := by
  simp only [pow5_5, pow5_10_q, f, pow5_10, pow5_10_mul_t]
  
  ring

theorem pow5_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow5_5 z * pow5_5 z = pow5_10_q z * f z + pow5_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow5_10_mul_integer z


theorem pow5_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow5_5 z * pow5_5 z = pow5_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_10_mul z


def pow5_20 {R : Type*} [CommRing R] (z : R) : R := (32 + z * (1 + z * (28 + z * (37 + z * (29 + z * (8 + z * (21 + z * (8 + z * (15 + z * (35 + z * (9 + z * (6 + z * (35 + z * (25 + z * (34 + z * (32 + z * (27 + z * (13 + z * (9 + z * 13)))))))))))))))))))

def pow5_20_q {R : Type*} [CommRing R] (z : R) : R := (0 + z * (30 + z * (27 + z * (23 + z * (17 + z * (8 + z * (28 + z * (28 + z * (39 + z * (31 + z * (6 + z * (18 + z * (24 + z * (29 + z * (21 + z * (32 + z * (23 + z * (35 + z * 20))))))))))))))))))

def pow5_20_mul_t {R : Type*} [CommRing R] (z : R) : R := (17 + z * (25 + z * (19 + z * (16 + z * (34 + z * (10 + z * (12 + z * ((-2) + z * (18 + z * ((-5) + z * (5 + z * ((-29) + z * ((-1) + z * ((-9) + z * (20 + z * ((-33) + z * ((-36) + z * ((-64) + z * ((-103) + z * ((-44) + z * ((-52) + z * ((-29) + z * ((-78) + z * ((-102) + z * ((-89) + z * ((-84) + z * ((-48) + z * ((-63) + z * ((-73) + z * ((-69) + z * ((-56) + z * ((-55) + z * ((-45) + z * ((-57) + z * ((-54) + z * ((-11) + z * ((-24) + z * (1 + z * 16))))))))))))))))))))))))))))))))))))))

theorem pow5_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_10 z * pow5_10 z = pow5_20_q z * f z + pow5_20 z + (41 : R) * pow5_20_mul_t z := by
  simp only [pow5_10, pow5_20_q, f, pow5_20, pow5_20_mul_t]
  
  ring

theorem pow5_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow5_10 z * pow5_10 z = pow5_20_q z * f z + pow5_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow5_20_mul_integer z


theorem pow5_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow5_10 z * pow5_10 z = pow5_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_20_mul z


def pow5_40 {R : Type*} [CommRing R] (z : R) : R := (14 + z * (4 + z * (21 + z * (27 + z * (36 + z * (31 + z * (32 + z * (22 + z * (1 + z * (40 + z * (32 + z * (14 + z * (14 + z * (17 + z * (8 + z * (39 + z * (30 + z * (19 + z * (34 + z * 15)))))))))))))))))))

def pow5_40_q {R : Type*} [CommRing R] (z : R) : R := (3 + z * (4 + z * (2 + z * (26 + z * (15 + z * (38 + z * (36 + z * (36 + z * (40 + z * (7 + z * (3 + z * (38 + z * (28 + z * (9 + z * (12 + z * (29 + z * (28 + z * (2 + z * 5))))))))))))))))))

def pow5_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (22 + z * ((-3) + z * (38 + z * (32 + z * (40 + z * (3 + z * (48 + z * ((-18) + z * ((-6) + z * (32 + z * ((-11) + z * (1 + z * (40 + z * (8 + z * (32 + z * (36 + z * (52 + z * (72 + z * (72 + z * (21 + z * ((-3) + z * (32 + z * ((-44) + z * ((-46) + z * ((-8) + z * (3 + z * ((-13) + z * (4 + z * (59 + z * (38 + z * (6 + z * (15 + z * (13 + z * (10 + z * ((-2) + z * ((-2) + z * (6 + z * (2 + z * 4))))))))))))))))))))))))))))))))))))))

theorem pow5_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_20 z * pow5_20 z = pow5_40_q z * f z + pow5_40 z + (41 : R) * pow5_40_mul_t z := by
  simp only [pow5_20, pow5_40_q, f, pow5_40, pow5_40_mul_t]
  
  ring

theorem pow5_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow5_20 z * pow5_20 z = pow5_40_q z * f z + pow5_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow5_40_mul_integer z


theorem pow5_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow5_20 z * pow5_20 z = pow5_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_40_mul z


def pow5_41 {R : Type*} [CommRing R] (z : R) : R := (23 + z * (27 + z * (33 + z * (10 + z * (7 + z * (20 + z * (9 + z * (5 + z * (10 + z * (21 + z * (32 + z * (35 + z * (17 + z * (32 + z * (1 + z * (24 + z * (30 + z * (12 + z * (4 + z * 21)))))))))))))))))))

def pow5_41_q {R : Type*} [CommRing R] (z : R) : R := (12 + z * (29 + z * (18 + z * (36 + z * (36 + z * (38 + z * (17 + z * (34 + z * (14 + z * (26 + z * (40 + z * (36 + z * (19 + z * (27 + z * (23 + z * (33 + z * (40 + z * (13 + z * 2))))))))))))))))))

def pow5_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-7) + z * ((-25) + z * ((-26) + z * ((-39) + z * ((-37) + z * ((-50) + z * ((-10) + z * ((-25) + z * (2 + z * (2 + z * (26 + z * ((-19) + z * ((-15) + z * ((-3) + z * ((-3) + z * (1 + z * ((-12) + z * ((-10) + z * ((-15) + z * (10 + z * (36 + z * (71 + z * (47 + z * (58 + z * (44 + z * (20 + z * (11 + z * (15 + z * (23 + z * (20 + z * (3 + z * (3 + z * (21 + z * (48 + z * (46 + z * (34 + z * (42 + z * (30 + z * 8))))))))))))))))))))))))))))))))))))))


abbrev u5 {R : Type*} [CommRing R] (z : R) : R := pow5_41 z


def pow6_2 {R : Type*} [CommRing R] (z : R) : R := (28 + z * (29 + z * (33 + z * (21 + z * (21 + z * (30 + z * (33 + z * (2 + z * (0 + z * (10 + z * (14 + z * (38 + z * (36 + z * (33 + z * (38 + z * (34 + z * (17 + z * (32 + z * (35 + z * 2)))))))))))))))))))

def pow6_2_q {R : Type*} [CommRing R] (z : R) : R := (31 + z * (2 + z * (19 + z * (17 + z * (12 + z * (33 + z * (34 + z * (31 + z * (32 + z * (1 + z * (13 + z * (11 + z * (19 + z * (37 + z * (1 + z * (38 + z * (16 + z * (17 + z * 31))))))))))))))))))

def pow6_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * (18 + z * (14 + z * (31 + z * ((-7) + z * ((-4) + z * ((-16) + z * ((-50) + z * ((-49) + z * ((-31) + z * ((-7) + z * (38 + z * (21 + z * (23 + z * ((-8) + z * ((-38) + z * ((-8) + z * ((-43) + z * ((-17) + z * ((-57) + z * ((-32) + z * (4 + z * ((-66) + z * ((-50) + z * ((-32) + z * ((-31) + z * (3 + z * ((-14) + z * (13 + z * ((-13) + z * ((-21) + z * ((-31) + z * ((-27) + z * ((-44) + z * ((-35) + z * ((-4) + z * ((-13) + z * ((-19) + z * 10))))))))))))))))))))))))))))))))))))))

theorem pow6_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u5 z * u5 z = pow6_2_q z * f z + pow6_2 z + (41 : R) * pow6_2_mul_t z := by
  simp only [u5, pow6_2_q, f, pow6_2, pow6_2_mul_t]
  simp only [pow5_41]
  ring

theorem pow6_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u5 z * u5 z = pow6_2_q z * f z + pow6_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow6_2_mul_integer z


theorem pow6_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u5 z * u5 z = pow6_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_2_mul z


theorem pow6_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u5 z ^ 2 = pow6_2 z := by
  calc
    _ = u5 z ^ 1 * u5 z ^ 1 := by ring
    _ = u5 z * u5 z := by simp only [pow_one]
    _ = _ := pow6_2_root z hz


def pow6_4 {R : Type*} [CommRing R] (z : R) : R := (22 + z * (6 + z * (3 + z * (6 + z * (26 + z * (35 + z * (21 + z * (3 + z * (40 + z * (10 + z * (16 + z * (28 + z * (7 + z * (26 + z * (2 + z * (11 + z * (10 + z * (11 + z * (5 + z * 32)))))))))))))))))))

def pow6_4_q {R : Type*} [CommRing R] (z : R) : R := (28 + z * (28 + z * (7 + z * (26 + z * (13 + z * (16 + z * (10 + z * (28 + z * (23 + z * (3 + z * (16 + z * (35 + z * (16 + z * (25 + z * (31 + z * (22 + z * (29 + z * (20 + z * 4))))))))))))))))))

def pow6_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-6) + z * (6 + z * (30 + z * (29 + z * (37 + z * (41 + z * (98 + z * (35 + z * (10 + z * (9 + z * (6 + z * (19 + z * (47 + z * (77 + z * (83 + z * (86 + z * (112 + z * (138 + z * (111 + z * (94 + z * (90 + z * (45 + z * (27 + z * (68 + z * (57 + z * (33 + z * (49 + z * (63 + z * (91 + z * (102 + z * (63 + z * (51 + z * (41 + z * (20 + z * (14 + z * (24 + z * (16 + z * (0 + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow6_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_2 z * pow6_2 z = pow6_4_q z * f z + pow6_4 z + (41 : R) * pow6_4_mul_t z := by
  simp only [pow6_2, pow6_4_q, f, pow6_4, pow6_4_mul_t]
  
  ring

theorem pow6_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow6_2 z * pow6_2 z = pow6_4_q z * f z + pow6_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow6_4_mul_integer z


theorem pow6_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow6_2 z * pow6_2 z = pow6_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_4_mul z


theorem pow6_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u5 z ^ 4 = pow6_4 z := by
  calc
    _ = u5 z ^ 2 * u5 z ^ 2 := by ring
    _ = pow6_2 z * pow6_2 z := by rw [pow6_2_pow z hz]
    _ = _ := pow6_4_root z hz


def pow6_5 {R : Type*} [CommRing R] (z : R) : R := (1 + z * (19 + z * (23 + z * (15 + z * (7 + z * (30 + z * (31 + z * (21 + z * (9 + z * (20 + z * (11 + z * (1 + z * (17 + z * (19 + z * (12 + z * (8 + z * (17 + z * (31 + z * (11 + z * 40)))))))))))))))))))

def pow6_5_q {R : Type*} [CommRing R] (z : R) : R := (22 + z * (13 + z * (20 + z * (10 + z * (27 + z * (7 + z * (10 + z * (10 + z * (40 + z * (37 + z * (5 + z * (9 + z * (23 + z * (19 + z * (17 + z * (39 + z * (24 + z * (40 + z * 16))))))))))))))))))

def pow6_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-7) + z * ((-1) + z * ((-15) + z * ((-10) + z * ((-33) + z * (18 + z * (16 + z * (10 + z * ((-26) + z * ((-18) + z * (12 + z * ((-8) + z * ((-26) + z * (8 + z * (0 + z * ((-31) + z * ((-46) + z * ((-59) + z * ((-38) + z * ((-61) + z * ((-29) + z * (19 + z * ((-41) + z * ((-54) + z * ((-37) + z * ((-68) + z * ((-51) + z * ((-55) + z * ((-54) + z * ((-30) + z * ((-33) + z * ((-76) + z * ((-52) + z * ((-72) + z * ((-42) + z * ((-13) + z * ((-21) + z * ((-7) + z * 16))))))))))))))))))))))))))))))))))))))

theorem pow6_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_4 z * u5 z = pow6_5_q z * f z + pow6_5 z + (41 : R) * pow6_5_mul_t z := by
  simp only [pow6_4, u5, pow6_5_q, f, pow6_5, pow6_5_mul_t]
  simp only [pow5_41]
  ring

theorem pow6_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow6_4 z * u5 z = pow6_5_q z * f z + pow6_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow6_5_mul_integer z


theorem pow6_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow6_4 z * u5 z = pow6_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_5_mul z


theorem pow6_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u5 z ^ 5 = pow6_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow6_4_pow z hz]
  exact pow6_5_root z hz


def pow6_10 {R : Type*} [CommRing R] (z : R) : R := (40 + z * (33 + z * (7 + z * (33 + z * (11 + z * (34 + z * (8 + z * (18 + z * (23 + z * (39 + z * (27 + z * (5 + z * (29 + z * (22 + z * (9 + z * (24 + z * (14 + z * (15 + z * (32 + z * 29)))))))))))))))))))

def pow6_10_q {R : Type*} [CommRing R] (z : R) : R := (16 + z * (16 + z * (33 + z * (19 + z * (26 + z * (20 + z * (12 + z * (9 + z * (16 + z * (0 + z * (4 + z * (16 + z * (1 + z * (14 + z * (0 + z * (25 + z * (3 + z * (30 + z * 1))))))))))))))))))

def pow6_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * ((-19) + z * ((-36) + z * ((-18) + z * ((-39) + z * ((-31) + z * ((-22) + z * (9 + z * (7 + z * ((-5) + z * (7 + z * (10 + z * ((-1) + z * ((-16) + z * (20 + z * ((-28) + z * ((-21) + z * ((-63) + z * (2 + z * ((-20) + z * (25 + z * (16 + z * (39 + z * (37 + z * (50 + z * (57 + z * (42 + z * (5 + z * (19 + z * (20 + z * (2 + z * (20 + z * (9 + z * (16 + z * (11 + z * (34 + z * (41 + z * (20 + z * 39))))))))))))))))))))))))))))))))))))))

theorem pow6_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_5 z * pow6_5 z = pow6_10_q z * f z + pow6_10 z + (41 : R) * pow6_10_mul_t z := by
  simp only [pow6_5, pow6_10_q, f, pow6_10, pow6_10_mul_t]
  
  ring

theorem pow6_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow6_5 z * pow6_5 z = pow6_10_q z * f z + pow6_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow6_10_mul_integer z


theorem pow6_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow6_5 z * pow6_5 z = pow6_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_10_mul z


theorem pow6_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u5 z ^ 10 = pow6_10 z := by
  calc
    _ = u5 z ^ 5 * u5 z ^ 5 := by ring
    _ = pow6_5 z * pow6_5 z := by rw [pow6_5_pow z hz]
    _ = _ := pow6_10_root z hz


def pow6_20 {R : Type*} [CommRing R] (z : R) : R := (38 + z * (17 + z * (9 + z * (12 + z * (33 + z * (1 + z * (35 + z * (28 + z * (34 + z * (27 + z * (2 + z * (9 + z * (21 + z * (19 + z * (23 + z * (23 + z * (17 + z * (22 + z * (24 + z * 2)))))))))))))))))))

def pow6_20_q {R : Type*} [CommRing R] (z : R) : R := (32 + z * (26 + z * (30 + z * (16 + z * (30 + z * (7 + z * (1 + z * (17 + z * (4 + z * (24 + z * (31 + z * (4 + z * (0 + z * (25 + z * (34 + z * (27 + z * (17 + z * (37 + z * 21))))))))))))))))))

def pow6_20_mul_t {R : Type*} [CommRing R] (z : R) : R := (10 + z * (31 + z * ((-18) + z * (32 + z * ((-4) + z * (43 + z * (47 + z * (13 + z * (61 + z * (60 + z * (98 + z * (8 + z * (84 + z * (100 + z * (28 + z * (46 + z * (24 + z * ((-2) + z * (56 + z * (72 + z * (51 + z * (28 + z * (75 + z * (54 + z * (36 + z * (5 + z * (20 + z * (64 + z * (27 + z * ((-30) + z * ((-4) + z * (6 + z * ((-39) + z * ((-34) + z * ((-4) + z * (3 + z * (10 + z * (29 + z * 20))))))))))))))))))))))))))))))))))))))

theorem pow6_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_10 z * pow6_10 z = pow6_20_q z * f z + pow6_20 z + (41 : R) * pow6_20_mul_t z := by
  simp only [pow6_10, pow6_20_q, f, pow6_20, pow6_20_mul_t]
  
  ring

theorem pow6_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow6_10 z * pow6_10 z = pow6_20_q z * f z + pow6_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow6_20_mul_integer z


theorem pow6_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow6_10 z * pow6_10 z = pow6_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_20_mul z


theorem pow6_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u5 z ^ 20 = pow6_20 z := by
  calc
    _ = u5 z ^ 10 * u5 z ^ 10 := by ring
    _ = pow6_10 z * pow6_10 z := by rw [pow6_10_pow z hz]
    _ = _ := pow6_20_root z hz


def pow6_40 {R : Type*} [CommRing R] (z : R) : R := (6 + z * (32 + z * (4 + z * (29 + z * (16 + z * (36 + z * (33 + z * (13 + z * (13 + z * (22 + z * (24 + z * (31 + z * (27 + z * (24 + z * (16 + z * (4 + z * (29 + z * (37 + z * (39 + z * 37)))))))))))))))))))

def pow6_40_q {R : Type*} [CommRing R] (z : R) : R := (24 + z * (40 + z * (5 + z * (20 + z * (0 + z * (27 + z * (37 + z * (38 + z * (23 + z * (20 + z * (1 + z * (9 + z * (29 + z * (7 + z * (28 + z * (8 + z * (4 + z * (17 + z * 4))))))))))))))))))

def pow6_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (14 + z * ((-12) + z * ((-11) + z * ((-20) + z * (43 + z * ((-39) + z * (32 + z * ((-1) + z * (22 + z * (7 + z * (18 + z * ((-6) + z * (28 + z * (37 + z * (8 + z * (50 + z * ((-9) + z * (10 + z * (33 + z * ((-6) + z * (16 + z * (29 + z * (13 + z * (6 + z * (13 + z * (4 + z * (15 + z * (8 + z * ((-18) + z * (9 + z * (19 + z * (7 + z * (18 + z * (4 + z * (13 + z * (15 + z * (2 + z * ((-1) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow6_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_20 z * pow6_20 z = pow6_40_q z * f z + pow6_40 z + (41 : R) * pow6_40_mul_t z := by
  simp only [pow6_20, pow6_40_q, f, pow6_40, pow6_40_mul_t]
  
  ring

theorem pow6_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow6_20 z * pow6_20 z = pow6_40_q z * f z + pow6_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow6_40_mul_integer z


theorem pow6_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow6_20 z * pow6_20 z = pow6_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_40_mul z


theorem pow6_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u5 z ^ 40 = pow6_40 z := by
  calc
    _ = u5 z ^ 20 * u5 z ^ 20 := by ring
    _ = pow6_20 z * pow6_20 z := by rw [pow6_20_pow z hz]
    _ = _ := pow6_40_root z hz


def pow6_41 {R : Type*} [CommRing R] (z : R) : R := (31 + z * (37 + z * (38 + z * (22 + z * (29 + z * (11 + z * (22 + z * (17 + z * (6 + z * (17 + z * (3 + z * (35 + z * (14 + z * (6 + z * (30 + z * (1 + z * (28 + z * (6 + z * (2 + z * 36)))))))))))))))))))

def pow6_41_q {R : Type*} [CommRing R] (z : R) : R := (36 + z * (28 + z * (0 + z * (31 + z * (18 + z * (12 + z * (31 + z * (39 + z * (9 + z * (9 + z * (19 + z * (23 + z * (36 + z * (5 + z * (0 + z * (29 + z * (39 + z * (2 + z * 39))))))))))))))))))

def pow6_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-29) + z * ((-15) + z * ((-8) + z * ((-3) + z * ((-15) + z * ((-2) + z * (30 + z * ((-31) + z * ((-27) + z * ((-5) + z * ((-5) + z * ((-14) + z * (6 + z * (35 + z * (12 + z * ((-19) + z * (1 + z * (7 + z * ((-5) + z * (20 + z * (16 + z * (70 + z * ((-6) + z * ((-13) + z * (37 + z * ((-6) + z * ((-17) + z * (26 + z * (58 + z * (48 + z * (19 + z * ((-7) + z * (10 + z * ((-2) + z * ((-4) + z * (5 + z * (15 + z * ((-5) + z * 18))))))))))))))))))))))))))))))))))))))

theorem pow6_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow6_40 z * u5 z = pow6_41_q z * f z + pow6_41 z + (41 : R) * pow6_41_mul_t z := by
  simp only [pow6_40, u5, pow6_41_q, f, pow6_41, pow6_41_mul_t]
  simp only [pow5_41]
  ring

theorem pow6_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow6_40 z * u5 z = pow6_41_q z * f z + pow6_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow6_41_mul_integer z


theorem pow6_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow6_40 z * u5 z = pow6_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow6_41_mul z


theorem pow6_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u5 z ^ 41 = pow6_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow6_40_pow z hz]
  exact pow6_41_root z hz


abbrev u6 {R : Type*} [CommRing R] (z : R) : R := pow6_41 z

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Powers04
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

theorem pow7_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u6 z * u6 z = pow7_2_q z * f z + pow7_2 z + (41 : R) * pow7_2_mul_t z := by
  simp only [u6, pow7_2_q, f, pow7_2, pow7_2_mul_t]
  simp only [pow6_41]
  ring

theorem pow7_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u6 z * u6 z = pow7_2_q z * f z + pow7_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow7_2_mul_integer z


theorem pow7_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u6 z * u6 z = pow7_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_2_mul z


theorem pow7_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u6 z ^ 2 = pow7_2 z := by
  calc
    _ = u6 z ^ 1 * u6 z ^ 1 := by ring
    _ = u6 z * u6 z := by simp only [pow_one]
    _ = _ := pow7_2_root z hz


def pow7_4 {R : Type*} [CommRing R] (z : R) : R := (27 + z * (26 + z * (13 + z * (34 + z * (5 + z * (36 + z * (19 + z * (32 + z * (7 + z * (7 + z * (18 + z * (29 + z * (24 + z * (35 + z * (3 + z * (34 + z * (18 + z * (39 + z * (18 + z * 12)))))))))))))))))))

def pow7_4_q {R : Type*} [CommRing R] (z : R) : R := (22 + z * (14 + z * (12 + z * (1 + z * (18 + z * (29 + z * (24 + z * (25 + z * (36 + z * (22 + z * (24 + z * (37 + z * (12 + z * (9 + z * (15 + z * (36 + z * (24 + z * (30 + z * 9))))))))))))))))))

def pow7_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-18) + z * ((-12) + z * ((-9) + z * (14 + z * ((-5) + z * ((-12) + z * (6 + z * ((-12) + z * ((-59) + z * ((-42) + z * ((-13) + z * ((-26) + z * ((-48) + z * (19 + z * (17 + z * ((-24) + z * ((-33) + z * ((-11) + z * (23 + z * (15 + z * (62 + z * (50 + z * (32 + z * (14 + z * (30 + z * ((-15) + z * (24 + z * (47 + z * (102 + z * (73 + z * (92 + z * (54 + z * (71 + z * (45 + z * (63 + z * (75 + z * (71 + z * (52 + z * 35))))))))))))))))))))))))))))))))))))))

theorem pow7_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_2 z * pow7_2 z = pow7_4_q z * f z + pow7_4 z + (41 : R) * pow7_4_mul_t z := by
  simp only [pow7_2, pow7_4_q, f, pow7_4, pow7_4_mul_t]
  
  ring

theorem pow7_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow7_2 z * pow7_2 z = pow7_4_q z * f z + pow7_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow7_4_mul_integer z


theorem pow7_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow7_2 z * pow7_2 z = pow7_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_4_mul z


theorem pow7_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u6 z ^ 4 = pow7_4 z := by
  calc
    _ = u6 z ^ 2 * u6 z ^ 2 := by ring
    _ = pow7_2 z * pow7_2 z := by rw [pow7_2_pow z hz]
    _ = _ := pow7_4_root z hz


def pow7_5 {R : Type*} [CommRing R] (z : R) : R := (22 + z * (30 + z * (3 + z * (37 + z * (35 + z * (28 + z * (36 + z * (17 + z * (37 + z * (21 + z * (33 + z * (23 + z * (40 + z * (30 + z * (33 + z * (13 + z * (12 + z * (14 + z * 30))))))))))))))))))

def pow7_5_q {R : Type*} [CommRing R] (z : R) : R := (1 + z * (33 + z * (16 + z * (1 + z * (32 + z * (8 + z * (0 + z * (19 + z * (18 + z * (38 + z * (16 + z * (28 + z * (14 + z * (12 + z * (19 + z * (39 + z * (40 + z * (12 + z * 22))))))))))))))))))

def pow7_5_mul_t {R : Type*} [CommRing R] (z : R) : R := (19 + z * (14 + z * (33 + z * (45 + z * (37 + z * (51 + z * (57 + z * (102 + z * (30 + z * (24 + z * (38 + z * (16 + z * (46 + z * (45 + z * (87 + z * (9 + z * (7 + z * (58 + z * ((-2) + z * (63 + z * ((-22) + z * (43 + z * (8 + z * ((-48) + z * (3 + z * ((-56) + z * ((-35) + z * ((-43) + z * ((-40) + z * ((-8) + z * ((-47) + z * ((-22) + z * ((-31) + z * ((-39) + z * ((-21) + z * ((-19) + z * (18 + z * (0 + z * 10))))))))))))))))))))))))))))))))))))))

theorem pow7_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_4 z * u6 z = pow7_5_q z * f z + pow7_5 z + (41 : R) * pow7_5_mul_t z := by
  simp only [pow7_4, u6, pow7_5_q, f, pow7_5, pow7_5_mul_t]
  simp only [pow6_41]
  ring

theorem pow7_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow7_4 z * u6 z = pow7_5_q z * f z + pow7_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow7_5_mul_integer z


theorem pow7_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow7_4 z * u6 z = pow7_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_5_mul z


theorem pow7_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u6 z ^ 5 = pow7_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow7_4_pow z hz]
  exact pow7_5_root z hz


def pow7_10 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (24 + z * (28 + z * (2 + z * (32 + z * (11 + z * (33 + z * (17 + z * (11 + z * (2 + z * (30 + z * (22 + z * (25 + z * (37 + z * (28 + z * (3 + z * (39 + z * (1 + z * (26 + z * 8)))))))))))))))))))

def pow7_10_q {R : Type*} [CommRing R] (z : R) : R := (19 + z * (28 + z * (27 + z * (12 + z * (24 + z * (23 + z * (31 + z * (9 + z * (39 + z * (12 + z * (11 + z * (1 + z * (10 + z * (6 + z * (26 + z * (39 + z * 39))))))))))))))))

def pow7_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-5) + z * (1 + z * ((-22) + z * (4 + z * (31 + z * (25 + z * (40 + z * (74 + z * (37 + z * (100 + z * (75 + z * (138 + z * (116 + z * (165 + z * (168 + z * (128 + z * (98 + z * (130 + z * (168 + z * (122 + z * (102 + z * (135 + z * (124 + z * (63 + z * (94 + z * (62 + z * (89 + z * (40 + z * (69 + z * (27 + z * (15 + z * ((-16) + z * ((-8) + z * ((-30) + z * ((-23) + z * ((-9) + z * 21))))))))))))))))))))))))))))))))))))

theorem pow7_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_5 z * pow7_5 z = pow7_10_q z * f z + pow7_10 z + (41 : R) * pow7_10_mul_t z := by
  simp only [pow7_5, pow7_10_q, f, pow7_10, pow7_10_mul_t]
  
  ring

theorem pow7_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow7_5 z * pow7_5 z = pow7_10_q z * f z + pow7_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow7_10_mul_integer z


theorem pow7_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow7_5 z * pow7_5 z = pow7_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_10_mul z


theorem pow7_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u6 z ^ 10 = pow7_10 z := by
  calc
    _ = u6 z ^ 5 * u6 z ^ 5 := by ring
    _ = pow7_5 z * pow7_5 z := by rw [pow7_5_pow z hz]
    _ = _ := pow7_10_root z hz


def pow7_20 {R : Type*} [CommRing R] (z : R) : R := (13 + z * (32 + z * (8 + z * (34 + z * (27 + z * (11 + z * (5 + z * (13 + z * (10 + z * (39 + z * (20 + z * (26 + z * (31 + z * (31 + z * (20 + z * (33 + z * (37 + z * (8 + z * (35 + z * 36)))))))))))))))))))

def pow7_20_q {R : Type*} [CommRing R] (z : R) : R := (14 + z * (3 + z * (37 + z * (15 + z * (10 + z * (4 + z * (24 + z * (6 + z * (40 + z * (11 + z * (9 + z * (30 + z * (4 + z * (8 + z * (10 + z * (13 + z * (34 + z * (13 + z * 23))))))))))))))))))

def pow7_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-12) + z * ((-2) + z * ((-23) + z * (5 + z * ((-23) + z * (20 + z * (5 + z * (17 + z * (19 + z * ((-11) + z * ((-16) + z * (5 + z * (40 + z * (2 + z * (80 + z * (27 + z * (25 + z * (47 + z * (24 + z * (6 + z * (80 + z * ((-5) + z * (40 + z * (19 + z * (53 + z * ((-9) + z * (43 + z * ((-10) + z * (34 + z * (43 + z * (17 + z * ((-1) + z * (17 + z * ((-46) + z * (1 + z * ((-27) + z * ((-3) + z * ((-7) + z * 1))))))))))))))))))))))))))))))))))))))

theorem pow7_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_10 z * pow7_10 z = pow7_20_q z * f z + pow7_20 z + (41 : R) * pow7_20_mul_t z := by
  simp only [pow7_10, pow7_20_q, f, pow7_20, pow7_20_mul_t]
  
  ring

theorem pow7_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow7_10 z * pow7_10 z = pow7_20_q z * f z + pow7_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow7_20_mul_integer z


theorem pow7_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow7_10 z * pow7_10 z = pow7_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_20_mul z


theorem pow7_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u6 z ^ 20 = pow7_20 z := by
  calc
    _ = u6 z ^ 10 * u6 z ^ 10 := by ring
    _ = pow7_10 z * pow7_10 z := by rw [pow7_10_pow z hz]
    _ = _ := pow7_20_root z hz


def pow7_40 {R : Type*} [CommRing R] (z : R) : R := (20 + z * (39 + z * (21 + z * (34 + z * (21 + z * (3 + z * (2 + z * (30 + z * (12 + z * (29 + z * (0 + z * (20 + z * (34 + z * (29 + z * (9 + z * (18 + z * (12 + z * (29 + z * (17 + z * 29)))))))))))))))))))

def pow7_40_q {R : Type*} [CommRing R] (z : R) : R := (3 + z * (5 + z * (2 + z * (34 + z * (12 + z * (22 + z * (23 + z * (5 + z * (22 + z * (33 + z * (15 + z * (6 + z * (13 + z * (37 + z * (3 + z * (22 + z * (18 + z * (7 + z * 25))))))))))))))))))

def pow7_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (1 + z * (14 + z * (24 + z * ((-1) + z * (46 + z * (10 + z * (20 + z * (7 + z * (7 + z * (3 + z * (17 + z * (26 + z * (71 + z * (52 + z * (75 + z * (60 + z * (102 + z * (54 + z * (85 + z * (133 + z * (70 + z * (98 + z * (107 + z * (83 + z * (56 + z * (81 + z * (85 + z * (111 + z * (125 + z * (88 + z * (100 + z * (106 + z * (58 + z * (56 + z * (75 + z * (48 + z * (28 + z * (43 + z * 31))))))))))))))))))))))))))))))))))))))

theorem pow7_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_20 z * pow7_20 z = pow7_40_q z * f z + pow7_40 z + (41 : R) * pow7_40_mul_t z := by
  simp only [pow7_20, pow7_40_q, f, pow7_40, pow7_40_mul_t]
  
  ring

theorem pow7_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow7_20 z * pow7_20 z = pow7_40_q z * f z + pow7_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow7_40_mul_integer z


theorem pow7_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow7_20 z * pow7_20 z = pow7_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_40_mul z


theorem pow7_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u6 z ^ 40 = pow7_40 z := by
  calc
    _ = u6 z ^ 20 * u6 z ^ 20 := by ring
    _ = pow7_20 z * pow7_20 z := by rw [pow7_20_pow z hz]
    _ = _ := pow7_40_root z hz


def pow7_41 {R : Type*} [CommRing R] (z : R) : R := (26 + z * (28 + z * (6 + z * (7 + z * (30 + z * (2 + z * (32 + z * (18 + z * (16 + z * (25 + z * (39 + z * (7 + z * (0 + z * (39 + z * (6 + z * (27 + z * (28 + z * (15 + z * (9 + z * 3)))))))))))))))))))

def pow7_41_q {R : Type*} [CommRing R] (z : R) : R := (37 + z * (40 + z * (27 + z * (3 + z * (18 + z * (36 + z * (19 + z * (18 + z * (2 + z * (17 + z * (17 + z * (8 + z * (24 + z * (11 + z * (26 + z * (20 + z * (20 + z * (18 + z * 19))))))))))))))))))

def pow7_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-18) + z * (0 + z * (6 + z * (50 + z * (34 + z * (21 + z * (9 + z * (12 + z * (6 + z * ((-1) + z * (19 + z * (6 + z * (5 + z * (40 + z * (21 + z * (20 + z * ((-56) + z * ((-20) + z * ((-2) + z * (7 + z * (11 + z * ((-9) + z * ((-7) + z * (22 + z * ((-35) + z * ((-26) + z * (0 + z * ((-12) + z * (4 + z * ((-30) + z * ((-9) + z * ((-6) + z * ((-20) + z * ((-18) + z * ((-16) + z * (1 + z * (9 + z * (2 + z * 25))))))))))))))))))))))))))))))))))))))

theorem pow7_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow7_40 z * u6 z = pow7_41_q z * f z + pow7_41 z + (41 : R) * pow7_41_mul_t z := by
  simp only [pow7_40, u6, pow7_41_q, f, pow7_41, pow7_41_mul_t]
  simp only [pow6_41]
  ring

theorem pow7_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow7_40 z * u6 z = pow7_41_q z * f z + pow7_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow7_41_mul_integer z


theorem pow7_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow7_40 z * u6 z = pow7_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow7_41_mul z


theorem pow7_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u6 z ^ 41 = pow7_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow7_40_pow z hz]
  exact pow7_41_root z hz


abbrev u7 {R : Type*} [CommRing R] (z : R) : R := pow7_41 z


def pow8_2 {R : Type*} [CommRing R] (z : R) : R := (13 + z * (32 + z * (30 + z * (4 + z * (27 + z * (25 + z * (10 + z * (33 + z * (5 + z * (30 + z * (5 + z * (39 + z * (14 + z * (10 + z * (40 + z * (30 + z * (40 + z * (38 + z * (2 + z * 20)))))))))))))))))))

def pow8_2_q {R : Type*} [CommRing R] (z : R) : R := (15 + z * (33 + z * (20 + z * (40 + z * (0 + z * (36 + z * (11 + z * (23 + z * (14 + z * (40 + z * (37 + z * (3 + z * (31 + z * (13 + z * (22 + z * (23 + z * (20 + z * (30 + z * 9))))))))))))))))))

def pow8_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (3 + z * (1 + z * ((-13) + z * ((-49) + z * (8 + z * ((-44) + z * (11 + z * ((-20) + z * (9 + z * ((-50) + z * (16 + z * ((-9) + z * ((-68) + z * (3 + z * ((-11) + z * ((-14) + z * ((-27) + z * ((-35) + z * ((-78) + z * ((-24) + z * ((-54) + z * ((-69) + z * ((-28) + z * (8 + z * ((-75) + z * ((-43) + z * ((-16) + z * ((-63) + z * ((-55) + z * ((-41) + z * ((-26) + z * ((-38) + z * ((-33) + z * ((-36) + z * ((-28) + z * ((-22) + z * ((-22) + z * ((-6) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow8_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u7 z * u7 z = pow8_2_q z * f z + pow8_2 z + (41 : R) * pow8_2_mul_t z := by
  simp only [u7, pow8_2_q, f, pow8_2, pow8_2_mul_t]
  simp only [pow7_41]
  ring

theorem pow8_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u7 z * u7 z = pow8_2_q z * f z + pow8_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow8_2_mul_integer z


theorem pow8_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u7 z * u7 z = pow8_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_2_mul z


theorem pow8_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u7 z ^ 2 = pow8_2 z := by
  calc
    _ = u7 z ^ 1 * u7 z ^ 1 := by ring
    _ = u7 z * u7 z := by simp only [pow_one]
    _ = _ := pow8_2_root z hz


def pow8_4 {R : Type*} [CommRing R] (z : R) : R := (22 + z * (29 + z * (10 + z * (10 + z * (23 + z * (26 + z * (7 + z * (22 + z * (37 + z * (17 + z * (29 + z * (15 + z * (15 + z * (6 + z * (19 + z * (3 + z * (15 + z * (23 + z * (1 + z * 36)))))))))))))))))))

def pow8_4_q {R : Type*} [CommRing R] (z : R) : R := (28 + z * (27 + z * (27 + z * (40 + z * (18 + z * (32 + z * (2 + z * (11 + z * (38 + z * (1 + z * (22 + z * (15 + z * (10 + z * (30 + z * (31 + z * (30 + z * (11 + z * (11 + z * 31))))))))))))))))))

def pow8_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-21) + z * ((-13) + z * ((-9) + z * ((-15) + z * ((-26) + z * ((-25) + z * (34 + z * ((-14) + z * ((-3) + z * (18 + z * ((-25) + z * (29 + z * ((-14) + z * (30 + z * ((-8) + z * ((-15) + z * (74 + z * (8 + z * (69 + z * ((-4) + z * (37 + z * (76 + z * (0 + z * (72 + z * (35 + z * (34 + z * (63 + z * (17 + z * (82 + z * ((-14) + z * (55 + z * (64 + z * (19 + z * (38 + z * (10 + z * (12 + z * (16 + z * ((-21) + z * 9))))))))))))))))))))))))))))))))))))))

theorem pow8_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_2 z * pow8_2 z = pow8_4_q z * f z + pow8_4 z + (41 : R) * pow8_4_mul_t z := by
  simp only [pow8_2, pow8_4_q, f, pow8_4, pow8_4_mul_t]
  
  ring

theorem pow8_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow8_2 z * pow8_2 z = pow8_4_q z * f z + pow8_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow8_4_mul_integer z


theorem pow8_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow8_2 z * pow8_2 z = pow8_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_4_mul z


theorem pow8_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u7 z ^ 4 = pow8_4 z := by
  calc
    _ = u7 z ^ 2 * u7 z ^ 2 := by ring
    _ = pow8_2 z * pow8_2 z := by rw [pow8_2_pow z hz]
    _ = _ := pow8_4_root z hz


def pow8_5 {R : Type*} [CommRing R] (z : R) : R := (19 + z * (8 + z * (15 + z * (37 + z * (15 + z * (31 + z * (10 + z * (32 + z * (19 + z * (36 + z * (32 + z * (33 + z * (34 + z * (36 + z * (27 + z * (15 + z * (12 + z * (37 + z * (17 + z * 3)))))))))))))))))))

def pow8_5_q {R : Type*} [CommRing R] (z : R) : R := (37 + z * (37 + z * (23 + z * (0 + z * (25 + z * (8 + z * (35 + z * (35 + z * (40 + z * (35 + z * (26 + z * (24 + z * (7 + z * (12 + z * (37 + z * (27 + z * (31 + z * (39 + z * 26))))))))))))))))))

def pow8_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-19) + z * ((-11) + z * ((-30) + z * ((-15) + z * ((-25) + z * (8 + z * ((-22) + z * ((-16) + z * ((-50) + z * ((-29) + z * ((-18) + z * ((-30) + z * ((-37) + z * ((-28) + z * ((-7) + z * ((-77) + z * ((-92) + z * ((-75) + z * ((-86) + z * ((-97) + z * ((-44) + z * ((-74) + z * ((-98) + z * ((-49) + z * ((-97) + z * ((-101) + z * ((-80) + z * ((-57) + z * ((-84) + z * ((-54) + z * ((-64) + z * ((-83) + z * ((-49) + z * ((-81) + z * ((-40) + z * ((-23) + z * ((-25) + z * ((-12) + z * 2))))))))))))))))))))))))))))))))))))))

theorem pow8_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_4 z * u7 z = pow8_5_q z * f z + pow8_5 z + (41 : R) * pow8_5_mul_t z := by
  simp only [pow8_4, u7, pow8_5_q, f, pow8_5, pow8_5_mul_t]
  simp only [pow7_41]
  ring

theorem pow8_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow8_4 z * u7 z = pow8_5_q z * f z + pow8_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow8_5_mul_integer z


theorem pow8_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow8_4 z * u7 z = pow8_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_5_mul z


theorem pow8_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u7 z ^ 5 = pow8_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow8_4_pow z hz]
  exact pow8_5_root z hz


def pow8_10 {R : Type*} [CommRing R] (z : R) : R := (6 + z * (15 + z * (33 + z * (17 + z * (18 + z * (6 + z * (27 + z * (36 + z * (15 + z * (36 + z * (15 + z * (4 + z * (24 + z * (39 + z * (22 + z * (7 + z * (27 + z * (19 + z * (16 + z * 6)))))))))))))))))))

def pow8_10_q {R : Type*} [CommRing R] (z : R) : R := (11 + z * (20 + z * (6 + z * (17 + z * (12 + z * (15 + z * (35 + z * (35 + z * (38 + z * (13 + z * (12 + z * (2 + z * (34 + z * (17 + z * (23 + z * (12 + z * (27 + z * (37 + z * 9))))))))))))))))))

def pow8_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-1) + z * ((-14) + z * ((-5) + z * (8 + z * (4 + z * (15 + z * (13 + z * (6 + z * ((-5) + z * (23 + z * (47 + z * (59 + z * (79 + z * (97 + z * (94 + z * (97 + z * (85 + z * (97 + z * (100 + z * (88 + z * (130 + z * (100 + z * (105 + z * (62 + z * (62 + z * (60 + z * (79 + z * (55 + z * (40 + z * (40 + z * (39 + z * ((-10) + z * ((-31) + z * ((-37) + z * ((-3) + z * ((-8) + z * ((-19) + z * ((-5) + z * 0))))))))))))))))))))))))))))))))))))))

theorem pow8_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_5 z * pow8_5 z = pow8_10_q z * f z + pow8_10 z + (41 : R) * pow8_10_mul_t z := by
  simp only [pow8_5, pow8_10_q, f, pow8_10, pow8_10_mul_t]
  
  ring

theorem pow8_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow8_5 z * pow8_5 z = pow8_10_q z * f z + pow8_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow8_10_mul_integer z


theorem pow8_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow8_5 z * pow8_5 z = pow8_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_10_mul z


def pow8_20 {R : Type*} [CommRing R] (z : R) : R := (21 + z * (29 + z * (1 + z * (12 + z * (12 + z * (3 + z * (38 + z * (20 + z * (21 + z * (20 + z * (31 + z * (22 + z * (27 + z * (13 + z * (16 + z * (23 + z * (6 + z * (13 + z * (36 + z * 1)))))))))))))))))))


def pow8_40 {R : Type*} [CommRing R] (z : R) : R := (10 + z * (16 + z * (24 + z * (21 + z * (19 + z * (1 + z * (34 + z * (28 + z * (40 + z * (21 + z * (18 + z * (3 + z * (40 + z * (21 + z * (10 + z * (2 + z * (5 + z * (12 + z * (10 + z * 38)))))))))))))))))))


def pow8_41 {R : Type*} [CommRing R] (z : R) : R := (21 + z * (7 + z * (26 + z * (28 + z * (4 + z * (30 + z * (16 + z * (39 + z * (9 + z * (24 + z * (8 + z * (22 + z * (31 + z * (17 + z * (27 + z * (40 + z * (17 + z * (32 + z * (35 + z * 1)))))))))))))))))))


abbrev u8 {R : Type*} [CommRing R] (z : R) : R := pow8_41 z

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Powers05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41


def pow10_41 {R : Type*} [CommRing R] (z : R) : R := (32 + z * (1 + z * (13 + z * (12 + z * (15 + z * (31 + z * (3 + z * (30 + z * (19 + z * (21 + z * (6 + z * (8 + z * (4 + z * (23 + z * (19 + z * (4 + z * (0 + z * (11 + z * (10 + z * 5)))))))))))))))))))


abbrev u10 {R : Type*} [CommRing R] (z : R) : R := pow10_41 z

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Result
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


lemma map_f {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (z : R) :
    φ (f z) = f (φ z) := by simp only [f, map_add, map_mul, map_ofNat, map_one]

section Field
variable (k : Type*) [Field k] [CharP k 41]

omit [CharP k 41] in
lemma root_f : f (AdjoinRoot.root (f (X : k[X]))) = 0 := by
  rw [← AdjoinRoot.mk_X, ← map_f]
  exact AdjoinRoot.mk_self

end Field

end DimensionTen.Mod41

end
end

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_PolynomialData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

def W1 : Fin 20 → ℤ :=
  ![-665456935831295645613234276870960, 0, 0, 82124647466024174155785096685260, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

end DimensionTen.Border

end
end

end OAI
end


