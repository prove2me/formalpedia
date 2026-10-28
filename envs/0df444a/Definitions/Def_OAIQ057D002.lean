-- Prove2me | Definitions.Def_OAIQ057D002
-- name    : OAIQ057D002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T20:43:55.961966+00:00
-- url     : https://prove2.me/theorems/cfe715ec-a0f1-4d9e-a36c-7e049c8736f8
-- title:
--   Definitions bundle OAIQ057D002 of the split of OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DimensionTen.exists_channel_fin21`, carved from OpenAI's openai/math development (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 280 declarations of OpenAI's Lean: 278 definitions and 2 theorems. The definitions and types are `OAI.DimensionTen.Border.W0`, `OAI.DimensionTen.Border.W10`, `OAI.DimensionTen.Border.W11`, `OAI.DimensionTen.Border.W12`, `OAI.DimensionTen.Border.W20`, `OAI.DimensionTen.Border.W3`, `OAI.DimensionTen.Border.pencilExplicit`, `OAI.DimensionTen.Border.rowChoices`, `OAI.DimensionTen.Mod131.pow1_16_q`, `OAI.DimensionTen.Mod131.pow1_2`, `OAI.DimensionTen.Mod131.pow1_2_q`, `OAI.DimensionTen.Mod41.pow10_10`, `OAI.DimensionTen.Mod41.pow10_10_mul_t`, `OAI.DimensionTen.Mod41.pow10_10_q`, `OAI.DimensionTen.Mod41.pow10_2`, `OAI.DimensionTen.Mod41.pow10_20`, `OAI.DimensionTen.Mod41.pow10_20_mul_t`, `OAI.DimensionTen.Mod41.pow10_20_q`, `OAI.DimensionTen.Mod41.pow10_2_mul_t`, `OAI.DimensionTen.Mod41.pow10_2_q`, `OAI.DimensionTen.Mod41.pow10_4`, `OAI.DimensionTen.Mod41.pow10_40`, `OAI.DimensionTen.Mod41.pow10_40_mul_t`, `OAI.DimensionTen.Mod41.pow10_40_q`, `OAI.DimensionTen.Mod41.pow10_41_mul_t`, `OAI.DimensionTen.Mod41.pow10_41_q`, `OAI.DimensionTen.Mod41.pow10_4_mul_t`, `OAI.DimensionTen.Mod41.pow10_4_q`, `OAI.DimensionTen.Mod41.pow10_5`, `OAI.DimensionTen.Mod41.pow10_5_mul_t`, `OAI.DimensionTen.Mod41.pow10_5_q`, `OAI.DimensionTen.Mod41.pow11_10`, `OAI.DimensionTen.Mod41.pow11_10_mul_t`, `OAI.DimensionTen.Mod41.pow11_10_q`, `OAI.DimensionTen.Mod41.pow11_2`, `OAI.DimensionTen.Mod41.pow11_20`, `OAI.DimensionTen.Mod41.pow11_20_mul_t`, `OAI.DimensionTen.Mod41.pow11_20_q`, `OAI.DimensionTen.Mod41.pow11_2_mul_t`, `OAI.DimensionTen.Mod41.pow11_2_q` and 238 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, lean/OAI/InformationTheory, in whole or in part: [`Quantum_DimensionTen_MinorData`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/MinorData.lean), [`Quantum_DimensionTen_Mod131Powers01`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod131Powers01.lean), [`Quantum_DimensionTen_Mod41Powers04`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod41Powers04.lean), [`Quantum_DimensionTen_Mod41Powers05`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod41Powers05.lean), [`Quantum_DimensionTen_Mod41Powers06`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod41Powers06.lean), [`Quantum_DimensionTen_Mod41Powers07`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod41Powers07.lean), [`Quantum_DimensionTen_Mod41Powers08`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod41Powers08.lean), [`Quantum_DimensionTen_Mod41Powers09`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod41Powers09.lean), [`Quantum_DimensionTen_Mod41Powers10`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod41Powers10.lean), [`Quantum_DimensionTen_Mod41Result`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Mod41Result.lean), [`Quantum_DimensionTen_PolynomialData`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/PolynomialData.lean), [`Quantum_PPTSquare_AlgebraData`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/PPTSquare/AlgebraData.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ057D008` and `OAIQ057D009`.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis, lean/OAI/InformationTheory at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ057_CH.Quantum_PPTSquare_AlgebraData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Matrix
namespace PencilAlgebra
def rows : Fin 15 → Fin 4 → Fin 6 :=
  ![![0,1,2,3],![0,1,2,4],![0,1,2,5],![0,1,3,4],![0,1,3,5],![0,1,4,5],![0,2,3,4],![0,2,3,5],![0,2,4,5],![0,3,4,5],![1,2,3,4],![1,2,3,5],![1,2,4,5],![1,3,4,5],![2,3,4,5]]
end PencilAlgebra

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_MinorData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

def rowChoices : Fin 15 → Fin 4 → Fin 6 := PencilAlgebra.rows

def pencilExplicit {R : Type*} [CommRing R] (x : Fin 4 → R) : Matrix (Fin 6) (Fin 4) R :=
  ![![(6 : R) * x 0 + (-12 : R) * x 1, (6 : R) * x 2, (-2 : R) * x 2 + (-4 : R) * x 3, (-3 : R) * x 3], ![(6 : R) * x 2, (6 : R) * x 0 + (-6 : R) * x 1 + (6 : R) * x 2 + (-2 : R) * x 3, (-3 : R) * x 3, (2 : R) * x 2 + (-4 : R) * x 3], ![(-2 : R) * x 2 + (-4 : R) * x 3, (-3 : R) * x 3, (6 : R) * x 0 + (6 : R) * x 1 + (10 : R) * x 2 + (11 : R) * x 3, (6 : R) * x 3], ![(-3 : R) * x 3, (2 : R) * x 2 + (-4 : R) * x 3, (6 : R) * x 3, (6 : R) * x 0 + (12 : R) * x 1 + (24 : R) * x 2 + (25 : R) * x 3], ![(-6 : R) * x 1 + (6 : R) * x 3, (6 : R) * x 3, (6 : R) * x 1, (6 : R) * x 1 + (6 : R) * x 2], ![(-6 : R) * x 1, (-6 : R) * x 1 + (-6 : R) * x 2 + (-6 : R) * x 3, (6 : R) * x 1 + (6 : R) * x 2 + (6 : R) * x 3, (-6 : R) * x 2 + (6 : R) * x 3]]

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Powers01
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

abbrev pow1_16_q {R : Type*} [CommRing R] (z : R) : R := pow1_2_q z

end DimensionTen.Mod131

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

def pow8_20_q {R : Type*} [CommRing R] (z : R) : R := (38 + z * (3 + z * (38 + z * (11 + z * (25 + z * (30 + z * (38 + z * (9 + z * (21 + z * (37 + z * (31 + z * (23 + z * (16 + z * (21 + z * (4 + z * (29 + z * (26 + z * (14 + z * 36))))))))))))))))))

def pow8_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-33) + z * ((-11) + z * ((-47) + z * (4 + z * ((-39) + z * ((-8) + z * ((-45) + z * ((-32) + z * ((-6) + z * ((-9) + z * ((-22) + z * ((-14) + z * ((-27) + z * ((-34) + z * (12 + z * (10 + z * ((-6) + z * ((-66) + z * ((-32) + z * ((-15) + z * ((-25) + z * ((-22) + z * ((-14) + z * ((-15) + z * ((-45) + z * ((-29) + z * ((-10) + z * ((-37) + z * ((-42) + z * ((-28) + z * ((-9) + z * ((-17) + z * ((-36) + z * ((-36) + z * ((-37) + z * ((-23) + z * ((-14) + z * ((-22) + z * 0))))))))))))))))))))))))))))))))))))))

def pow8_40_q {R : Type*} [CommRing R] (z : R) : R := (4 + z * (16 + z * (25 + z * (29 + z * (26 + z * (20 + z * (18 + z * (29 + z * (26 + z * (6 + z * (2 + z * (31 + z * (28 + z * (8 + z * (7 + z * (9 + z * (4 + z * (1 + z * 1))))))))))))))))))

def pow8_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (7 + z * (14 + z * ((-9) + z * ((-32) + z * ((-25) + z * ((-40) + z * ((-17) + z * (5 + z * ((-29) + z * ((-9) + z * (13 + z * ((-12) + z * (2 + z * (8 + z * (3 + z * (2 + z * (23 + z * (14 + z * (41 + z * (10 + z * ((-8) + z * (28 + z * ((-10) + z * ((-9) + z * (69 + z * (41 + z * (15 + z * (17 + z * (37 + z * (29 + z * (19 + z * (1 + z * (25 + z * (32 + z * (6 + z * (19 + z * (31 + z * (1 + z * 0))))))))))))))))))))))))))))))))))))))

def pow8_41_q {R : Type*} [CommRing R] (z : R) : R := (26 + z * (20 + z * (36 + z * (5 + z * (7 + z * (27 + z * (5 + z * (36 + z * (12 + z * (34 + z * (12 + z * (12 + z * (22 + z * (24 + z * (25 + z * (38 + z * (39 + z * (27 + z * 32))))))))))))))))))

def pow8_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-17) + z * ((-9) + z * ((-30) + z * (2 + z * ((-15) + z * ((-17) + z * (5 + z * ((-6) + z * (32 + z * ((-37) + z * (39 + z * ((-19) + z * (26 + z * (18 + z * (0 + z * ((-36) + z * ((-45) + z * ((-52) + z * ((-51) + z * ((-19) + z * ((-51) + z * ((-34) + z * ((-23) + z * ((-19) + z * ((-82) + z * ((-32) + z * ((-71) + z * ((-51) + z * ((-57) + z * ((-51) + z * ((-81) + z * ((-100) + z * ((-71) + z * ((-83) + z * ((-48) + z * ((-26) + z * ((-17) + z * ((-15) + z * 2))))))))))))))))))))))))))))))))))))))

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

def pow10_41_q {R : Type*} [CommRing R] (z : R) : R := (12 + z * (22 + z * (30 + z * (36 + z * (8 + z * (20 + z * (7 + z * (18 + z * (8 + z * (9 + z * (16 + z * (7 + z * (40 + z * (19 + z * (15 + z * (17 + z * (18 + z * (22 + z * 16))))))))))))))))))

def pow10_41_mul_t {R : Type*} [CommRing R] (z : R) : R := (8 + z * (1 + z * ((-1) + z * (0 + z * (7 + z * ((-19) + z * (35 + z * (18 + z * (7 + z * (3 + z * (0 + z * (21 + z * ((-33) + z * (17 + z * ((-8) + z * (39 + z * (7 + z * (24 + z * (4 + z * ((-12) + z * ((-23) + z * ((-10) + z * (4 + z * ((-14) + z * ((-10) + z * (5 + z * ((-11) + z * ((-13) + z * ((-23) + z * ((-5) + z * ((-2) + z * ((-19) + z * ((-8) + z * ((-10) + z * ((-10) + z * ((-10) + z * ((-14) + z * ((-2) + z * 0))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Powers06
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
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Powers07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41
def pow13_2 {R : Type*} [CommRing R] (z : R) : R := (19 + z * (7 + z * (4 + z * (21 + z * (9 + z * (21 + z * (15 + z * (6 + z * (8 + z * (13 + z * (37 + z * (8 + z * (9 + z * (3 + z * (24 + z * (11 + z * (26 + z * (8 + z * (35 + z * 18)))))))))))))))))))

def pow13_2_q {R : Type*} [CommRing R] (z : R) : R := (7 + z * (8 + z * (29 + z * (37 + z * (15 + z * (40 + z * (36 + z * (32 + z * (29 + z * (0 + z * (20 + z * (39 + z * (19 + z * (22 + z * (3 + z * (0 + z * (39 + z * (32 + z * 10))))))))))))))))))

def pow13_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-6) + z * ((-6) + z * ((-26) + z * ((-37) + z * ((-28) + z * ((-32) + z * ((-29) + z * ((-49) + z * ((-6) + z * ((-6) + z * ((-33) + z * ((-26) + z * ((-28) + z * ((-25) + z * (19 + z * ((-14) + z * ((-8) + z * ((-70) + z * ((-40) + z * ((-22) + z * ((-3) + z * ((-27) + z * ((-9) + z * ((-30) + z * (0 + z * ((-45) + z * (27 + z * ((-41) + z * (25 + z * ((-1) + z * (5 + z * ((-18) + z * ((-13) + z * ((-11) + z * (24 + z * ((-24) + z * (16 + z * ((-2) + z * 15))))))))))))))))))))))))))))))))))))))


def pow13_4 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (17 + z * (26 + z * (40 + z * (18 + z * (13 + z * (17 + z * (16 + z * (37 + z * (8 + z * (13 + z * (34 + z * (18 + z * (16 + z * (6 + z * (18 + z * (11 + z * (20 + z * (21 + z * 29)))))))))))))))))))

def pow13_4_q {R : Type*} [CommRing R] (z : R) : R := (18 + z * (38 + z * (16 + z * (12 + z * (33 + z * (26 + z * (17 + z * (11 + z * (21 + z * (38 + z * (14 + z * (19 + z * (0 + z * (35 + z * (12 + z * (16 + z * (33 + z * (27 + z * 37))))))))))))))))))

def pow13_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-7) + z * ((-33) + z * ((-35) + z * ((-24) + z * ((-44) + z * ((-48) + z * ((-32) + z * ((-38) + z * ((-67) + z * ((-69) + z * ((-28) + z * ((-77) + z * ((-70) + z * ((-82) + z * ((-37) + z * ((-87) + z * ((-107) + z * ((-128) + z * ((-118) + z * ((-72) + z * ((-129) + z * ((-60) + z * ((-67) + z * ((-74) + z * ((-59) + z * ((-89) + z * ((-40) + z * ((-66) + z * ((-26) + z * ((-44) + z * ((-38) + z * ((-50) + z * ((-48) + z * ((-39) + z * ((-15) + z * ((-20) + z * (1 + z * (3 + z * 7))))))))))))))))))))))))))))))))))))))


def pow13_5 {R : Type*} [CommRing R] (z : R) : R := (33 + z * (11 + z * (39 + z * (36 + z * (26 + z * (0 + z * (12 + z * (37 + z * (11 + z * (26 + z * (30 + z * (17 + z * (28 + z * (19 + z * (4 + z * (1 + z * (15 + z * (3 + z * (40 + z * 38)))))))))))))))))))

def pow13_5_q {R : Type*} [CommRing R] (z : R) : R := (23 + z * (4 + z * (17 + z * (7 + z * (22 + z * (31 + z * (38 + z * (21 + z * (25 + z * (23 + z * (32 + z * (3 + z * (6 + z * (17 + z * (26 + z * (35 + z * (0 + z * (35 + z * 28))))))))))))))))))

def pow13_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-21) + z * ((-9) + z * ((-25) + z * (2 + z * ((-23) + z * ((-1) + z * ((-7) + z * ((-1) + z * ((-8) + z * ((-22) + z * ((-24) + z * (7 + z * (33 + z * (21 + z * ((-17) + z * ((-11) + z * ((-7) + z * ((-44) + z * ((-8) + z * ((-31) + z * (22 + z * ((-28) + z * ((-3) + z * (6 + z * ((-42) + z * ((-58) + z * ((-17) + z * (10 + z * (5 + z * ((-35) + z * (6 + z * ((-26) + z * ((-30) + z * ((-40) + z * ((-14) + z * (5 + z * (3 + z * ((-5) + z * 17))))))))))))))))))))))))))))))))))))))


def pow13_10 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (15 + z * (18 + z * (2 + z * (12 + z * (21 + z * (5 + z * (27 + z * (23 + z * (32 + z * (37 + z * (16 + z * (15 + z * (20 + z * (23 + z * (29 + z * (18 + z * (4 + z * (12 + z * 40)))))))))))))))))))

def pow13_10_q {R : Type*} [CommRing R] (z : R) : R := (21 + z * (19 + z * (9 + z * (20 + z * (23 + z * (5 + z * (4 + z * (21 + z * (29 + z * (21 + z * (4 + z * (17 + z * (29 + z * (28 + z * (22 + z * (14 + z * (1 + z * (23 + z * 9))))))))))))))))))

def pow13_10_mul_t {R : Type*} [CommRing R] (z : R) : R := (8 + z * ((-6) + z * (36 + z * (44 + z * (48 + z * (38 + z * (68 + z * (53 + z * ((-5) + z * (66 + z * (93 + z * (56 + z * (69 + z * (82 + z * (58 + z * ((-2) + z * (29 + z * ((-18) + z * (35 + z * (52 + z * (79 + z * (97 + z * (68 + z * (3 + z * ((-48) + z * (32 + z * (22 + z * ((-16) + z * (19 + z * (15 + z * (14 + z * (17 + z * ((-16) + z * ((-38) + z * (0 + z * (18 + z * (24 + z * (67 + z * 35))))))))))))))))))))))))))))))))))))))


def pow13_20 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (10 + z * (38 + z * (33 + z * (33 + z * (15 + z * (28 + z * (16 + z * (30 + z * (23 + z * (31 + z * (17 + z * (13 + z * (3 + z * (4 + z * (22 + z * (26 + z * (0 + z * (37 + z * 28)))))))))))))))))))

def pow13_20_q {R : Type*} [CommRing R] (z : R) : R := (36 + z * (0 + z * (36 + z * (20 + z * (27 + z * (26 + z * (24 + z * (23 + z * (7 + z * (31 + z * (14 + z * (11 + z * (40 + z * (27 + z * (14 + z * (35 + z * (17 + z * (28 + z * 1))))))))))))))))))

def pow13_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-31) + z * ((-8) + z * ((-49) + z * ((-17) + z * ((-73) + z * ((-36) + z * ((-52) + z * ((-67) + z * ((-39) + z * ((-49) + z * ((-29) + z * ((-45) + z * ((-31) + z * ((-68) + z * ((-49) + z * ((-37) + z * ((-60) + z * ((-57) + z * ((-24) + z * ((-59) + z * (3 + z * ((-23) + z * ((-17) + z * (7 + z * (12 + z * (9 + z * (21 + z * (4 + z * (9 + z * (28 + z * ((-13) + z * ((-38) + z * ((-19) + z * (7 + z * (18 + z * (12 + z * ((-10) + z * (22 + z * 39))))))))))))))))))))))))))))))))))))))


def pow13_40 {R : Type*} [CommRing R] (z : R) : R := (6 + z * (9 + z * (25 + z * (3 + z * (6 + z * (37 + z * (40 + z * (17 + z * (3 + z * (31 + z * (13 + z * (6 + z * (20 + z * (4 + z * (11 + z * (29 + z * (32 + z * (4 + z * (36 + z * 27)))))))))))))))))))

def pow13_40_q {R : Type*} [CommRing R] (z : R) : R := (34 + z * (0 + z * (25 + z * (27 + z * (10 + z * (19 + z * (35 + z * (21 + z * (22 + z * (36 + z * (20 + z * (15 + z * (5 + z * (21 + z * (33 + z * (21 + z * (40 + z * (36 + z * 5))))))))))))))))))

def pow13_40_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-30) + z * ((-11) + z * ((-45) + z * ((-14) + z * ((-11) + z * (32 + z * (29 + z * ((-1) + z * (30 + z * (12 + z * (21 + z * (31 + z * (88 + z * (31 + z * (14 + z * ((-22) + z * ((-58) + z * ((-62) + z * ((-28) + z * ((-19) + z * (29 + z * (6 + z * (24 + z * ((-22) + z * ((-42) + z * ((-41) + z * (1 + z * ((-11) + z * ((-25) + z * ((-25) + z * ((-39) + z * ((-55) + z * ((-80) + z * ((-44) + z * (20 + z * ((-12) + z * (4 + z * (46 + z * 19))))))))))))))))))))))))))))))))))))))


def pow13_41 {R : Type*} [CommRing R] (z : R) : R := (30 + z * (23 + z * (8 + z * (32 + z * (34 + z * (36 + z * (32 + z * (30 + z * (33 + z * (23 + z * (36 + z * (1 + z * (27 + z * (2 + z * (6 + z * (12 + z * (14 + z * (15 + z * (1 + z * 4)))))))))))))))))))

def pow13_41_q {R : Type*} [CommRing R] (z : R) : R := (0 + z * (28 + z * (4 + z * (23 + z * (3 + z * (40 + z * (33 + z * (25 + z * (4 + z * (33 + z * (28 + z * (22 + z * (5 + z * (26 + z * (11 + z * (25 + z * (17 + z * (14 + z * 19))))))))))))))))))

def pow13_41_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * ((-22) + z * ((-5) + z * ((-29) + z * (3 + z * ((-44) + z * (0 + z * ((-26) + z * ((-17) + z * ((-13) + z * (7 + z * (1 + z * ((-15) + z * ((-34) + z * ((-6) + z * ((-15) + z * ((-4) + z * ((-53) + z * ((-33) + z * (26 + z * ((-20) + z * ((-2) + z * ((-14) + z * (33 + z * ((-19) + z * ((-24) + z * ((-12) + z * (1 + z * ((-4) + z * ((-2) + z * ((-8) + z * (5 + z * ((-10) + z * (17 + z * (4 + z * (30 + z * (12 + z * (11 + z * 16))))))))))))))))))))))))))))))))))))))


abbrev u13 {R : Type*} [CommRing R] (z : R) : R := pow13_41 z


def pow14_2 {R : Type*} [CommRing R] (z : R) : R := (14 + z * (39 + z * (30 + z * (23 + z * (27 + z * (17 + z * (29 + z * (28 + z * (14 + z * (4 + z * (15 + z * (25 + z * (32 + z * (18 + z * (38 + z * (8 + z * (26 + z * (40 + z * (40 + z * 21)))))))))))))))))))

def pow14_2_q {R : Type*} [CommRing R] (z : R) : R := (36 + z * (14 + z * (32 + z * (33 + z * (39 + z * (14 + z * (13 + z * (25 + z * (3 + z * (11 + z * (22 + z * (35 + z * (14 + z * (23 + z * (24 + z * (29 + z * (28 + z * (20 + z * 16))))))))))))))))))

def pow14_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-10) + z * (9 + z * ((-35) + z * (5 + z * ((-10) + z * (38 + z * (52 + z * (50 + z * (94 + z * (104 + z * (125 + z * (52 + z * (103 + z * (97 + z * (33 + z * (26 + z * (22 + z * ((-10) + z * ((-64) + z * ((-68) + z * ((-28) + z * ((-70) + z * ((-48) + z * ((-69) + z * ((-36) + z * ((-69) + z * ((-83) + z * ((-70) + z * ((-91) + z * ((-88) + z * ((-105) + z * ((-79) + z * ((-79) + z * ((-64) + z * ((-49) + z * ((-35) + z * ((-19) + z * ((-12) + z * 0))))))))))))))))))))))))))))))))))))))


def pow14_4 {R : Type*} [CommRing R] (z : R) : R := (16 + z * (26 + z * (7 + z * (39 + z * (17 + z * (16 + z * (3 + z * (19 + z * (21 + z * (12 + z * (10 + z * (25 + z * (25 + z * (28 + z * (35 + z * (25 + z * (30 + z * (34 + z * (11 + z * 22)))))))))))))))))))

def pow14_4_q {R : Type*} [CommRing R] (z : R) : R := (5 + z * (13 + z * (3 + z * (39 + z * (25 + z * (25 + z * (6 + z * (16 + z * (14 + z * (24 + z * (0 + z * (6 + z * (37 + z * (1 + z * (33 + z * (14 + z * (15 + z * (12 + z * 31))))))))))))))))))

def pow14_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * (13 + z * (47 + z * (27 + z * (43 + z * (27 + z * (68 + z * (59 + z * (82 + z * (54 + z * (50 + z * (42 + z * (54 + z * (99 + z * (69 + z * (105 + z * (47 + z * (129 + z * (140 + z * (137 + z * (133 + z * (120 + z * (69 + z * (83 + z * (112 + z * (83 + z * (55 + z * (36 + z * (65 + z * (72 + z * (92 + z * (69 + z * (60 + z * (30 + z * (49 + z * (71 + z * (58 + z * (18 + z * 10))))))))))))))))))))))))))))))))))))))


def pow14_5 {R : Type*} [CommRing R] (z : R) : R := (4 + z * (0 + z * (23 + z * (16 + z * (0 + z * (26 + z * (39 + z * (16 + z * (8 + z * (5 + z * (28 + z * (36 + z * (37 + z * (12 + z * (24 + z * (28 + z * (17 + z * (15 + z * (35 + z * 23)))))))))))))))))))

def pow14_5_q {R : Type*} [CommRing R] (z : R) : R := (36 + z * (28 + z * (16 + z * (23 + z * (29 + z * (3 + z * (28 + z * (35 + z * (8 + z * (19 + z * (39 + z * (8 + z * (33 + z * (40 + z * (17 + z * (15 + z * (23 + z * (9 + z * 6))))))))))))))))))

def pow14_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * ((-8) + z * ((-27) + z * (3 + z * ((-4) + z * (14 + z * (21 + z * (10 + z * (20 + z * (32 + z * (8 + z * (3 + z * (10 + z * (30 + z * ((-38) + z * (9 + z * ((-3) + z * (2 + z * (10 + z * (31 + z * (25 + z * (18 + z * (30 + z * (10 + z * (8 + z * ((-16) + z * ((-20) + z * ((-28) + z * ((-50) + z * ((-41) + z * ((-41) + z * ((-36) + z * ((-40) + z * ((-12) + z * ((-5) + z * ((-9) + z * (2 + z * ((-3) + z * 2))))))))))))))))))))))))))))))))))))))


def pow14_10 {R : Type*} [CommRing R] (z : R) : R := (17 + z * (5 + z * (18 + z * (10 + z * (17 + z * (23 + z * (23 + z * (8 + z * (26 + z * (0 + z * (16 + z * (40 + z * (11 + z * (8 + z * (33 + z * (9 + z * (24 + z * (4 + z * (12 + z * 21)))))))))))))))))))

def pow14_10_q {R : Type*} [CommRing R] (z : R) : R := (33 + z * (13 + z * (10 + z * (5 + z * (4 + z * (40 + z * (38 + z * (19 + z * (3 + z * (4 + z * (0 + z * (1 + z * (13 + z * (12 + z * (26 + z * (10 + z * (21 + z * (8 + z * 37))))))))))))))))))

def pow14_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-29) + z * ((-22) + z * ((-33) + z * ((-15) + z * ((-26) + z * ((-32) + z * ((-46) + z * ((-58) + z * ((-3) + z * ((-25) + z * ((-20) + z * (5 + z * (22 + z * (15 + z * ((-11) + z * ((-8) + z * ((-8) + z * (66 + z * (27 + z * (13 + z * (36 + z * (78 + z * (48 + z * (75 + z * (103 + z * (72 + z * (81 + z * (72 + z * (72 + z * (82 + z * (82 + z * (36 + z * (10 + z * (13 + z * (15 + z * (5 + z * (25 + z * (12 + z * 12))))))))))))))))))))))))))))))))))))))


def pow14_20 {R : Type*} [CommRing R] (z : R) : R := (1 + z * (18 + z * (37 + z * (11 + z * (34 + z * (27 + z * (17 + z * (33 + z * (27 + z * (15 + z * (4 + z * (10 + z * (18 + z * (18 + z * (23 + z * (18 + z * (10 + z * (0 + z * (4 + z * 37)))))))))))))))))))

def pow14_20_q {R : Type*} [CommRing R] (z : R) : R := (8 + z * (15 + z * (8 + z * (27 + z * (28 + z * (26 + z * (33 + z * (9 + z * (38 + z * (28 + z * (10 + z * (14 + z * (32 + z * (21 + z * (31 + z * (11 + z * (19 + z * (25 + z * 31))))))))))))))))))

def pow14_20_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * ((-12) + z * ((-3) + z * ((-25) + z * ((-22) + z * ((-33) + z * ((-25) + z * ((-27) + z * ((-41) + z * ((-41) + z * ((-36) + z * ((-16) + z * ((-55) + z * ((-45) + z * ((-39) + z * ((-61) + z * ((-41) + z * ((-68) + z * ((-75) + z * ((-60) + z * ((-103) + z * ((-65) + z * ((-47) + z * ((-96) + z * ((-60) + z * ((-63) + z * ((-51) + z * ((-44) + z * ((-75) + z * ((-52) + z * ((-7) + z * ((-63) + z * ((-48) + z * ((-42) + z * ((-32) + z * ((-15) + z * ((-24) + z * ((-11) + z * 10))))))))))))))))))))))))))))))))))))))


def pow14_40 {R : Type*} [CommRing R] (z : R) : R := (21 + z * (8 + z * (29 + z * (20 + z * (28 + z * (9 + z * (1 + z * (15 + z * (20 + z * (19 + z * (6 + z * (39 + z * (40 + z * (16 + z * (37 + z * (28 + z * (24 + z * (3 + z * 19))))))))))))))))))

def pow14_40_q {R : Type*} [CommRing R] (z : R) : R := (4 + z * (13 + z * (25 + z * (0 + z * (14 + z * (40 + z * (27 + z * (5 + z * (9 + z * (18 + z * (10 + z * (39 + z * (29 + z * (8 + z * (16 + z * (27 + z * (16 + z * (21 + z * 16))))))))))))))))))

def pow14_40_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-4) + z * ((-12) + z * ((-20) + z * (15 + z * (10 + z * (0 + z * (21 + z * (34 + z * (49 + z * (54 + z * (61 + z * (37 + z * (6 + z * ((-5) + z * (34 + z * (15 + z * ((-2) + z * ((-5) + z * ((-18) + z * ((-37) + z * ((-4) + z * (14 + z * ((-41) + z * ((-2) + z * ((-34) + z * ((-57) + z * ((-21) + z * ((-25) + z * ((-46) + z * ((-61) + z * ((-60) + z * ((-41) + z * ((-30) + z * ((-18) + z * ((-17) + z * ((-12) + z * ((-22) + z * ((-5) + z * 33))))))))))))))))))))))))))))))))))))))


def pow14_41 {R : Type*} [CommRing R] (z : R) : R := (20 + z * (40 + z * (16 + z * (8 + z * (24 + z * (12 + z * (40 + z * (1 + z * (21 + z * (19 + z * (12 + z * (2 + z * (34 + z * (16 + z * (3 + z * (3 + z * (24 + z * (14 + z * (19 + z * 7)))))))))))))))))))

def pow14_41_q {R : Type*} [CommRing R] (z : R) : R := (1 + z * (30 + z * (15 + z * (17 + z * (20 + z * (17 + z * (4 + z * (25 + z * (33 + z * (4 + z * (35 + z * (4 + z * (14 + z * (37 + z * (36 + z * (19 + z * (6 + z * 35)))))))))))))))))

def pow14_41_mul_t {R : Type*} [CommRing R] (z : R) : R := (14 + z * ((-10) + z * (6 + z * (7 + z * (25 + z * (16 + z * (34 + z * (46 + z * (33 + z * (40 + z * (30 + z * (53 + z * (52 + z * (46 + z * (36 + z * (34 + z * (60 + z * (15 + z * (42 + z * (51 + z * (37 + z * (13 + z * (7 + z * (6 + z * ((-30) + z * ((-47) + z * ((-27) + z * ((-48) + z * ((-44) + z * ((-81) + z * ((-38) + z * ((-52) + z * ((-64) + z * ((-47) + z * ((-26) + z * ((-10) + z * ((-25) + z * 1)))))))))))))))))))))))))))))))))))))


abbrev u14 {R : Type*} [CommRing R] (z : R) : R := pow14_41 z

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Powers08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41
def pow15_2 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (29 + z * (4 + z * (21 + z * (5 + z * (39 + z * (39 + z * (10 + z * (33 + z * (7 + z * (19 + z * (29 + z * (19 + z * (35 + z * (16 + z * (10 + z * (21 + z * (35 + z * (16 + z * 35)))))))))))))))))))

def pow15_2_q {R : Type*} [CommRing R] (z : R) : R := (2 + z * (19 + z * (16 + z * (37 + z * (19 + z * (6 + z * (31 + z * (17 + z * (38 + z * (25 + z * (37 + z * (8 + z * (25 + z * (7 + z * (13 + z * (24 + z * (10 + z * (26 + z * 8))))))))))))))))))

def pow15_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (8 + z * (21 + z * (33 + z * ((-13) + z * (3 + z * (10 + z * (23 + z * (35 + z * ((-26) + z * (12 + z * ((-22) + z * ((-29) + z * ((-12) + z * (13 + z * ((-13) + z * ((-53) + z * ((-34) + z * ((-67) + z * ((-7) + z * ((-79) + z * ((-56) + z * ((-71) + z * ((-53) + z * ((-86) + z * ((-54) + z * ((-76) + z * ((-75) + z * ((-79) + z * ((-42) + z * ((-45) + z * ((-19) + z * ((-42) + z * ((-36) + z * ((-33) + z * ((-15) + z * ((-2) + z * ((-9) + z * (0 + z * 1))))))))))))))))))))))))))))))))))))))


def pow15_4 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (12 + z * (38 + z * (13 + z * (4 + z * (38 + z * (0 + z * (25 + z * (8 + z * (10 + z * (22 + z * (16 + z * (16 + z * (11 + z * (40 + z * (29 + z * (17 + z * (38 + z * (30 + z * 36)))))))))))))))))))

def pow15_4_q {R : Type*} [CommRing R] (z : R) : R := (3 + z * (2 + z * (2 + z * (15 + z * (5 + z * (27 + z * (21 + z * (30 + z * (35 + z * (34 + z * (16 + z * (33 + z * (35 + z * (29 + z * (38 + z * (10 + z * (33 + z * (40 + z * 36))))))))))))))))))

def pow15_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-3) + z * ((-3) + z * (15 + z * ((-10) + z * (17 + z * ((-28) + z * (34 + z * (0 + z * ((-3) + z * (9 + z * ((-13) + z * (37 + z * ((-1) + z * (3 + z * (21 + z * ((-22) + z * ((-4) + z * ((-4) + z * (2 + z * (19 + z * (5 + z * ((-13) + z * (17 + z * ((-4) + z * (6 + z * ((-13) + z * ((-52) + z * ((-23) + z * ((-65) + z * ((-24) + z * (9 + z * ((-30) + z * ((-27) + z * ((-44) + z * ((-10) + z * (2 + z * (21 + z * (0 + z * 29))))))))))))))))))))))))))))))))))))))


def pow15_5 {R : Type*} [CommRing R] (z : R) : R := (16 + z * (0 + z * (32 + z * (13 + z * (32 + z * (15 + z * (33 + z * (9 + z * (26 + z * (20 + z * (5 + z * (29 + z * (3 + z * (4 + z * (9 + z * (26 + z * (13 + z * (29 + z * (20 + z * 2)))))))))))))))))))

def pow15_5_q {R : Type*} [CommRing R] (z : R) : R := (17 + z * (32 + z * (35 + z * (10 + z * (33 + z * (14 + z * (14 + z * (38 + z * (2 + z * (2 + z * (35 + z * (3 + z * (8 + z * (20 + z * (34 + z * (30 + z * (31 + z * (17 + z * 6))))))))))))))))))

def pow15_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-8) + z * ((-13) + z * ((-18) + z * (7 + z * ((-32) + z * ((-12) + z * (8 + z * ((-17) + z * (0 + z * ((-22) + z * ((-14) + z * (2 + z * ((-34) + z * (10 + z * ((-38) + z * ((-19) + z * ((-46) + z * ((-55) + z * ((-27) + z * (10 + z * (13 + z * ((-37) + z * ((-21) + z * (19 + z * ((-14) + z * ((-16) + z * ((-18) + z * (17 + z * ((-10) + z * ((-33) + z * ((-13) + z * ((-12) + z * ((-30) + z * ((-21) + z * ((-4) + z * (18 + z * (17 + z * (17 + z * 6))))))))))))))))))))))))))))))))))))))


def pow15_10 {R : Type*} [CommRing R] (z : R) : R := (7 + z * (19 + z * (12 + z * (4 + z * (13 + z * (12 + z * (1 + z * (30 + z * (33 + z * (27 + z * (26 + z * (22 + z * (22 + z * (6 + z * (40 + z * (14 + z * (28 + z * (4 + z * (8 + z * 31)))))))))))))))))))

def pow15_10_q {R : Type*} [CommRing R] (z : R) : R := (24 + z * (17 + z * (35 + z * (17 + z * (37 + z * (37 + z * (36 + z * (30 + z * (12 + z * (0 + z * (21 + z * (4 + z * (39 + z * (36 + z * (7 + z * (2 + z * (8 + z * (1 + z * 4))))))))))))))))))

def pow15_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * ((-23) + z * ((-29) + z * ((-29) + z * ((-33) + z * ((-42) + z * ((-21) + z * ((-53) + z * (1 + z * ((-30) + z * (1 + z * ((-3) + z * ((-55) + z * ((-33) + z * ((-75) + z * ((-35) + z * ((-86) + z * ((-32) + z * ((-62) + z * ((-32) + z * ((-59) + z * ((-57) + z * ((-32) + z * ((-38) + z * ((-35) + z * ((-17) + z * (9 + z * ((-37) + z * ((-27) + z * ((-33) + z * ((-20) + z * ((-24) + z * (9 + z * (29 + z * (27 + z * (21 + z * (10 + z * ((-1) + z * 0))))))))))))))))))))))))))))))))))))))


def pow15_20 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (20 + z * (12 + z * (12 + z * (5 + z * (13 + z * (2 + z * (27 + z * (23 + z * (35 + z * (11 + z * (21 + z * (12 + z * (40 + z * (24 + z * (16 + z * (3 + z * (34 + z * (5 + z * 15)))))))))))))))))))

def pow15_20_q {R : Type*} [CommRing R] (z : R) : R := (23 + z * (27 + z * (31 + z * (16 + z * (15 + z * (24 + z * (5 + z * (40 + z * (6 + z * (10 + z * (20 + z * (6 + z * (36 + z * (22 + z * (30 + z * (33 + z * (14 + z * (38 + z * 18))))))))))))))))))

def pow15_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-19) + z * ((-25) + z * ((-40) + z * ((-32) + z * ((-48) + z * ((-44) + z * ((-32) + z * ((-70) + z * ((-24) + z * ((-41) + z * ((-14) + z * ((-34) + z * ((-42) + z * ((-30) + z * ((-73) + z * ((-28) + z * ((-44) + z * ((-66) + z * ((-47) + z * ((-50) + z * ((-17) + z * ((-21) + z * ((-20) + z * (25 + z * (1 + z * ((-15) + z * (14 + z * (6 + z * ((-3) + z * ((-43) + z * ((-4) + z * ((-55) + z * ((-57) + z * ((-19) + z * ((-34) + z * (7 + z * ((-28) + z * ((-2) + z * 23))))))))))))))))))))))))))))))))))))))


def pow15_40 {R : Type*} [CommRing R] (z : R) : R := (34 + z * (21 + z * (30 + z * (35 + z * (11 + z * (4 + z * (10 + z * (32 + z * (18 + z * (11 + z * (26 + z * (19 + z * (39 + z * (1 + z * (10 + z * (21 + z * (38 + z * (38 + z * (23 + z * 19)))))))))))))))))))

def pow15_40_q {R : Type*} [CommRing R] (z : R) : R := (15 + z * (35 + z * (25 + z * (25 + z * (15 + z * (0 + z * (7 + z * (3 + z * (38 + z * (39 + z * (40 + z * (36 + z * (27 + z * (17 + z * (23 + z * (39 + z * (19 + z * (1 + z * 20))))))))))))))))))

def pow15_40_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-14) + z * ((-36) + z * ((-35) + z * ((-45) + z * ((-37) + z * ((-41) + z * ((-23) + z * ((-29) + z * ((-55) + z * ((-50) + z * ((-61) + z * ((-80) + z * ((-81) + z * ((-82) + z * ((-34) + z * ((-82) + z * ((-65) + z * ((-99) + z * ((-62) + z * ((-102) + z * ((-40) + z * ((-16) + z * ((-12) + z * ((-57) + z * ((-9) + z * ((-72) + z * ((-23) + z * ((-64) + z * ((-28) + z * ((-79) + z * ((-25) + z * ((-32) + z * ((-11) + z * ((-36) + z * ((-13) + z * ((-16) + z * (16 + z * ((-11) + z * 5))))))))))))))))))))))))))))))))))))))


def pow15_41 {R : Type*} [CommRing R] (z : R) : R := (14 + z * (4 + z * (4 + z * (17 + z * (24 + z * (11 + z * (4 + z * (5 + z * (16 + z * (11 + z * (17 + z * (15 + z * (8 + z * (33 + z * (15 + z * (16 + z * (22 + z * (23 + z * (29 + z * 28)))))))))))))))))))

def pow15_41_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (25 + z * (26 + z * (6 + z * (11 + z * (5 + z * (36 + z * (30 + z * (32 + z * (32 + z * (15 + z * (6 + z * (38 + z * (32 + z * (3 + z * (39 + z * (2 + z * (17 + z * 10))))))))))))))))))

def pow15_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-18) + z * (9 + z * ((-11) + z * (28 + z * (13 + z * (17 + z * (11 + z * ((-2) + z * ((-5) + z * ((-6) + z * ((-25) + z * ((-12) + z * (10 + z * ((-3) + z * ((-37) + z * ((-58) + z * ((-18) + z * ((-64) + z * (35 + z * ((-34) + z * (0 + z * ((-17) + z * ((-36) + z * ((-43) + z * ((-33) + z * ((-39) + z * ((-53) + z * ((-42) + z * ((-17) + z * ((-19) + z * ((-16) + z * ((-35) + z * ((-24) + z * (7 + z * (2 + z * (28 + z * (7 + z * (5 + z * 3))))))))))))))))))))))))))))))))))))))


abbrev u15 {R : Type*} [CommRing R] (z : R) : R := pow15_41 z


def pow16_2 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (28 + z * (17 + z * (10 + z * (19 + z * (8 + z * (28 + z * (34 + z * (36 + z * (30 + z * (3 + z * (38 + z * (37 + z * (16 + z * (39 + z * (11 + z * (11 + z * (23 + z * (38 + z * 8)))))))))))))))))))

def pow16_2_q {R : Type*} [CommRing R] (z : R) : R := (11 + z * (20 + z * (22 + z * (6 + z * (20 + z * (32 + z * (40 + z * (40 + z * (9 + z * (0 + z * (29 + z * (23 + z * (14 + z * (13 + z * (27 + z * (4 + z * (13 + z * (39 + z * 5))))))))))))))))))

def pow16_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-5) + z * ((-19) + z * ((-31) + z * ((-15) + z * ((-25) + z * ((-41) + z * ((-64) + z * ((-63) + z * ((-54) + z * ((-64) + z * ((-65) + z * ((-71) + z * ((-76) + z * ((-53) + z * ((-92) + z * ((-76) + z * ((-71) + z * ((-91) + z * ((-88) + z * ((-62) + z * ((-59) + z * ((-94) + z * ((-46) + z * ((-28) + z * ((-65) + z * ((-67) + z * ((-14) + z * (9 + z * ((-5) + z * (6 + z * (19 + z * (21 + z * (25 + z * (3 + z * (31 + z * (34 + z * (21 + z * (35 + z * 19))))))))))))))))))))))))))))))))))))))


def pow16_4 {R : Type*} [CommRing R] (z : R) : R := (20 + z * (22 + z * (25 + z * (9 + z * (39 + z * (20 + z * (35 + z * (18 + z * (37 + z * (2 + z * (27 + z * (33 + z * (37 + z * (25 + z * (5 + z * (32 + z * (28 + z * (19 + z * (8 + z * 3)))))))))))))))))))

def pow16_4_q {R : Type*} [CommRing R] (z : R) : R := (40 + z * (36 + z * (33 + z * (11 + z * (11 + z * (5 + z * (24 + z * (10 + z * (15 + z * (19 + z * (9 + z * (33 + z * (28 + z * (7 + z * (34 + z * (11 + z * (27 + z * (0 + z * 23))))))))))))))))))

def pow16_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-35) + z * ((-38) + z * ((-47) + z * ((-22) + z * ((-45) + z * ((-14) + z * ((-27) + z * ((-4) + z * ((-3) + z * (16 + z * (21 + z * ((-26) + z * (22 + z * (46 + z * (34 + z * (70 + z * ((-14) + z * (27 + z * (32 + z * (86 + z * (101 + z * (81 + z * (73 + z * (87 + z * (94 + z * (97 + z * (92 + z * (28 + z * (20 + z * (42 + z * (24 + z * (14 + z * (32 + z * ((-17) + z * ((-1) + z * (14 + z * (34 + z * ((-2) + z * 1))))))))))))))))))))))))))))))))))))))


def pow16_5 {R : Type*} [CommRing R] (z : R) : R := (29 + z * (35 + z * (34 + z * (29 + z * (2 + z * (4 + z * (27 + z * (0 + z * (4 + z * (2 + z * (16 + z * (16 + z * (20 + z * (40 + z * (3 + z * (9 + z * (26 + z * (36 + z * (38 + z * 18)))))))))))))))))))

def pow16_5_q {R : Type*} [CommRing R] (z : R) : R := (40 + z * (17 + z * (7 + z * (36 + z * (39 + z * (0 + z * (30 + z * (31 + z * (23 + z * (20 + z * (17 + z * (36 + z * (20 + z * (6 + z * (29 + z * (24 + z * (34 + z * (5 + z * 2))))))))))))))))))

def pow16_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-29) + z * ((-19) + z * ((-29) + z * ((-32) + z * ((-45) + z * ((-17) + z * ((-21) + z * ((-55) + z * ((-56) + z * ((-18) + z * ((-40) + z * ((-85) + z * ((-31) + z * ((-29) + z * ((-58) + z * ((-59) + z * ((-56) + z * ((-29) + z * ((-74) + z * ((-31) + z * ((-3) + z * (11 + z * ((-45) + z * ((-23) + z * (15 + z * ((-3) + z * ((-12) + z * ((-12) + z * (11 + z * (27 + z * (1 + z * (1 + z * (3 + z * (0 + z * (21 + z * (10 + z * (15 + z * (6 + z * 2))))))))))))))))))))))))))))))))))))))


def pow16_10 {R : Type*} [CommRing R] (z : R) : R := (31 + z * (33 + z * (12 + z * (9 + z * (36 + z * (1 + z * (39 + z * (2 + z * (16 + z * (39 + z * (8 + z * (24 + z * (2 + z * (19 + z * (29 + z * (0 + z * (37 + z * (26 + z * (8 + z * 19)))))))))))))))))))

def pow16_10_q {R : Type*} [CommRing R] (z : R) : R := (2 + z * (24 + z * (36 + z * (26 + z * (17 + z * (1 + z * (21 + z * (26 + z * (20 + z * (27 + z * (32 + z * (8 + z * (40 + z * (35 + z * (36 + z * (25 + z * (29 + z * (12 + z * 37))))))))))))))))))

def pow16_10_mul_t {R : Type*} [CommRing R] (z : R) : R := (18 + z * (27 + z * (37 + z * (47 + z * (28 + z * (12 + z * (5 + z * ((-2) + z * ((-23) + z * ((-47) + z * ((-79) + z * ((-43) + z * ((-26) + z * ((-1) + z * ((-41) + z * ((-30) + z * ((-56) + z * ((-69) + z * ((-23) + z * (49 + z * ((-57) + z * ((-67) + z * ((-97) + z * ((-76) + z * ((-67) + z * ((-109) + z * ((-89) + z * ((-88) + z * ((-57) + z * ((-31) + z * (1 + z * ((-15) + z * ((-39) + z * ((-31) + z * (20 + z * (42 + z * (42 + z * (6 + z * 7))))))))))))))))))))))))))))))))))))))


def pow16_20 {R : Type*} [CommRing R] (z : R) : R := (34 + z * (26 + z * (9 + z * (32 + z * (10 + z * (19 + z * (2 + z * (37 + z * (33 + z * (19 + z * (3 + z * (1 + z * (0 + z * (27 + z * (35 + z * (5 + z * (39 + z * (15 + z * (2 + z * 4)))))))))))))))))))

def pow16_20_q {R : Type*} [CommRing R] (z : R) : R := (36 + z * (34 + z * (38 + z * (30 + z * (25 + z * (12 + z * (24 + z * (21 + z * (25 + z * (29 + z * (10 + z * (23 + z * (33 + z * (34 + z * (25 + z * (23 + z * (38 + z * (11 + z * 33))))))))))))))))))

def pow16_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-9) + z * (8 + z * ((-26) + z * ((-32) + z * ((-16) + z * ((-8) + z * (5 + z * ((-12) + z * ((-34) + z * ((-15) + z * (31 + z * ((-65) + z * ((-20) + z * ((-51) + z * ((-42) + z * ((-26) + z * ((-133) + z * ((-11) + z * ((-81) + z * ((-93) + z * ((-31) + z * ((-96) + z * ((-31) + z * ((-42) + z * ((-86) + z * ((-10) + z * ((-72) + z * ((-48) + z * ((-54) + z * ((-81) + z * ((-27) + z * ((-71) + z * ((-47) + z * ((-14) + z * ((-35) + z * ((-7) + z * (3 + z * ((-17) + z * 8))))))))))))))))))))))))))))))))))))))


def pow16_40 {R : Type*} [CommRing R] (z : R) : R := (11 + z * (25 + z * (14 + z * (16 + z * (17 + z * (18 + z * (23 + z * (13 + z * (1 + z * (13 + z * (11 + z * (6 + z * (35 + z * (22 + z * (29 + z * (37 + z * (0 + z * (26 + z * (1 + z * 8)))))))))))))))))))

def pow16_40_q {R : Type*} [CommRing R] (z : R) : R := (17 + z * (40 + z * (25 + z * (37 + z * (29 + z * (3 + z * (30 + z * (12 + z * (12 + z * (5 + z * (2 + z * (18 + z * (30 + z * (16 + z * (37 + z * (17 + z * (37 + z * (28 + z * 16))))))))))))))))))

def pow16_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (13 + z * (2 + z * ((-16) + z * ((-6) + z * ((-11) + z * ((-15) + z * ((-18) + z * (18 + z * (30 + z * (33 + z * (15 + z * ((-24) + z * ((-35) + z * ((-32) + z * ((-3) + z * ((-28) + z * ((-7) + z * ((-13) + z * ((-118) + z * ((-80) + z * ((-86) + z * ((-16) + z * ((-47) + z * ((-29) + z * ((-17) + z * ((-65) + z * ((-62) + z * ((-59) + z * ((-77) + z * ((-49) + z * ((-25) + z * ((-78) + z * ((-52) + z * ((-56) + z * ((-47) + z * ((-39) + z * ((-25) + z * ((-12) + z * 0))))))))))))))))))))))))))))))))))))))


def pow16_41 {R : Type*} [CommRing R] (z : R) : R := (37 + z * (22 + z * (16 + z * (31 + z * (12 + z * (28 + z * (39 + z * (39 + z * (25 + z * (11 + z * (6 + z * (28 + z * (12 + z * (1 + z * (9 + z * (7 + z * (28 + z * (3 + z * (36 + z * 13)))))))))))))))))))

def pow16_41_q {R : Type*} [CommRing R] (z : R) : R := (34 + z * (14 + z * (28 + z * (40 + z * (23 + z * (2 + z * (32 + z * (17 + z * (21 + z * (21 + z * (35 + z * (20 + z * (12 + z * (40 + z * (13 + z * (2 + z * (37 + z * (18 + z * 19))))))))))))))))))

def pow16_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-27) + z * ((-14) + z * ((-46) + z * ((-42) + z * ((-55) + z * ((-22) + z * ((-38) + z * ((-58) + z * ((-65) + z * ((-36) + z * ((-92) + z * ((-92) + z * ((-63) + z * ((-88) + z * ((-82) + z * ((-72) + z * ((-76) + z * ((-105) + z * ((-111) + z * ((-60) + z * ((-88) + z * ((-82) + z * ((-53) + z * ((-44) + z * ((-65) + z * ((-54) + z * ((-44) + z * ((-52) + z * ((-28) + z * ((-36) + z * (8 + z * (6 + z * ((-20) + z * (0 + z * (1 + z * ((-22) + z * (1 + z * ((-8) + z * 5))))))))))))))))))))))))))))))))))))))


abbrev u16 {R : Type*} [CommRing R] (z : R) : R := pow16_41 z

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Powers09
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41
def pow17_2 {R : Type*} [CommRing R] (z : R) : R := (27 + z * (34 + z * (10 + z * (7 + z * (17 + z * (21 + z * (5 + z * (36 + z * (23 + z * (26 + z * (33 + z * (12 + z * (17 + z * (10 + z * (23 + z * (16 + z * (8 + z * (18 + z * (39 + z * 20)))))))))))))))))))

def pow17_2_q {R : Type*} [CommRing R] (z : R) : R := (35 + z * (10 + z * (11 + z * (14 + z * (27 + z * (25 + z * (21 + z * (24 + z * (25 + z * (28 + z * (14 + z * (32 + z * (0 + z * (35 + z * (14 + z * (33 + z * (13 + z * (7 + z * 5))))))))))))))))))

def pow17_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (2 + z * (19 + z * (2 + z * (49 + z * ((-3) + z * (34 + z * (76 + z * (64 + z * (69 + z * (55 + z * (50 + z * (42 + z * (73 + z * (21 + z * (49 + z * ((-63) + z * ((-1) + z * ((-29) + z * (24 + z * (3 + z * ((-49) + z * ((-4) + z * ((-25) + z * ((-12) + z * ((-15) + z * ((-13) + z * ((-35) + z * ((-34) + z * ((-61) + z * ((-34) + z * ((-42) + z * ((-46) + z * ((-33) + z * ((-20) + z * (16 + z * (7 + z * (26 + z * (19 + z * 4))))))))))))))))))))))))))))))))))))))


def pow17_4 {R : Type*} [CommRing R] (z : R) : R := (2 + z * (14 + z * (13 + z * (0 + z * (33 + z * (19 + z * (6 + z * (35 + z * (30 + z * (6 + z * (5 + z * (9 + z * (4 + z * (35 + z * (12 + z * (21 + z * (20 + z * (34 + z * (17 + z * 40)))))))))))))))))))

def pow17_4_q {R : Type*} [CommRing R] (z : R) : R := (35 + z * (30 + z * (17 + z * (36 + z * (35 + z * (6 + z * (28 + z * (27 + z * (5 + z * (38 + z * (25 + z * (36 + z * (18 + z * (34 + z * (18 + z * (23 + z * (34 + z * (15 + z * 31))))))))))))))))))

def pow17_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-13) + z * (7 + z * ((-9) + z * ((-34) + z * ((-47) + z * ((-12) + z * ((-20) + z * ((-26) + z * ((-1) + z * (6 + z * (5 + z * ((-54) + z * ((-3) + z * ((-59) + z * ((-24) + z * ((-41) + z * ((-64) + z * ((-63) + z * ((-60) + z * (2 + z * ((-78) + z * ((-50) + z * ((-49) + z * ((-36) + z * ((-24) + z * ((-36) + z * ((-22) + z * ((-20) + z * ((-26) + z * ((-44) + z * ((-54) + z * ((-39) + z * ((-36) + z * ((-22) + z * ((-26) + z * ((-7) + z * (30 + z * (15 + z * 9))))))))))))))))))))))))))))))))))))))


def pow17_5 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (30 + z * (32 + z * (6 + z * (32 + z * (10 + z * (0 + z * (16 + z * (28 + z * (24 + z * (13 + z * (19 + z * (24 + z * (2 + z * (25 + z * (6 + z * (40 + z * (10 + z * (9 + z * 14)))))))))))))))))))

def pow17_5_q {R : Type*} [CommRing R] (z : R) : R := (21 + z * (22 + z * (9 + z * (30 + z * (31 + z * (15 + z * (38 + z * (7 + z * (8 + z * (39 + z * (17 + z * (20 + z * (1 + z * (3 + z * (19 + z * (35 + z * (12 + z * (1 + z * 28))))))))))))))))))

def pow17_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-17) + z * ((-13) + z * ((-11) + z * ((-32) + z * ((-15) + z * ((-15) + z * ((-28) + z * (19 + z * (5 + z * (6 + z * ((-4) + z * ((-22) + z * (12 + z * (11 + z * (4 + z * ((-16) + z * ((-24) + z * ((-42) + z * ((-31) + z * (13 + z * (0 + z * ((-1) + z * ((-4) + z * (25 + z * (45 + z * ((-5) + z * (8 + z * (1 + z * ((-22) + z * ((-18) + z * ((-22) + z * (13 + z * ((-10) + z * ((-2) + z * ((-9) + z * (39 + z * (16 + z * (20 + z * 12))))))))))))))))))))))))))))))))))))))


def pow17_10 {R : Type*} [CommRing R] (z : R) : R := (39 + z * (29 + z * (11 + z * (13 + z * (8 + z * (20 + z * (35 + z * (34 + z * (28 + z * (34 + z * (23 + z * (0 + z * (3 + z * (22 + z * (24 + z * (28 + z * (2 + z * (5 + z * (33 + z * 7)))))))))))))))))))

def pow17_10_q {R : Type*} [CommRing R] (z : R) : R := (12 + z * (21 + z * (11 + z * (2 + z * (13 + z * (22 + z * (3 + z * (13 + z * (34 + z * (18 + z * (11 + z * (1 + z * (12 + z * (13 + z * (36 + z * (31 + z * (24 + z * (30 + z * 32))))))))))))))))))

def pow17_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-6) + z * ((-1) + z * (20 + z * (30 + z * (27 + z * (20 + z * (34 + z * ((-6) + z * (1 + z * (21 + z * (32 + z * (43 + z * (28 + z * (51 + z * (7 + z * ((-21) + z * (3 + z * ((-7) + z * (12 + z * ((-30) + z * (15 + z * ((-10) + z * ((-53) + z * ((-18) + z * ((-39) + z * ((-47) + z * ((-26) + z * ((-30) + z * ((-16) + z * ((-75) + z * ((-26) + z * ((-63) + z * ((-53) + z * ((-66) + z * ((-52) + z * ((-17) + z * ((-27) + z * ((-18) + z * 4))))))))))))))))))))))))))))))))))))))


def pow17_20 {R : Type*} [CommRing R] (z : R) : R := (20 + z * (8 + z * (21 + z * (21 + z * (16 + z * (20 + z * (35 + z * (9 + z * (20 + z * (13 + z * (27 + z * (31 + z * (4 + z * (13 + z * (12 + z * (25 + z * (14 + z * (24 + z * (35 + z * 37)))))))))))))))))))

def pow17_20_q {R : Type*} [CommRing R] (z : R) : R := (36 + z * (20 + z * (39 + z * (9 + z * (23 + z * (8 + z * (32 + z * (33 + z * (15 + z * (29 + z * (9 + z * (0 + z * (17 + z * (12 + z * (34 + z * (34 + z * (21 + z * (17 + z * 8))))))))))))))))))

def pow17_20_mul_t {R : Type*} [CommRing R] (z : R) : R := (5 + z * (26 + z * ((-26) + z * (4 + z * ((-44) + z * (14 + z * (21 + z * (43 + z * (33 + z * (37 + z * (51 + z * ((-7) + z * (13 + z * (36 + z * (41 + z * (65 + z * ((-19) + z * ((-65) + z * ((-8) + z * ((-12) + z * ((-10) + z * ((-23) + z * ((-11) + z * ((-9) + z * (6 + z * ((-31) + z * ((-38) + z * (7 + z * ((-6) + z * ((-49) + z * ((-58) + z * ((-49) + z * ((-26) + z * ((-18) + z * ((-37) + z * ((-19) + z * (12 + z * (5 + z * 1))))))))))))))))))))))))))))))))))))))


def pow17_40 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (5 + z * (29 + z * (12 + z * (21 + z * (37 + z * (7 + z * (31 + z * (14 + z * (32 + z * (28 + z * (26 + z * (28 + z * (24 + z * (30 + z * (35 + z * (19 + z * (36 + z * (37 + z * 23)))))))))))))))))))

def pow17_40_q {R : Type*} [CommRing R] (z : R) : R := (5 + z * (32 + z * (12 + z * (16 + z * (4 + z * (4 + z * (25 + z * (34 + z * (12 + z * (37 + z * (17 + z * (25 + z * (13 + z * (39 + z * (13 + z * (26 + z * (27 + z * (19 + z * 16))))))))))))))))))

def pow17_40_mul_t {R : Type*} [CommRing R] (z : R) : R := (5 + z * ((-22) + z * ((-3) + z * ((-13) + z * (12 + z * (4 + z * (29 + z * ((-1) + z * (12 + z * ((-12) + z * (12 + z * (1 + z * (24 + z * ((-20) + z * (3 + z * ((-20) + z * ((-13) + z * ((-37) + z * ((-24) + z * (40 + z * ((-7) + z * (57 + z * (10 + z * (10 + z * (8 + z * (1 + z * ((-20) + z * ((-9) + z * ((-7) + z * (17 + z * ((-3) + z * ((-32) + z * ((-19) + z * (15 + z * (29 + z * (29 + z * (52 + z * (51 + z * 33))))))))))))))))))))))))))))))))))))))


def pow17_41 {R : Type*} [CommRing R] (z : R) : R := (34 + z * (9 + z * (39 + z * (20 + z * (17 + z * (14 + z * (34 + z * (29 + z * (18 + z * (11 + z * (3 + z * (26 + z * (37 + z * (1 + z * (26 + z * (38 + z * (20 + z * (20 + z * (11 + z * 34)))))))))))))))))))

def pow17_41_q {R : Type*} [CommRing R] (z : R) : R := (27 + z * (10 + z * (26 + z * (33 + z * (11 + z * (6 + z * (34 + z * (30 + z * (38 + z * (16 + z * (39 + z * (22 + z * (39 + z * (38 + z * (22 + z * (10 + z * (9 + z * (6 + z * 12))))))))))))))))))

def pow17_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-11) + z * ((-5) + z * ((-12) + z * ((-6) + z * ((-16) + z * (38 + z * (6 + z * (11 + z * (13 + z * (36 + z * (4 + z * (28 + z * (19 + z * (21 + z * ((-12) + z * (19 + z * (41 + z * (5 + z * (49 + z * (25 + z * (50 + z * (37 + z * (2 + z * (40 + z * (7 + z * (6 + z * ((-10) + z * ((-36) + z * ((-24) + z * ((-26) + z * (1 + z * ((-4) + z * (1 + z * (36 + z * (35 + z * (40 + z * (36 + z * (23 + z * 7))))))))))))))))))))))))))))))))))))))


abbrev u17 {R : Type*} [CommRing R] (z : R) : R := pow17_41 z


def pow18_2 {R : Type*} [CommRing R] (z : R) : R := (18 + z * (30 + z * (17 + z * (31 + z * (23 + z * (40 + z * (12 + z * (11 + z * (21 + z * (39 + z * (29 + z * (4 + z * (15 + z * (15 + z * (20 + z * (34 + z * (10 + z * (26 + z * (33 + z * 31)))))))))))))))))))

def pow18_2_q {R : Type*} [CommRing R] (z : R) : R := (2 + z * (20 + z * (21 + z * (23 + z * (18 + z * (34 + z * (25 + z * (40 + z * (31 + z * (25 + z * (24 + z * (15 + z * (38 + z * (20 + z * (34 + z * (35 + z * (4 + z * (16 + z * 8))))))))))))))))))

def pow18_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (26 + z * ((-4) + z * (40 + z * (8 + z * (33 + z * ((-1) + z * (39 + z * (15 + z * (34 + z * (7 + z * ((-7) + z * (15 + z * (0 + z * (1 + z * (23 + z * (4 + z * ((-18) + z * (22 + z * (35 + z * (28 + z * ((-5) + z * (22 + z * ((-26) + z * ((-1) + z * ((-41) + z * ((-30) + z * (3 + z * (0 + z * ((-29) + z * ((-21) + z * (20 + z * (26 + z * ((-9) + z * (21 + z * (40 + z * (29 + z * (21 + z * (12 + z * 28))))))))))))))))))))))))))))))))))))))


def pow18_4 {R : Type*} [CommRing R] (z : R) : R := (28 + z * (27 + z * (34 + z * (6 + z * (9 + z * (10 + z * (24 + z * (33 + z * (40 + z * (6 + z * (35 + z * (5 + z * (36 + z * (5 + z * (33 + z * (40 + z * (24 + z * (39 + z * (7 + z * 23)))))))))))))))))))

def pow18_4_q {R : Type*} [CommRing R] (z : R) : R := (31 + z * (34 + z * (28 + z * (21 + z * (31 + z * (16 + z * (33 + z * (34 + z * (11 + z * (28 + z * (33 + z * (17 + z * (10 + z * (29 + z * (29 + z * (22 + z * (19 + z * (30 + z * 18))))))))))))))))))

def pow18_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * ((-14) + z * ((-22) + z * ((-1) + z * ((-7) + z * (24 + z * (27 + z * ((-4) + z * (2 + z * (19 + z * (42 + z * ((-10) + z * (17 + z * (19 + z * (0 + z * ((-3) + z * ((-33) + z * ((-48) + z * (17 + z * (48 + z * (37 + z * ((-15) + z * (38 + z * (48 + z * (28 + z * ((-38) + z * ((-8) + z * (51 + z * (18 + z * ((-17) + z * ((-12) + z * ((-3) + z * (2 + z * (16 + z * (28 + z * (20 + z * (36 + z * (36 + z * 23))))))))))))))))))))))))))))))))))))))


def pow18_5 {R : Type*} [CommRing R] (z : R) : R := (11 + z * (1 + z * (29 + z * (11 + z * (25 + z * (24 + z * (35 + z * (29 + z * (25 + z * (34 + z * (27 + z * (7 + z * (5 + z * (21 + z * (39 + z * (28 + z * (1 + z * (13 + z * (27 + z * 9)))))))))))))))))))

def pow18_5_q {R : Type*} [CommRing R] (z : R) : R := (25 + z * (28 + z * (1 + z * (32 + z * (31 + z * (20 + z * (11 + z * (30 + z * (33 + z * (36 + z * (7 + z * (22 + z * (10 + z * (23 + z * (29 + z * (26 + z * (32 + z * (32 + z * 3))))))))))))))))))

def pow18_5_mul_t {R : Type*} [CommRing R] (z : R) : R := (1 + z * ((-4) + z * (32 + z * (2 + z * (7 + z * ((-23) + z * (35 + z * (11 + z * (23 + z * (6 + z * (36 + z * ((-39) + z * (51 + z * (22 + z * (62 + z * ((-7) + z * (13 + z * (39 + z * (7 + z * (43 + z * (13 + z * (55 + z * (29 + z * (10 + z * ((-4) + z * (8 + z * (30 + z * (23 + z * ((-15) + z * (49 + z * (1 + z * (32 + z * ((-14) + z * (11 + z * (30 + z * (6 + z * (20 + z * (9 + z * 19))))))))))))))))))))))))))))))))))))))


def pow18_10 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (37 + z * (29 + z * (25 + z * (2 + z * (3 + z * (20 + z * (6 + z * (31 + z * (39 + z * (34 + z * (4 + z * (8 + z * (22 + z * (12 + z * (5 + z * (38 + z * (18 + z * (19 + z * 8)))))))))))))))))))

def pow18_10_q {R : Type*} [CommRing R] (z : R) : R := (26 + z * (5 + z * (6 + z * (4 + z * (30 + z * (17 + z * (13 + z * (14 + z * (28 + z * (1 + z * (1 + z * (33 + z * (39 + z * (28 + z * (19 + z * (38 + z * (14 + z * (24 + z * 40))))))))))))))))))

def pow18_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * ((-13) + z * ((-11) + z * ((-3) + z * ((-18) + z * ((-5) + z * (13 + z * (10 + z * (12 + z * (56 + z * (71 + z * (50 + z * (40 + z * (51 + z * (57 + z * (6 + z * (42 + z * (48 + z * (14 + z * ((-3) + z * (46 + z * (54 + z * ((-2) + z * (30 + z * (47 + z * ((-19) + z * ((-49) + z * ((-26) + z * ((-11) + z * ((-61) + z * ((-87) + z * ((-60) + z * ((-29) + z * ((-38) + z * ((-62) + z * ((-26) + z * ((-11) + z * ((-18) + z * 1))))))))))))))))))))))))))))))))))))))


def pow18_20 {R : Type*} [CommRing R] (z : R) : R := (7 + z * (34 + z * (10 + z * (19 + z * (19 + z * (38 + z * (17 + z * (16 + z * (28 + z * (35 + z * (40 + z * (17 + z * (32 + z * (7 + z * (4 + z * (26 + z * (17 + z * (29 + z * (20 + z * 34)))))))))))))))))))

def pow18_20_q {R : Type*} [CommRing R] (z : R) : R := (21 + z * (12 + z * (16 + z * (36 + z * (34 + z * (30 + z * (31 + z * (0 + z * (40 + z * (12 + z * (36 + z * (39 + z * (39 + z * (6 + z * (18 + z * (29 + z * (30 + z * (24 + z * 23))))))))))))))))))

def pow18_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-18) + z * ((-9) + z * (7 + z * (12 + z * ((-4) + z * ((-37) + z * ((-49) + z * ((-36) + z * ((-60) + z * (21 + z * ((-10) + z * (29 + z * ((-60) + z * ((-62) + z * ((-62) + z * ((-74) + z * ((-72) + z * ((-35) + z * ((-31) + z * ((-53) + z * ((-90) + z * ((-96) + z * ((-94) + z * ((-95) + z * ((-56) + z * ((-50) + z * ((-23) + z * ((-74) + z * ((-62) + z * ((-66) + z * ((-68) + z * ((-67) + z * ((-29) + z * ((-39) + z * ((-21) + z * ((-14) + z * ((-12) + z * ((-10) + z * 1))))))))))))))))))))))))))))))))))))))


def pow18_40 {R : Type*} [CommRing R] (z : R) : R := (35 + z * (19 + z * (21 + z * (12 + z * (14 + z * (5 + z * (0 + z * (16 + z * (14 + z * (38 + z * (40 + z * (31 + z * (35 + z * (1 + z * (25 + z * (23 + z * (25 + z * (14 + z * (2 + z * 7)))))))))))))))))))

def pow18_40_q {R : Type*} [CommRing R] (z : R) : R := (30 + z * (3 + z * (23 + z * (20 + z * (21 + z * (10 + z * (26 + z * (27 + z * (18 + z * (6 + z * (30 + z * (22 + z * (39 + z * (5 + z * (30 + z * (36 + z * (1 + z * (13 + z * 8))))))))))))))))))

def pow18_40_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-26) + z * ((-1) + z * ((-12) + z * ((-5) + z * ((-25) + z * (17 + z * (26 + z * ((-13) + z * (8 + z * (46 + z * (47 + z * (46 + z * (27 + z * (95 + z * (7 + z * (29 + z * (40 + z * (45 + z * (56 + z * (28 + z * (145 + z * (47 + z * (45 + z * (41 + z * (84 + z * (35 + z * (21 + z * (80 + z * (54 + z * (23 + z * ((-8) + z * (0 + z * (5 + z * (1 + z * (39 + z * (45 + z * (45 + z * (27 + z * 28))))))))))))))))))))))))))))))))))))))


def pow18_41 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (30 + z * (36 + z * (31 + z * (11 + z * (39 + z * (17 + z * (26 + z * (7 + z * (11 + z * (5 + z * (8 + z * (12 + z * (9 + z * (5 + z * (8 + z * (33 + z * (10 + z * (5 + z * 29)))))))))))))))))))

def pow18_41_q {R : Type*} [CommRing R] (z : R) : R := (9 + z * (34 + z * (3 + z * (9 + z * (26 + z * (31 + z * (14 + z * (11 + z * (18 + z * (26 + z * (16 + z * (37 + z * (35 + z * (34 + z * (14 + z * (25 + z * (7 + z * (16 + z * 33))))))))))))))))))

def pow18_41_mul_t {R : Type*} [CommRing R] (z : R) : R := (21 + z * ((-10) + z * (34 + z * (15 + z * (22 + z * ((-22) + z * (16 + z * (24 + z * ((-10) + z * (13 + z * (29 + z * (19 + z * (21 + z * ((-14) + z * (55 + z * (12 + z * (41 + z * (30 + z * (15 + z * ((-4) + z * ((-57) + z * (16 + z * ((-25) + z * ((-2) + z * ((-10) + z * ((-31) + z * (5 + z * ((-14) + z * ((-19) + z * ((-22) + z * ((-21) + z * (1 + z * ((-40) + z * ((-15) + z * ((-17) + z * ((-2) + z * ((-10) + z * ((-21) + z * 5))))))))))))))))))))))))))))))))))))))


abbrev u18 {R : Type*} [CommRing R] (z : R) : R := pow18_41 z

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Powers10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41
def pow19_2 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (39 + z * (34 + z * (14 + z * (14 + z * (15 + z * (25 + z * (2 + z * (10 + z * (31 + z * (12 + z * (31 + z * (0 + z * (23 + z * (24 + z * (2 + z * (32 + z * (17 + z * (5 + z * 32)))))))))))))))))))

def pow19_2_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (0 + z * (38 + z * (9 + z * (31 + z * (28 + z * (33 + z * (12 + z * (13 + z * (34 + z * (14 + z * (33 + z * (24 + z * (34 + z * (15 + z * (18 + z * (34 + z * (29 + z * 21))))))))))))))))))

def pow19_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-34) + z * ((-6) + z * ((-32) + z * (39 + z * ((-9) + z * (33 + z * (12 + z * (31 + z * (46 + z * ((-6) + z * (12 + z * ((-57) + z * ((-22) + z * ((-96) + z * ((-53) + z * ((-102) + z * ((-125) + z * ((-100) + z * ((-85) + z * ((-95) + z * ((-98) + z * ((-56) + z * ((-63) + z * ((-95) + z * ((-85) + z * ((-110) + z * ((-84) + z * ((-116) + z * ((-108) + z * ((-90) + z * ((-86) + z * ((-72) + z * ((-63) + z * ((-55) + z * ((-39) + z * (0 + z * ((-16) + z * ((-9) + z * 20))))))))))))))))))))))))))))))))))))))


def pow19_4 {R : Type*} [CommRing R] (z : R) : R := (20 + z * (18 + z * (36 + z * (5 + z * (21 + z * (32 + z * (35 + z * (27 + z * (31 + z * (16 + z * (14 + z * (21 + z * (17 + z * (2 + z * (2 + z * (12 + z * (39 + z * (22 + z * (27 + z * 28)))))))))))))))))))

def pow19_4_q {R : Type*} [CommRing R] (z : R) : R := (0 + z * (32 + z * (25 + z * (29 + z * (14 + z * (18 + z * (9 + z * (33 + z * (12 + z * (28 + z * (10 + z * (26 + z * (1 + z * (5 + z * (22 + z * (26 + z * (19 + z * (22 + z * 40))))))))))))))))))

def pow19_4_mul_t {R : Type*} [CommRing R] (z : R) : R := (5 + z * (0 + z * (29 + z * (18 + z * (24 + z * ((-7) + z * (26 + z * (11 + z * ((-2) + z * ((-33) + z * (27 + z * (5 + z * (30 + z * ((-1) + z * (15 + z * (19 + z * ((-28) + z * ((-5) + z * ((-60) + z * ((-12) + z * (9 + z * ((-26) + z * ((-30) + z * ((-30) + z * ((-29) + z * ((-17) + z * ((-71) + z * (11 + z * ((-7) + z * ((-35) + z * (13 + z * ((-45) + z * ((-18) + z * ((-26) + z * ((-54) + z * (8 + z * ((-6) + z * ((-22) + z * 24))))))))))))))))))))))))))))))))))))))


def pow19_5 {R : Type*} [CommRing R] (z : R) : R := (10 + z * (2 + z * (8 + z * (32 + z * (24 + z * (29 + z * (31 + z * (6 + z * (4 + z * (5 + z * (3 + z * (15 + z * (37 + z * (13 + z * (12 + z * (10 + z * (12 + z * (30 + z * (40 + z * 6)))))))))))))))))))

def pow19_5_q {R : Type*} [CommRing R] (z : R) : R := (23 + z * (37 + z * (38 + z * (13 + z * (21 + z * (39 + z * (21 + z * (20 + z * (25 + z * (5 + z * (35 + z * (18 + z * (11 + z * (5 + z * (25 + z * (38 + z * (1 + z * (15 + z * 33))))))))))))))))))

def pow19_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-18) + z * ((-23) + z * ((-27) + z * (6 + z * ((-13) + z * ((-9) + z * (3 + z * (41 + z * (14 + z * (21 + z * (6 + z * (19 + z * ((-30) + z * (16 + z * ((-32) + z * ((-83) + z * ((-74) + z * ((-70) + z * ((-55) + z * ((-62) + z * ((-29) + z * ((-3) + z * ((-54) + z * (2 + z * ((-3) + z * ((-52) + z * ((-57) + z * ((-26) + z * ((-26) + z * ((-75) + z * ((-45) + z * ((-24) + z * ((-20) + z * ((-37) + z * ((-18) + z * (33 + z * (1 + z * ((-2) + z * 19))))))))))))))))))))))))))))))))))))))


def pow19_10 {R : Type*} [CommRing R] (z : R) : R := (34 + z * (2 + z * (22 + z * (11 + z * (8 + z * (17 + z * (15 + z * (1 + z * (33 + z * (36 + z * (23 + z * (40 + z * (3 + z * (38 + z * (35 + z * (16 + z * (10 + z * (11 + z * (37 + z * 35)))))))))))))))))))

def pow19_10_q {R : Type*} [CommRing R] (z : R) : R := (36 + z * (4 + z * (34 + z * (12 + z * (22 + z * (29 + z * (21 + z * (27 + z * (6 + z * (1 + z * (18 + z * (13 + z * (15 + z * (27 + z * (30 + z * (23 + z * (37 + z * (15 + z * 36))))))))))))))))))

def pow19_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-30) + z * ((-14) + z * ((-54) + z * ((-9) + z * ((-60) + z * ((-21) + z * ((-20) + z * ((-40) + z * (3 + z * ((-1) + z * ((-13) + z * ((-38) + z * ((-39) + z * ((-75) + z * ((-90) + z * ((-58) + z * ((-77) + z * ((-52) + z * ((-78) + z * ((-81) + z * ((-62) + z * ((-30) + z * ((-36) + z * ((-4) + z * ((-11) + z * ((-81) + z * ((-74) + z * ((-62) + z * ((-50) + z * ((-30) + z * ((-8) + z * ((-46) + z * ((-65) + z * ((-56) + z * ((-22) + z * (8 + z * (21 + z * ((-15) + z * 0))))))))))))))))))))))))))))))))))))))


def pow19_20 {R : Type*} [CommRing R] (z : R) : R := (17 + z * (35 + z * (6 + z * (5 + z * (1 + z * (37 + z * (25 + z * (34 + z * (28 + z * (38 + z * (22 + z * (23 + z * (34 + z * (34 + z * (39 + z * (7 + z * (40 + z * (12 + z * (39 + z * 7)))))))))))))))))))

def pow19_20_q {R : Type*} [CommRing R] (z : R) : R := (10 + z * (14 + z * (19 + z * (2 + z * (21 + z * (7 + z * (16 + z * (34 + z * (8 + z * (24 + z * (12 + z * (22 + z * (2 + z * (26 + z * (12 + z * (27 + z * (15 + z * (34 + z * 36))))))))))))))))))

def pow19_20_mul_t {R : Type*} [CommRing R] (z : R) : R := (19 + z * ((-13) + z * (8 + z * (2 + z * ((-15) + z * (13 + z * ((-11) + z * ((-28) + z * (18 + z * ((-4) + z * (33 + z * (32 + z * (5 + z * (56 + z * (54 + z * (2 + z * (36 + z * ((-4) + z * (25 + z * (94 + z * (28 + z * (48 + z * (61 + z * (58 + z * (77 + z * (3 + z * (30 + z * (117 + z * (70 + z * (50 + z * (25 + z * (19 + z * (36 + z * (6 + z * ((-26) + z * ((-9) + z * (12 + z * (36 + z * 29))))))))))))))))))))))))))))))))))))))


def pow19_40 {R : Type*} [CommRing R] (z : R) : R := (23 + z * (21 + z * (0 + z * (12 + z * (4 + z * (12 + z * (32 + z * (18 + z * (3 + z * (19 + z * (5 + z * (19 + z * (27 + z * (8 + z * (19 + z * (30 + z * (3 + z * (39 + z * (32 + z * 30)))))))))))))))))))

def pow19_40_q {R : Type*} [CommRing R] (z : R) : R := (37 + z * (10 + z * (36 + z * (29 + z * (37 + z * (13 + z * (9 + z * (23 + z * (33 + z * (16 + z * (19 + z * (10 + z * (28 + z * (23 + z * (29 + z * (35 + z * (40 + z * (19 + z * 8))))))))))))))))))

def pow19_40_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-26) + z * (8 + z * ((-27) + z * ((-31) + z * ((-87) + z * ((-24) + z * (14 + z * ((-9) + z * ((-5) + z * ((-4) + z * (21 + z * ((-11) + z * (20 + z * (67 + z * (68 + z * (28 + z * ((-1) + z * (55 + z * (50 + z * (89 + z * (48 + z * (108 + z * (74 + z * (118 + z * (93 + z * (127 + z * (86 + z * (71 + z * (60 + z * (32 + z * (53 + z * ((-10) + z * (26 + z * ((-31) + z * (22 + z * ((-6) + z * (23 + z * (7 + z * 1))))))))))))))))))))))))))))))))))))))


def pow19_41 {R : Type*} [CommRing R] (z : R) : R := (7 + z * (10 + z * (32 + z * (2 + z * (10 + z * (31 + z * (9 + z * (27 + z * (26 + z * (19 + z * (31 + z * (13 + z * (16 + z * (17 + z * (36 + z * (16 + z * (26 + z * (1 + z * (14 + z * 3)))))))))))))))))))

def pow19_41_q {R : Type*} [CommRing R] (z : R) : R := (3 + z * (23 + z * (14 + z * (9 + z * (24 + z * (26 + z * (35 + z * (36 + z * (0 + z * (1 + z * (32 + z * (29 + z * (3 + z * (40 + z * (12 + z * (6 + z * (35 + z * (29 + z * 9))))))))))))))))))

def pow19_41_mul_t {R : Type*} [CommRing R] (z : R) : R := (0 + z * ((-2) + z * (13 + z * (8 + z * ((-6) + z * ((-14) + z * ((-16) + z * ((-9) + z * (2 + z * ((-9) + z * ((-14) + z * ((-31) + z * ((-10) + z * ((-37) + z * ((-34) + z * ((-53) + z * ((-11) + z * ((-63) + z * ((-62) + z * (21 + z * ((-19) + z * ((-67) + z * ((-10) + z * ((-37) + z * ((-43) + z * ((-44) + z * ((-44) + z * ((-54) + z * ((-42) + z * ((-58) + z * ((-26) + z * ((-11) + z * ((-61) + z * ((-4) + z * (20 + z * ((-4) + z * (13 + z * (19 + z * 21))))))))))))))))))))))))))))))))))))))


abbrev u19 {R : Type*} [CommRing R] (z : R) : R := pow19_41 z


def pow20_2 {R : Type*} [CommRing R] (z : R) : R := (16 + z * (16 + z * (14 + z * (21 + z * (5 + z * (21 + z * (35 + z * (7 + z * (29 + z * (11 + z * (15 + z * (12 + z * (26 + z * (10 + z * (27 + z * (1 + z * (2 + z * (22 + z * (36 + z * 12)))))))))))))))))))

def pow20_2_q {R : Type*} [CommRing R] (z : R) : R := (18 + z * (22 + z * (1 + z * (17 + z * (12 + z * (21 + z * (14 + z * (14 + z * (27 + z * (6 + z * (32 + z * (8 + z * (31 + z * (16 + z * (34 + z * (32 + z * (12 + z * (19 + z * 9))))))))))))))))))

def pow20_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-15) + z * ((-22) + z * ((-8) + z * ((-16) + z * ((-2) + z * ((-36) + z * (1 + z * (2 + z * ((-36) + z * (18 + z * (0 + z * (3 + z * ((-10) + z * (16 + z * ((-21) + z * (1 + z * (1 + z * ((-17) + z * (14 + z * ((-26) + z * (12 + z * (9 + z * ((-24) + z * (9 + z * ((-11) + z * ((-32) + z * ((-22) + z * ((-42) + z * ((-20) + z * ((-58) + z * ((-32) + z * ((-62) + z * ((-32) + z * ((-51) + z * ((-27) + z * ((-18) + z * ((-13) + z * ((-5) + z * 0))))))))))))))))))))))))))))))))))))))


def pow20_4 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (25 + z * (14 + z * (1 + z * (38 + z * (7 + z * (18 + z * (11 + z * (0 + z * (13 + z * (24 + z * (17 + z * (10 + z * (36 + z * (16 + z * (16 + z * (24 + z * (15 + z * (34 + z * 36)))))))))))))))))))

def pow20_4_q {R : Type*} [CommRing R] (z : R) : R := (39 + z * (4 + z * (8 + z * (1 + z * (21 + z * (0 + z * (38 + z * (15 + z * (36 + z * (9 + z * (23 + z * (34 + z * (28 + z * (38 + z * (3 + z * (7 + z * (23 + z * (29 + z * 21))))))))))))))))))

def pow20_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-28) + z * ((-4) + z * ((-20) + z * (20 + z * ((-31) + z * (19 + z * (1 + z * ((-7) + z * ((-29) + z * (24 + z * ((-34) + z * ((-16) + z * ((-18) + z * ((-35) + z * (2 + z * ((-64) + z * ((-43) + z * ((-58) + z * ((-33) + z * ((-44) + z * ((-10) + z * ((-54) + z * ((-45) + z * ((-46) + z * ((-31) + z * ((-68) + z * ((-31) + z * ((-87) + z * ((-66) + z * ((-54) + z * ((-27) + z * ((-24) + z * ((-36) + z * ((-41) + z * ((-32) + z * ((-1) + z * (14 + z * (5 + z * 3))))))))))))))))))))))))))))))))))))))


def pow20_5 {R : Type*} [CommRing R] (z : R) : R := (10 + z * (30 + z * (29 + z * (24 + z * (25 + z * (20 + z * (34 + z * (1 + z * (16 + z * (12 + z * (34 + z * (9 + z * (19 + z * (7 + z * (20 + z * (31 + z * (26 + z * (29 + z * (3 + z * 34)))))))))))))))))))

def pow20_5_q {R : Type*} [CommRing R] (z : R) : R := (2 + z * (9 + z * (29 + z * (19 + z * (39 + z * (14 + z * (2 + z * (34 + z * (33 + z * (22 + z * (38 + z * (39 + z * (20 + z * (6 + z * (32 + z * (18 + z * (5 + z * (31 + z * 26))))))))))))))))))

def pow20_5_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-2) + z * ((-5) + z * ((-22) + z * ((-10) + z * ((-45) + z * ((-29) + z * ((-3) + z * ((-32) + z * ((-37) + z * ((-32) + z * ((-56) + z * ((-56) + z * ((-57) + z * ((-37) + z * ((-50) + z * ((-43) + z * ((-44) + z * ((-52) + z * ((-78) + z * ((-88) + z * ((-2) + z * ((-59) + z * ((-79) + z * ((-26) + z * ((-28) + z * ((-59) + z * ((-48) + z * ((-20) + z * ((-26) + z * ((-26) + z * ((-26) + z * ((-4) + z * ((-1) + z * ((-20) + z * ((-9) + z * ((-1) + z * ((-20) + z * ((-5) + z * 2))))))))))))))))))))))))))))))))))))))


def pow20_10 {R : Type*} [CommRing R] (z : R) : R := (3 + z * (13 + z * (22 + z * (27 + z * (2 + z * (6 + z * (30 + z * (18 + z * (6 + z * (40 + z * (6 + z * (21 + z * (20 + z * (8 + z * (36 + z * (35 + z * (29 + z * (36 + z * (18 + z * 19)))))))))))))))))))

def pow20_10_q {R : Type*} [CommRing R] (z : R) : R := (38 + z * (6 + z * (34 + z * (5 + z * (4 + z * (24 + z * (19 + z * (9 + z * (36 + z * (36 + z * (24 + z * (6 + z * (31 + z * (18 + z * (35 + z * (23 + z * (14 + z * (5 + z * 8))))))))))))))))))

def pow20_10_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-31) + z * ((-3) + z * ((-24) + z * (33 + z * (8 + z * (44 + z * (39 + z * (37 + z * (19 + z * ((-16) + z * ((-4) + z * (28 + z * (3 + z * ((-12) + z * ((-11) + z * ((-8) + z * ((-15) + z * ((-5) + z * (50 + z * (7 + z * (72 + z * (35 + z * (27 + z * ((-4) + z * ((-38) + z * (10 + z * ((-31) + z * ((-3) + z * ((-36) + z * (16 + z * ((-12) + z * (15 + z * (13 + z * (20 + z * (43 + z * (30 + z * (41 + z * ((-1) + z * 28))))))))))))))))))))))))))))))))))))))


def pow20_20 {R : Type*} [CommRing R] (z : R) : R := (15 + z * (14 + z * (31 + z * (14 + z * (27 + z * (8 + z * (11 + z * (38 + z * (39 + z * (34 + z * (32 + z * (35 + z * (5 + z * (25 + z * (39 + z * (19 + z * (37 + z * (24 + z * (40 + z * 11)))))))))))))))))))

def pow20_20_q {R : Type*} [CommRing R] (z : R) : R := (34 + z * (10 + z * (12 + z * (36 + z * (28 + z * (29 + z * (1 + z * (13 + z * (18 + z * (13 + z * (34 + z * (0 + z * (33 + z * (18 + z * (30 + z * (9 + z * (20 + z * (22 + z * 33))))))))))))))))))

def pow20_20_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-30) + z * ((-18) + z * ((-32) + z * ((-26) + z * ((-43) + z * ((-42) + z * ((-15) + z * ((-61) + z * ((-21) + z * ((-9) + z * ((-43) + z * ((-37) + z * ((-37) + z * ((-18) + z * ((-80) + z * ((-9) + z * ((-46) + z * ((-7) + z * ((-1) + z * ((-52) + z * (14 + z * (19 + z * ((-6) + z * (50 + z * (26 + z * (28 + z * (52 + z * (11 + z * (31 + z * (6 + z * (48 + z * (46 + z * (34 + z * (31 + z * (35 + z * (16 + z * (11 + z * ((-8) + z * 8))))))))))))))))))))))))))))))))))))))


def pow20_40 {R : Type*} [CommRing R] (z : R) : R := (18 + z * (6 + z * (10 + z * (31 + z * (23 + z * (22 + z * (37 + z * (24 + z * (39 + z * (34 + z * (20 + z * (35 + z * (28 + z * (24 + z * (31 + z * (17 + z * (37 + z * (1 + z * (16 + z * 1)))))))))))))))))))

def pow20_40_q {R : Type*} [CommRing R] (z : R) : R := (16 + z * (8 + z * (33 + z * (25 + z * (21 + z * (33 + z * (11 + z * (4 + z * (18 + z * (36 + z * (32 + z * (26 + z * (23 + z * (11 + z * (27 + z * (10 + z * (38 + z * (38 + z * 39))))))))))))))))))

def pow20_40_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-9) + z * ((-2) + z * ((-16) + z * ((-8) + z * ((-11) + z * ((-18) + z * ((-5) + z * ((-3) + z * (33 + z * (22 + z * (37 + z * (61 + z * (33 + z * (39 + z * (47 + z * (99 + z * (55 + z * (78 + z * (97 + z * (65 + z * (80 + z * (80 + z * (103 + z * (99 + z * (96 + z * (104 + z * (96 + z * (85 + z * (34 + z * (37 + z * (28 + z * (23 + z * (32 + z * ((-9) + z * (20 + z * (1 + z * (7 + z * ((-8) + z * 2))))))))))))))))))))))))))))))))))))))

def pow20_41_q {R : Type*} [CommRing R] (z : R) : R := (24 + z * (10 + z * (37 + z * (11 + z * (21 + z * (10 + z * (28 + z * (30 + z * (21 + z * (40 + z * (21 + z * (40 + z * (0 + z * (18 + z * (18 + z * (35 + z * (33 + z * (13 + z * 3))))))))))))))))))

def pow20_41_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-18) + z * ((-11) + z * ((-36) + z * ((-16) + z * ((-44) + z * (14 + z * ((-32) + z * ((-16) + z * (2 + z * ((-32) + z * (8 + z * ((-25) + z * (26 + z * (15 + z * (43 + z * ((-8) + z * (24 + z * ((-10) + z * (11 + z * (16 + z * (22 + z * (25 + z * (11 + z * (6 + z * ((-1) + z * ((-26) + z * ((-25) + z * ((-24) + z * ((-17) + z * ((-19) + z * ((-30) + z * ((-40) + z * ((-29) + z * ((-43) + z * ((-25) + z * ((-28) + z * ((-6) + z * ((-1) + z * 0))))))))))))))))))))))))))))))))))))))

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

section
noncomputable section
open Polynomial
namespace DimensionTen.Mod41

section Field
variable (k : Type*) [Field k] [CharP k 41]



theorem irreducible_degree_twenty {k : Type*} [Field k] [Finite k]
    (f : k[X]) (hd : f.natDegree = 20)
    (h20 : f ∣ X ^ (Nat.card k) ^ 20 - X)
    (h4 : IsCoprime f (X ^ (Nat.card k) ^ 4 - X))
    (h10 : IsCoprime f (X ^ (Nat.card k) ^ 10 - X)) : Irreducible f := by
  have hf : f ≠ 0 := by intro h; simp [h] at hd
  obtain ⟨g, hig, hgf⟩ := exists_irreducible_of_natDegree_pos (f := f) (by omega)
  have hdiv := hig.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X (dvd_trans hgf h20)
  have hle : g.natDegree ≤ 20 := hd ▸ natDegree_le_of_dvd hgf hf
  have hgd : g.natDegree = 20 := by
    by_contra hne
    have hc : ∀ d : Fin 21, d.val ∣ 20 → d.val ≠ 20 → d.val ∣ 4 ∨ d.val ∣ 10 := by
      decide
    rcases hc ⟨g.natDegree, by omega⟩ hdiv hne with h | h
    · exact hig.not_isUnit (h4.isUnit_of_dvd' hgf
        (hig.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp h))
    · exact hig.not_isUnit (h10.isUnit_of_dvd' hgf
        (hig.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp h))
  exact (associated_of_dvd_of_natDegree_le hgf hf (by omega)).irreducible_iff.mp hig


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
def W0 : Fin 20 → ℤ :=
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def W3 : Fin 20 → ℤ :=
  ![145204575748123705650598860122042297964140180806502873813425954437770925496552439336297911807152000, 0, 0, -5795987267995200387519610739842401541571946151711224626711871647496259731254938162887059799624000, 0, 0, 0, 0, 0, -4488146169139044100856485459443528548465534037069137957418469548310173104736923040124281628896000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 553886212721019589139236596321065222674818042004315535591884873070406855664319748868328235576000]

def W10 : Fin 20 → ℤ :=
  ![2936184657948960899194025333480301515549193240915920839216577223145985288485787223708638107124855634431840186123439343964409461638678351668536004291025670770115170038115314993325422057547131724807360450332756488750954038448128386649211591456961868865554183691403789298331385852833963160107894080690956486702458880000000000, -18761811967677122345833897205876358349184547160865022482076301380944873150875594035757370363264766202189973137768050818314479478018147233610141285883920417407297612085761334614069487472340268879717879533116310442219552299007287374942962791171407303323090533816310511759683399174311471491460829506946462759610480640000000000, -14238741835978483621754925860980654063120156751195405038006152341097468305383572310400147453204963938776446829224542980146828585024535432863534044156181838357664569579597603392619227967033602911069070883249068832462966174354965690429427698840054973929299614607538430912112675231835233890352997554257197317454008320000000000, -40143652577413347673802226746351997230352816062070610523888799609792090729350958382885114667924929513485831139985052809838347407621996215268664927208430167256040210864740539251276803817370114344866447212239901955436475015013537056421311556477169901638596277126432835916314112163130926952882987708284598399404236800000000000, -22376372984863934537770278124471961354780835196775090957438899865809142201808814921006301867671970696887986395046521286066691550277736284467635967215089838098292649551160368104193814689488292771454691772242501220290761333459239761272175345345014525450319310917776275765739451612443208353699566462641567417358771200000000000, -50662555202548479288370990737582326510532009348835174150184002452469571579853568044213200932656903226332522502090265826613764497879867387429520834595388550285620347144603229887636496792957793770116619507744515071639744475825155830059779374952966068175680906035664999040174691567720550591211799939260501582105077760000000000, 2981020442040240541196907155860676051377788037016351784336427282079294600228787722631027441093151721306165155487064111392747793099369239431150248512270681706709611406523867006571548113089894899321150707898861127001595431054977556740680463664041417642965055106436860143919916045202140284474804989005635773510850560000000000, 11614912491234909118271707728991306303015466533496036650299158869277941022074496363559240240728704363979108773076666887450014466419939815585159307403987541087078603113594119025917150578948895149329234188882724597605531303554003472461505585293523153361441651001413949692886230611079060505241183304088333619411025920000000000, 89616489596765940768467690725274313047385525769685132564169162856162596932407789261485830619862392671932655284132879003171935826245239804968978583436782832716238038805502978102451863936699677167000988219401228218100294524406774294695173009980856397625884059181608885153310839347820649709942696367335625409722716160000000000, 46667177192065940665871617885653273641783087322919121130276345914392942712622257303862766089650566408484804222789257640873169038910730662109748019841759663300464969924526592986046944493029133746320894681403907303114518539343115580285250438754192904777574837993159534091740265736366298647638904537859915443095255040000000000, -4863537950651788152678818779083426160708792682097383317661448755482547188390608643090703515642678155292473044272075085694308963833187076729365652001558224301596689328305809600500207990876140955545786147033675790253893480814288003100093592389047261166669613536844079624566509740783148211097346964148816367667279360000000000, 9444028613832463058958250897994001503511476138547253871588695062458486743226648153964495735608602147853776064720323523981822483179492163074416200194748424592756845015320825031105548011573752237407732961472020403678273181317974205428897599523598987873798859892047166766880493563518919515964060734565828251563939840000000000, 36256698382130871412785359463608279321846509544575709041818018200640860683505988505298253108657344191306621721143105768896782521242759944062349820228337589384926741416358909303430113524367157389344408009286880193370169455213246704680217425896095680849378340619574782085982406774061247563661025305062817843834393600000000000, 4837872954955750265723303105726731214445993238339332106955591765687368935077973059356333857691415158026225278793040316151534054535480833243500915123227472233031490387789533886041925570073859217003498459229878680849065950602004476982139443844712430125655792890519675939799440372328538706200948523935728692458536960000000000, 41885856706842111628753835930350052224693407864910790456079219305900229239205223198349379246010696228645805281900508073549709890084251404754213576865523746799453611296510628475950596495818185676299454519299978734340280018962563379888725464322826409004085087668897873877600531060325172234502803937504282325020917760000000000, 100321103624105247714086736590862041926374390791032128832834983283969447753945449240248265908811644937107489604050686604063287759839260743082868676024111358995296838938250524890391781548633213707128433897921515499001004429405623144217562158268932198798356726599906151586838583581195679017297372281231547229130629120000000000, -37115736360492670084562642948384725480599790248883417396881134106071750012196290497149151420292283861965649702015734769393944332257519876585606519025400587303646904818649828144220314739846109135634679541878081160112490976163480142026658864437488023686690949498975839901054681133111609116926881706153587046886502400000000000, 37202773041734379395035372682518569935300566794833947402623404621722284660957612250211082086601567022260808319947889038309574819883298207881237504280312396471900342574152643145091248268802599146798868804470696127416312773982804714599005378770903655747594539071239103870991715584024693332719553879085029013325224960000000000, -102070226924504096885002859307224316991550690795023219666855305723241562488249360819282768398165898368806833408388001626827564307465446470042058661459885239897869248709055044879472810739717941234045679255688353280001487829114328621725206289564138606562306739305155518677880023170181812235015936573487138715168491520000000000, -23344274443648802507670669273369023012326346174037550951128775184582470557231129321388994141065921944623089605001023644638003823883947814503937451691706075926857602979284651813369829844036020438648065904503172012378540483033201542518804967841754857220208994874137093675062284931311975370457621107113750444390860800000000000]

def W11 : Fin 20 → ℤ :=
  ![2787751283815326153172956270126456134339904049961158171927118494057889141680413053833393366969360097725551327011686078246539505344245602025322298443820435800603969142106560894223322968282936924095088121809919883724660645028975924633509196552522420722659904757348167155095132805580190452637579296507126809035092535913530329901874596817154063155200000000000, 1662835853026375739836789763133777092613578424213646531136901898981729159890027686720991380474700475752794316794243099990706612992290200996509732514042551096486588537067665747235974825573423613930704245857234820843415352961038308878559313761008962464977615950874463502912929001807307611942272206233283097918094986090229004488626710154259251404800000000000, 1560799856984930092089346578717440767216742226059721376568415412994415174017721008161545905095615694976871574634801587297802189652672911268506806221926643712842603632025022339465247878186107328544842198375928723266726074573114475944441065677262290542011130294949038506676507161123989575072782476980573931631893223840423903500638752363908012236800000000000, -1867597553150855118656436126988041086119454201043562918173077560420257296199346289570393057615076856386136657017372234274327747303782827596884691509361141903622069475762550959883737821865625560672825956192967074755025571949373945229618891643647393034833500028323204587700802047389506783288019276436953921112819759721858338958412018690321681612800000000000, 2069548577999659099027659521197033630406099779676265127445699935695805190896856404878392225036201900080502510623805509873114204938844748112205553524598035334133838166097221793494003460127777547975288572139186617797191451391481918613357855075483429406144093511258455611423678195652640441882953638343535088845075450136839064029147198588054845747200000000000, 4485862898428941287102666495778141733397314718942423758085654397389155893771257800404928537537467337024457695981007184164000246487723463765881620780734699647450123634993738101437583825229537129968183279738911207076457567315278516185481669259970488709424547382879269907663409307842358809915478440777162705170225290821244191019730325627050482790400000000000, 182622841508238964511391193166720242445358529516193323671058183373895039967358502492998439090405658783304005331219846497692734299782289963909100031528831474508659464868420447696761417357585869231975564966036733333552832567204753012007472587873321751510530813326555664171519026204570761680419087163091502042347931988282698342948532963916682854400000000000, -2726604660188271502914900270170877001957012545200335156940753888674021131572851215741398178087116931856300391898232699195339158003586534478438556514470282568789295291427282595271938323712238434379935002007432771951804853718089860926175793713569722644806346000524460157063562315513051490028093967320080967015055643181810951849930037725344525209600000000000, -7812093414362046643678581453477794608574869995421782574921717869993426025106820898971178301318301186477574765910170154875326351419711864734723139852196981701121342524668299449392983985854130788280171315101501302846032242017906468711540822956533931779574160044087393138662563987464292936445528253111639224995344462538149107330996466798973146521600000000000, -2729624816451141478457649944555171045314884108253436740138154944892125822983524235538636808824929687806745655212169886845357757439604344437024285823397560032513418422825585917965888574197035486217501590154904321243727043947434136493934476336431702831117964240359421549412854799989981779172625530859769458383960885406015536849422863382029403136000000000000, 7436355610674300463548674632245389187504544428876973892921749605157130933846105569643424972833004754379788742959631286742785194061927654426535556081099722703270075735336560651768175049029203719578184869156861052444211471963740165503873007210863410971558592701283573672147909051831478185237675038179657877680640505940957291461997675460307200000000000000, -1432116646926411734365544014732726118878378436108388709881239644531549553712093996967245054278463068533021019807117299277044821081524088132462674094209019693405177682740675696534019095224576347537865482520715748258462423399961428667570124604997544346802905843866137905487954399355029357771158327764093895753375068349679273152953467191614710937600000000000, -3368706240660659591177213452175723329630133571140567350288649259285418692307594924024376515593765235040594632410557654861639224280248125797237430287012700112191146371744322874853756481305233228104709793760098703119595745316385629425751658784319875384626521397703049267914442159573811433739862825067106182467745515074701523822967083987293643776000000000000, -746532137355505267075689858715849947619769154917039634173514075219573795742442718166493149048666948706410721182037549253025564825262176004921349404743563029766196598654276547503308507507758615793153328982369294369669217204316084034265949033119071823318565381849555549179021647639591437557115876575357350061318346540010064277645770400774691225600000000000, -3535286839406275623420479714745805908448863801592429278363972546133068390513952022003492654147600820419143030220289926781875348299850912382040970980085804142701264079898477784695891853686707435789470139467414416809211061005862619765481835306008165863669753476472134901377287365647250399823710295348010111863262797137913410465084448719987396249600000000000, -8428971522502393187959046878914273762761478432313880207333359083549408361033941082571480285053807322399070930186117791234605363135728701585996048096411044596685052562244981608682212072253981544403529734660592625410745944454321485330435301104646806116216521419454519478018298453393074954418427093611202245410625915844740452812937627764496207667200000000000, 1235322462394044382352741537862936755407695235797587341516625475087858052749384256906399527448437471957691616638545138734372686585981638483363114932970268010060327561878405694447519068501120357832398570218534453213056663867214109720195201678807430868826909401265271300091351239554439727010414724974690063293695357380000540210901105902517946777600000000000, -296573779928443006716605415107366247693343257607029751915814331614293714327503407479454246155633142974297912683346756059949930286526777880165872289103818405342412597331234506189574864552428891948321186588281503230679668313039329109650103073514902882463979598678371639166399319010514135035893419258444004389553067566371994501415072880053675724800000000000, 8246341073661912134235638811020648184086416036797164960724183311655218993347044753628770401782584698161129014594921309372134226694814659556943350356151147914816488264824480118234859536220376660800284039482711811101292897379840571826077800658308717127527749420476446801205228698595177540184581209152003429420811712556055844843474958883952932454400000000000, 3643616362473291340139858378780259113501076252645199129492295506882675917145313689016466963441994274932857023887905182890003247347650278022458865050256264092194525597988128237224606309117478221289300372598145568772177252578509285680778036694799633429573358550444061845901560920654404299887596081744894263278505408666112097393947902680424079155200000000000]

def W12 : Fin 20 → ℤ :=
  ![-167603159816123523557602427951647958721144400556041944970104462239510064527218962446411883566680929138205106197512143501298475476921261031681900575432205904440267600231130466419857107852547167414566896537079346113721020516907125690038667844754489592520726826935702931997410682171982503449448868424704069062239799738506006461304193971715373691759935654448245305553984051572736000000000000, -75716367506804246143579473408705403629491490663550650698832048677090696678146426126542452936937537977971757423397365226222162598910660802112581581101646149845795362919978501316020084362964110089191183204816985086487745955532600377575717648108498254701931918620718026267349303831392300930425803515998498036433096718983264289444130210127047650801732816840001160087985243975680000000000000, -90299988907102112555264019253677223826134014883925195628837449500604183144516543540246257612281608183994560033882772318159077840613903797286154822633746420794915717755970936302026488073361887504884167746385206294117863317173451807152195294414409982499371927991407448283601119682361802473451101264250047547699946203789209248369990477739147245312155881641730552376653373132800000000000000, 205309403859821356483381766921905688886526628296245388060294093517210224177181696553809513437784596369116828837885638783380507991708673039356926980293341573738137974712717745109855016795498362505450041863243328777915549751992180301737575330891634622927371699571424414979146625253089329737638000653248461028898460253885987146108381542794580831908572300743333092762032213766144000000000000, -107784096928938967144327220748704038445080784504909224955212266130786112520848112608595180356837501844572843105437112118590389844720610898285358794247916629597264278113511705698358211906768127703183129027920843831562933016846104385472202611479859308872651024399521785885104468542725890719712605150609895772271508109866061710111224687202298457410687753853878061567362524047360000000000000, -234359556578610145406921784861417475642320023733603923264331770115282672173791708572156177255671679656866850799398185223086633144688461735147506612876541701006508464132963619341037227456800233275240650773916247349347823440230985445481105623665903193160211230738082075800317254073910522791039943176983507864405013791472227909558859904406157567980570596518287172295469051537408000000000000, -25753928261129257051104657754639988870224895699481040861740317701004672535134157386125307143605663240802565283438128850379568299320300099665362405969410708088066327799021804056989304394541406100750535222319662451295492339926832882410883102387745289574780378206559500334075440493758618873620991197220718482496282897887199516069871143649198571018400137910570367653417413324800000000000000, 159284887445376351260545125173314709111261568766969961295336065777009990309489781809709120449097591860497646221024514939470787588391975494917577233803047160535118812784274127425451195882686309330366648829465572854751755825432559785131202389597767232979143424504354852321842609884367724340232424854710333588821338552466418034231549427351619884588554236019007068396872331622400000000000000, 379870456582410811184816072298086171051673008184329954597523292575214196258363273003501582916751067750177066395453531394015541454856604071197425292646646904118795664521735452394452946110219340282122591882878390993566174777120172739977407269044220618943278511689174388315002006107710008109968289715838057417509939095121973711149079075934989844058877307632851266842199230414848000000000000, 90029681058358851027003767181484929401053935896054741979697544716273994319622159130409219313461199733666714498647048720195898027642668415752264452533184019559528006078742446043424349139705755794606602437873806960965299297570613234032805507473569415934553407641224714206371507306214169512310428932363565879467506580854973319123385279419426099991901294243128020934324412866560000000000000, 13443314444458602052242723390503786590717477639876254317957963235619837796836663498916319457441889472655106716235670105462851495376095028021265228050670266687557557258544484876476691850871713609552868944325995640088617739739186626117590734341268788285910548848603872373182973441567460260907983301556595422141519173952883964676336994860199258424274185475145305740832195946496000000000000, 98199361093950525616638070541350357679468867829806053678142547282402562924168217851417998995519762727967024047247377555229771595693568377979785886761701824450937769331423194834858272409804886258752478886435164260822572732811842376017939139659399746273411057471559124353985490140825868079464957230635016891532950296113269555835548501660641049457094213418132045140480861012992000000000000, 188467875936685673590460619058713276900219771719473585255344783310378423287576910284414855444883648772040147620281968628150063931686838627998409055807358076034454431617471236107146924550394457824170099408793834900362115130086861587762429238722077763956134012575659920755377075514381716694274578429489611522574577599183687702340047633715402424141427856158750689474451828774912000000000000, 53551127833205661607150783137349077261542787263093884382127813616974160600264042420975635820807302642183069571718554004799769318875541903586053897899618837835484776874972769999740976441854842017267597431993301054766455918220572428682144806300259482773913928668221760414877692070272258469404223718231971315163838209985001307247331922587966068717417088663274399005920686116864000000000000, 180139951889095930996889975805338914847085428896620008346086446166257824332383529649927722170854972073688019457170867501841339253501376306871326958422185954719189544805587947002309907859875841936212584418321447270466336972603801987703914746277158517227219943619188073106608720731858402945892232713330614229887087716093265920613350413931262768062220766015863854455360911526912000000000000, 437036097490668536742194773978134710101261856025321734154593668007116605031203599951098641248089803794500007272090133150156240763540006833892500848495454056395550030065986563854747151780176228441068034251965960999767724668475577457379268874479207060215288944116687548440269117912154254700014779684992566972668098236229224249187905293001735361779758057133199211084100667777024000000000000, 11996686352917533978200014890741966057613820454712452873947995631253689060241014811261571639754509013301288767208425452928011025030250052901584168102805478383590946302358488699509117524554036586740676930824644664181904108665479408748237181590227746901548540847599995848545946218770754491238816980780753826036544152401938648560352998462249466073658627301836540735007682187264000000000000, -48137127017288304047973260445859937290604516650131939341192842741631958534046872677060716511968606116079698619272894829819739950338296565481196261123905422595352131624639393771431277875640335015832129908708327851920025666670582595652505976852964770395973012670483295352054346542967519466182067449467118476986593388520900900932618951556758690469054308990235154431381015148544000000000000, -374075724638319026095363765904136901980058985673915105151782131819446657283156080251977214847780466437527692532093743657992857656962412921845853244654396640376062927419207532654392574316328755288969697540916823628579894870086695707823550657921301840237584501745222911466633267465433255842538618755830359978197685834860171800533976590971501635276230463222739462698949451112448000000000000, -214499108465008306643434441633451596228784709115822938234322323955618557625658009709341181851551907700053664252364910711594117820795420962047025329024118306737712023949214236741171529527259295644321362690776888306820514646374309254397328316303871494076776796016313322218183134652875041015128045559455429835869283382992766615650760944012863538254347869786526120188700747161600000000000000]

def W20 : Fin 20 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

lemma W20_eq : W20 = 0 := by decide +kernel

end DimensionTen.Border

end
end

end OAI
end


