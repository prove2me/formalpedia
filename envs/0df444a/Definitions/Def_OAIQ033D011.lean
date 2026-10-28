-- Prove2me | Definitions.Def_OAIQ033D011
-- name    : OAIQ033D011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T01:52:45.169868+00:00
-- url     : https://prove2.me/theorems/7e0fe6e9-05ac-40af-bc6b-822745aa1b62
-- title:
--   Definitions bundle OAIQ033D011 of the split of OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DimensionTen.main_pair`, carved from OpenAI's openai/math development (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 240 declarations of OpenAI's Lean: 3 definitions and 237 theorems. The definitions and types are `OAI.DimensionTen.Border.K`, `OAI.DimensionTen.Mod41.pow20_41`, `OAI.DimensionTen.Mod41.u20`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Quantum/DimensionTen, in whole or in part: [`Quantum_DimensionTen_Annihilator`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Annihilator.lean), [`Quantum_DimensionTen_BorderData`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/BorderData.lean), [`Quantum_DimensionTen_GaloisField`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/GaloisField.lean), [`Quantum_DimensionTen_IntegerPolynomials`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/IntegerPolynomials.lean), [`Quantum_DimensionTen_Mod41Powers07`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod41Powers07.lean), [`Quantum_DimensionTen_Mod41Powers08`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod41Powers08.lean), [`Quantum_DimensionTen_Mod41Powers09`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod41Powers09.lean), [`Quantum_DimensionTen_Mod41Powers10`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod41Powers10.lean), [`Quantum_DimensionTen_PolynomialData`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/PolynomialData.lean).
--
--   **Imports.** It imports the bundles `OAIQ033D000`, `OAIQ033D001`, `OAIQ033D002` and `OAIQ033D003` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ033D014`.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Quantum/DimensionTen at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ033D000
import Definitions.Def_OAIQ033D001
import Definitions.Def_OAIQ033D002
import Definitions.Def_OAIQ033D003

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod41Powers07
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41

theorem pow14_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u13 z * u13 z = pow14_2_q z * f z + pow14_2 z + (41 : R) * pow14_2_mul_t z := by
  simp only [u13, pow14_2_q, f, pow14_2, pow14_2_mul_t]
  simp only [pow13_41]
  ring

theorem pow14_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u13 z * u13 z = pow14_2_q z * f z + pow14_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow14_2_mul_integer z


theorem pow14_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u13 z * u13 z = pow14_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_2_mul z


theorem pow14_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u13 z ^ 2 = pow14_2 z := by
  calc
    _ = u13 z ^ 1 * u13 z ^ 1 := by ring
    _ = u13 z * u13 z := by simp only [pow_one]
    _ = _ := pow14_2_root z hz


theorem pow14_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_2 z * pow14_2 z = pow14_4_q z * f z + pow14_4 z + (41 : R) * pow14_4_mul_t z := by
  simp only [pow14_2, pow14_4_q, f, pow14_4, pow14_4_mul_t]
  
  ring

theorem pow14_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow14_2 z * pow14_2 z = pow14_4_q z * f z + pow14_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow14_4_mul_integer z


theorem pow14_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow14_2 z * pow14_2 z = pow14_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_4_mul z


theorem pow14_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u13 z ^ 4 = pow14_4 z := by
  calc
    _ = u13 z ^ 2 * u13 z ^ 2 := by ring
    _ = pow14_2 z * pow14_2 z := by rw [pow14_2_pow z hz]
    _ = _ := pow14_4_root z hz


theorem pow14_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_4 z * u13 z = pow14_5_q z * f z + pow14_5 z + (41 : R) * pow14_5_mul_t z := by
  simp only [pow14_4, u13, pow14_5_q, f, pow14_5, pow14_5_mul_t]
  simp only [pow13_41]
  ring

theorem pow14_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow14_4 z * u13 z = pow14_5_q z * f z + pow14_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow14_5_mul_integer z


theorem pow14_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow14_4 z * u13 z = pow14_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_5_mul z


theorem pow14_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u13 z ^ 5 = pow14_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow14_4_pow z hz]
  exact pow14_5_root z hz


theorem pow14_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_5 z * pow14_5 z = pow14_10_q z * f z + pow14_10 z + (41 : R) * pow14_10_mul_t z := by
  simp only [pow14_5, pow14_10_q, f, pow14_10, pow14_10_mul_t]
  
  ring

theorem pow14_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow14_5 z * pow14_5 z = pow14_10_q z * f z + pow14_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow14_10_mul_integer z


theorem pow14_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow14_5 z * pow14_5 z = pow14_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_10_mul z


theorem pow14_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u13 z ^ 10 = pow14_10 z := by
  calc
    _ = u13 z ^ 5 * u13 z ^ 5 := by ring
    _ = pow14_5 z * pow14_5 z := by rw [pow14_5_pow z hz]
    _ = _ := pow14_10_root z hz


theorem pow14_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_10 z * pow14_10 z = pow14_20_q z * f z + pow14_20 z + (41 : R) * pow14_20_mul_t z := by
  simp only [pow14_10, pow14_20_q, f, pow14_20, pow14_20_mul_t]
  
  ring

theorem pow14_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow14_10 z * pow14_10 z = pow14_20_q z * f z + pow14_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow14_20_mul_integer z


theorem pow14_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow14_10 z * pow14_10 z = pow14_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_20_mul z


theorem pow14_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u13 z ^ 20 = pow14_20 z := by
  calc
    _ = u13 z ^ 10 * u13 z ^ 10 := by ring
    _ = pow14_10 z * pow14_10 z := by rw [pow14_10_pow z hz]
    _ = _ := pow14_20_root z hz


theorem pow14_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_20 z * pow14_20 z = pow14_40_q z * f z + pow14_40 z + (41 : R) * pow14_40_mul_t z := by
  simp only [pow14_20, pow14_40_q, f, pow14_40, pow14_40_mul_t]
  
  ring

theorem pow14_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow14_20 z * pow14_20 z = pow14_40_q z * f z + pow14_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow14_40_mul_integer z


theorem pow14_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow14_20 z * pow14_20 z = pow14_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_40_mul z


theorem pow14_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u13 z ^ 40 = pow14_40 z := by
  calc
    _ = u13 z ^ 20 * u13 z ^ 20 := by ring
    _ = pow14_20 z * pow14_20 z := by rw [pow14_20_pow z hz]
    _ = _ := pow14_40_root z hz


theorem pow14_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow14_40 z * u13 z = pow14_41_q z * f z + pow14_41 z + (41 : R) * pow14_41_mul_t z := by
  simp only [pow14_40, u13, pow14_41_q, f, pow14_41, pow14_41_mul_t]
  simp only [pow13_41]
  ring

theorem pow14_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow14_40 z * u13 z = pow14_41_q z * f z + pow14_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow14_41_mul_integer z


theorem pow14_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow14_40 z * u13 z = pow14_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow14_41_mul z


theorem pow14_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u13 z ^ 41 = pow14_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow14_40_pow z hz]
  exact pow14_41_root z hz


end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod41Powers08
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41

theorem pow15_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u14 z * u14 z = pow15_2_q z * f z + pow15_2 z + (41 : R) * pow15_2_mul_t z := by
  simp only [u14, pow15_2_q, f, pow15_2, pow15_2_mul_t]
  simp only [pow14_41]
  ring

theorem pow15_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u14 z * u14 z = pow15_2_q z * f z + pow15_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow15_2_mul_integer z


theorem pow15_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u14 z * u14 z = pow15_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_2_mul z


theorem pow15_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u14 z ^ 2 = pow15_2 z := by
  calc
    _ = u14 z ^ 1 * u14 z ^ 1 := by ring
    _ = u14 z * u14 z := by simp only [pow_one]
    _ = _ := pow15_2_root z hz


theorem pow15_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_4 z * u14 z = pow15_5_q z * f z + pow15_5 z + (41 : R) * pow15_5_mul_t z := by
  simp only [pow15_4, u14, pow15_5_q, f, pow15_5, pow15_5_mul_t]
  simp only [pow14_41]
  ring

theorem pow15_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow15_4 z * u14 z = pow15_5_q z * f z + pow15_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow15_5_mul_integer z


theorem pow15_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow15_4 z * u14 z = pow15_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_5_mul z


theorem pow15_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_5 z * pow15_5 z = pow15_10_q z * f z + pow15_10 z + (41 : R) * pow15_10_mul_t z := by
  simp only [pow15_5, pow15_10_q, f, pow15_10, pow15_10_mul_t]
  
  ring

theorem pow15_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow15_5 z * pow15_5 z = pow15_10_q z * f z + pow15_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow15_10_mul_integer z


theorem pow15_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow15_5 z * pow15_5 z = pow15_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_10_mul z


theorem pow15_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_10 z * pow15_10 z = pow15_20_q z * f z + pow15_20 z + (41 : R) * pow15_20_mul_t z := by
  simp only [pow15_10, pow15_20_q, f, pow15_20, pow15_20_mul_t]
  
  ring

theorem pow15_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow15_10 z * pow15_10 z = pow15_20_q z * f z + pow15_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow15_20_mul_integer z


theorem pow15_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow15_10 z * pow15_10 z = pow15_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_20_mul z


theorem pow15_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_20 z * pow15_20 z = pow15_40_q z * f z + pow15_40 z + (41 : R) * pow15_40_mul_t z := by
  simp only [pow15_20, pow15_40_q, f, pow15_40, pow15_40_mul_t]
  
  ring

theorem pow15_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow15_20 z * pow15_20 z = pow15_40_q z * f z + pow15_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow15_40_mul_integer z


theorem pow15_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow15_20 z * pow15_20 z = pow15_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_40_mul z


theorem pow15_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_40 z * u14 z = pow15_41_q z * f z + pow15_41 z + (41 : R) * pow15_41_mul_t z := by
  simp only [pow15_40, u14, pow15_41_q, f, pow15_41, pow15_41_mul_t]
  simp only [pow14_41]
  ring

theorem pow15_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow15_40 z * u14 z = pow15_41_q z * f z + pow15_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow15_41_mul_integer z


theorem pow15_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow15_40 z * u14 z = pow15_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_41_mul z


theorem pow16_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u15 z * u15 z = pow16_2_q z * f z + pow16_2 z + (41 : R) * pow16_2_mul_t z := by
  simp only [u15, pow16_2_q, f, pow16_2, pow16_2_mul_t]
  simp only [pow15_41]
  ring

theorem pow16_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u15 z * u15 z = pow16_2_q z * f z + pow16_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow16_2_mul_integer z


theorem pow16_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u15 z * u15 z = pow16_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_2_mul z


theorem pow16_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u15 z ^ 2 = pow16_2 z := by
  calc
    _ = u15 z ^ 1 * u15 z ^ 1 := by ring
    _ = u15 z * u15 z := by simp only [pow_one]
    _ = _ := pow16_2_root z hz


theorem pow16_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_2 z * pow16_2 z = pow16_4_q z * f z + pow16_4 z + (41 : R) * pow16_4_mul_t z := by
  simp only [pow16_2, pow16_4_q, f, pow16_4, pow16_4_mul_t]
  
  ring

theorem pow16_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow16_2 z * pow16_2 z = pow16_4_q z * f z + pow16_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow16_4_mul_integer z


theorem pow16_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow16_2 z * pow16_2 z = pow16_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_4_mul z


theorem pow16_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u15 z ^ 4 = pow16_4 z := by
  calc
    _ = u15 z ^ 2 * u15 z ^ 2 := by ring
    _ = pow16_2 z * pow16_2 z := by rw [pow16_2_pow z hz]
    _ = _ := pow16_4_root z hz


theorem pow16_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_4 z * u15 z = pow16_5_q z * f z + pow16_5 z + (41 : R) * pow16_5_mul_t z := by
  simp only [pow16_4, u15, pow16_5_q, f, pow16_5, pow16_5_mul_t]
  simp only [pow15_41]
  ring

theorem pow16_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow16_4 z * u15 z = pow16_5_q z * f z + pow16_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow16_5_mul_integer z


theorem pow16_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow16_4 z * u15 z = pow16_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_5_mul z


theorem pow16_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u15 z ^ 5 = pow16_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow16_4_pow z hz]
  exact pow16_5_root z hz


theorem pow16_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_5 z * pow16_5 z = pow16_10_q z * f z + pow16_10 z + (41 : R) * pow16_10_mul_t z := by
  simp only [pow16_5, pow16_10_q, f, pow16_10, pow16_10_mul_t]
  
  ring

theorem pow16_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow16_5 z * pow16_5 z = pow16_10_q z * f z + pow16_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow16_10_mul_integer z


theorem pow16_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow16_5 z * pow16_5 z = pow16_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_10_mul z


theorem pow16_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u15 z ^ 10 = pow16_10 z := by
  calc
    _ = u15 z ^ 5 * u15 z ^ 5 := by ring
    _ = pow16_5 z * pow16_5 z := by rw [pow16_5_pow z hz]
    _ = _ := pow16_10_root z hz


theorem pow16_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_10 z * pow16_10 z = pow16_20_q z * f z + pow16_20 z + (41 : R) * pow16_20_mul_t z := by
  simp only [pow16_10, pow16_20_q, f, pow16_20, pow16_20_mul_t]
  
  ring

theorem pow16_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow16_10 z * pow16_10 z = pow16_20_q z * f z + pow16_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow16_20_mul_integer z


theorem pow16_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow16_10 z * pow16_10 z = pow16_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_20_mul z


theorem pow16_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u15 z ^ 20 = pow16_20 z := by
  calc
    _ = u15 z ^ 10 * u15 z ^ 10 := by ring
    _ = pow16_10 z * pow16_10 z := by rw [pow16_10_pow z hz]
    _ = _ := pow16_20_root z hz


theorem pow16_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_20 z * pow16_20 z = pow16_40_q z * f z + pow16_40 z + (41 : R) * pow16_40_mul_t z := by
  simp only [pow16_20, pow16_40_q, f, pow16_40, pow16_40_mul_t]
  
  ring

theorem pow16_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow16_20 z * pow16_20 z = pow16_40_q z * f z + pow16_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow16_40_mul_integer z


theorem pow16_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow16_20 z * pow16_20 z = pow16_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_40_mul z


theorem pow16_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u15 z ^ 40 = pow16_40 z := by
  calc
    _ = u15 z ^ 20 * u15 z ^ 20 := by ring
    _ = pow16_20 z * pow16_20 z := by rw [pow16_20_pow z hz]
    _ = _ := pow16_40_root z hz


theorem pow16_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow16_40 z * u15 z = pow16_41_q z * f z + pow16_41 z + (41 : R) * pow16_41_mul_t z := by
  simp only [pow16_40, u15, pow16_41_q, f, pow16_41, pow16_41_mul_t]
  simp only [pow15_41]
  ring

theorem pow16_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow16_40 z * u15 z = pow16_41_q z * f z + pow16_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow16_41_mul_integer z


theorem pow16_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow16_40 z * u15 z = pow16_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow16_41_mul z


theorem pow16_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u15 z ^ 41 = pow16_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow16_40_pow z hz]
  exact pow16_41_root z hz


end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod41Powers09
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41

theorem pow17_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u16 z * u16 z = pow17_2_q z * f z + pow17_2 z + (41 : R) * pow17_2_mul_t z := by
  simp only [u16, pow17_2_q, f, pow17_2, pow17_2_mul_t]
  simp only [pow16_41]
  ring

theorem pow17_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u16 z * u16 z = pow17_2_q z * f z + pow17_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow17_2_mul_integer z


theorem pow17_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u16 z * u16 z = pow17_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_2_mul z


theorem pow17_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u16 z ^ 2 = pow17_2 z := by
  calc
    _ = u16 z ^ 1 * u16 z ^ 1 := by ring
    _ = u16 z * u16 z := by simp only [pow_one]
    _ = _ := pow17_2_root z hz


theorem pow17_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_2 z * pow17_2 z = pow17_4_q z * f z + pow17_4 z + (41 : R) * pow17_4_mul_t z := by
  simp only [pow17_2, pow17_4_q, f, pow17_4, pow17_4_mul_t]
  
  ring

theorem pow17_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow17_2 z * pow17_2 z = pow17_4_q z * f z + pow17_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow17_4_mul_integer z


theorem pow17_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow17_2 z * pow17_2 z = pow17_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_4_mul z


theorem pow17_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u16 z ^ 4 = pow17_4 z := by
  calc
    _ = u16 z ^ 2 * u16 z ^ 2 := by ring
    _ = pow17_2 z * pow17_2 z := by rw [pow17_2_pow z hz]
    _ = _ := pow17_4_root z hz


theorem pow17_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_4 z * u16 z = pow17_5_q z * f z + pow17_5 z + (41 : R) * pow17_5_mul_t z := by
  simp only [pow17_4, u16, pow17_5_q, f, pow17_5, pow17_5_mul_t]
  simp only [pow16_41]
  ring

theorem pow17_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow17_4 z * u16 z = pow17_5_q z * f z + pow17_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow17_5_mul_integer z


theorem pow17_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow17_4 z * u16 z = pow17_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_5_mul z


theorem pow17_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u16 z ^ 5 = pow17_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow17_4_pow z hz]
  exact pow17_5_root z hz


theorem pow17_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_5 z * pow17_5 z = pow17_10_q z * f z + pow17_10 z + (41 : R) * pow17_10_mul_t z := by
  simp only [pow17_5, pow17_10_q, f, pow17_10, pow17_10_mul_t]
  
  ring

theorem pow17_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow17_5 z * pow17_5 z = pow17_10_q z * f z + pow17_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow17_10_mul_integer z


theorem pow17_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow17_5 z * pow17_5 z = pow17_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_10_mul z


theorem pow17_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u16 z ^ 10 = pow17_10 z := by
  calc
    _ = u16 z ^ 5 * u16 z ^ 5 := by ring
    _ = pow17_5 z * pow17_5 z := by rw [pow17_5_pow z hz]
    _ = _ := pow17_10_root z hz


theorem pow17_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_10 z * pow17_10 z = pow17_20_q z * f z + pow17_20 z + (41 : R) * pow17_20_mul_t z := by
  simp only [pow17_10, pow17_20_q, f, pow17_20, pow17_20_mul_t]
  
  ring

theorem pow17_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow17_10 z * pow17_10 z = pow17_20_q z * f z + pow17_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow17_20_mul_integer z


theorem pow17_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow17_10 z * pow17_10 z = pow17_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_20_mul z


theorem pow17_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u16 z ^ 20 = pow17_20 z := by
  calc
    _ = u16 z ^ 10 * u16 z ^ 10 := by ring
    _ = pow17_10 z * pow17_10 z := by rw [pow17_10_pow z hz]
    _ = _ := pow17_20_root z hz


theorem pow17_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_20 z * pow17_20 z = pow17_40_q z * f z + pow17_40 z + (41 : R) * pow17_40_mul_t z := by
  simp only [pow17_20, pow17_40_q, f, pow17_40, pow17_40_mul_t]
  
  ring

theorem pow17_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow17_20 z * pow17_20 z = pow17_40_q z * f z + pow17_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow17_40_mul_integer z


theorem pow17_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow17_20 z * pow17_20 z = pow17_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_40_mul z


theorem pow17_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u16 z ^ 40 = pow17_40 z := by
  calc
    _ = u16 z ^ 20 * u16 z ^ 20 := by ring
    _ = pow17_20 z * pow17_20 z := by rw [pow17_20_pow z hz]
    _ = _ := pow17_40_root z hz


theorem pow17_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow17_40 z * u16 z = pow17_41_q z * f z + pow17_41 z + (41 : R) * pow17_41_mul_t z := by
  simp only [pow17_40, u16, pow17_41_q, f, pow17_41, pow17_41_mul_t]
  simp only [pow16_41]
  ring

theorem pow17_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow17_40 z * u16 z = pow17_41_q z * f z + pow17_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow17_41_mul_integer z


theorem pow17_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow17_40 z * u16 z = pow17_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow17_41_mul z


theorem pow17_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u16 z ^ 41 = pow17_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow17_40_pow z hz]
  exact pow17_41_root z hz


theorem pow18_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u17 z * u17 z = pow18_2_q z * f z + pow18_2 z + (41 : R) * pow18_2_mul_t z := by
  simp only [u17, pow18_2_q, f, pow18_2, pow18_2_mul_t]
  simp only [pow17_41]
  ring

theorem pow18_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u17 z * u17 z = pow18_2_q z * f z + pow18_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow18_2_mul_integer z


theorem pow18_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u17 z * u17 z = pow18_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_2_mul z


theorem pow18_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u17 z ^ 2 = pow18_2 z := by
  calc
    _ = u17 z ^ 1 * u17 z ^ 1 := by ring
    _ = u17 z * u17 z := by simp only [pow_one]
    _ = _ := pow18_2_root z hz


theorem pow18_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_2 z * pow18_2 z = pow18_4_q z * f z + pow18_4 z + (41 : R) * pow18_4_mul_t z := by
  simp only [pow18_2, pow18_4_q, f, pow18_4, pow18_4_mul_t]
  
  ring

theorem pow18_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow18_2 z * pow18_2 z = pow18_4_q z * f z + pow18_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow18_4_mul_integer z


theorem pow18_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow18_2 z * pow18_2 z = pow18_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_4_mul z


theorem pow18_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u17 z ^ 4 = pow18_4 z := by
  calc
    _ = u17 z ^ 2 * u17 z ^ 2 := by ring
    _ = pow18_2 z * pow18_2 z := by rw [pow18_2_pow z hz]
    _ = _ := pow18_4_root z hz


theorem pow18_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_4 z * u17 z = pow18_5_q z * f z + pow18_5 z + (41 : R) * pow18_5_mul_t z := by
  simp only [pow18_4, u17, pow18_5_q, f, pow18_5, pow18_5_mul_t]
  simp only [pow17_41]
  ring

theorem pow18_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow18_4 z * u17 z = pow18_5_q z * f z + pow18_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow18_5_mul_integer z


theorem pow18_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow18_4 z * u17 z = pow18_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_5_mul z


theorem pow18_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u17 z ^ 5 = pow18_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow18_4_pow z hz]
  exact pow18_5_root z hz


theorem pow18_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_5 z * pow18_5 z = pow18_10_q z * f z + pow18_10 z + (41 : R) * pow18_10_mul_t z := by
  simp only [pow18_5, pow18_10_q, f, pow18_10, pow18_10_mul_t]
  
  ring

theorem pow18_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow18_5 z * pow18_5 z = pow18_10_q z * f z + pow18_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow18_10_mul_integer z


theorem pow18_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow18_5 z * pow18_5 z = pow18_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_10_mul z


theorem pow18_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u17 z ^ 10 = pow18_10 z := by
  calc
    _ = u17 z ^ 5 * u17 z ^ 5 := by ring
    _ = pow18_5 z * pow18_5 z := by rw [pow18_5_pow z hz]
    _ = _ := pow18_10_root z hz


theorem pow18_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_10 z * pow18_10 z = pow18_20_q z * f z + pow18_20 z + (41 : R) * pow18_20_mul_t z := by
  simp only [pow18_10, pow18_20_q, f, pow18_20, pow18_20_mul_t]
  
  ring

theorem pow18_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow18_10 z * pow18_10 z = pow18_20_q z * f z + pow18_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow18_20_mul_integer z


theorem pow18_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow18_10 z * pow18_10 z = pow18_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_20_mul z


theorem pow18_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u17 z ^ 20 = pow18_20 z := by
  calc
    _ = u17 z ^ 10 * u17 z ^ 10 := by ring
    _ = pow18_10 z * pow18_10 z := by rw [pow18_10_pow z hz]
    _ = _ := pow18_20_root z hz


theorem pow18_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_20 z * pow18_20 z = pow18_40_q z * f z + pow18_40 z + (41 : R) * pow18_40_mul_t z := by
  simp only [pow18_20, pow18_40_q, f, pow18_40, pow18_40_mul_t]
  
  ring

theorem pow18_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow18_20 z * pow18_20 z = pow18_40_q z * f z + pow18_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow18_40_mul_integer z


theorem pow18_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow18_20 z * pow18_20 z = pow18_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_40_mul z


theorem pow18_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u17 z ^ 40 = pow18_40 z := by
  calc
    _ = u17 z ^ 20 * u17 z ^ 20 := by ring
    _ = pow18_20 z * pow18_20 z := by rw [pow18_20_pow z hz]
    _ = _ := pow18_40_root z hz


theorem pow18_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow18_40 z * u17 z = pow18_41_q z * f z + pow18_41 z + (41 : R) * pow18_41_mul_t z := by
  simp only [pow18_40, u17, pow18_41_q, f, pow18_41, pow18_41_mul_t]
  simp only [pow17_41]
  ring

theorem pow18_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow18_40 z * u17 z = pow18_41_q z * f z + pow18_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow18_41_mul_integer z


theorem pow18_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow18_40 z * u17 z = pow18_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow18_41_mul z


theorem pow18_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u17 z ^ 41 = pow18_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow18_40_pow z hz]
  exact pow18_41_root z hz


end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod41Powers10
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41

theorem pow19_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u18 z * u18 z = pow19_2_q z * f z + pow19_2 z + (41 : R) * pow19_2_mul_t z := by
  simp only [u18, pow19_2_q, f, pow19_2, pow19_2_mul_t]
  simp only [pow18_41]
  ring

theorem pow19_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u18 z * u18 z = pow19_2_q z * f z + pow19_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow19_2_mul_integer z


theorem pow19_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u18 z * u18 z = pow19_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_2_mul z


theorem pow19_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u18 z ^ 2 = pow19_2 z := by
  calc
    _ = u18 z ^ 1 * u18 z ^ 1 := by ring
    _ = u18 z * u18 z := by simp only [pow_one]
    _ = _ := pow19_2_root z hz


theorem pow19_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_2 z * pow19_2 z = pow19_4_q z * f z + pow19_4 z + (41 : R) * pow19_4_mul_t z := by
  simp only [pow19_2, pow19_4_q, f, pow19_4, pow19_4_mul_t]
  
  ring

theorem pow19_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow19_2 z * pow19_2 z = pow19_4_q z * f z + pow19_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow19_4_mul_integer z


theorem pow19_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow19_2 z * pow19_2 z = pow19_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_4_mul z


theorem pow19_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u18 z ^ 4 = pow19_4 z := by
  calc
    _ = u18 z ^ 2 * u18 z ^ 2 := by ring
    _ = pow19_2 z * pow19_2 z := by rw [pow19_2_pow z hz]
    _ = _ := pow19_4_root z hz


theorem pow19_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_4 z * u18 z = pow19_5_q z * f z + pow19_5 z + (41 : R) * pow19_5_mul_t z := by
  simp only [pow19_4, u18, pow19_5_q, f, pow19_5, pow19_5_mul_t]
  simp only [pow18_41]
  ring

theorem pow19_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow19_4 z * u18 z = pow19_5_q z * f z + pow19_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow19_5_mul_integer z


theorem pow19_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow19_4 z * u18 z = pow19_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_5_mul z


theorem pow19_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u18 z ^ 5 = pow19_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow19_4_pow z hz]
  exact pow19_5_root z hz


theorem pow19_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_5 z * pow19_5 z = pow19_10_q z * f z + pow19_10 z + (41 : R) * pow19_10_mul_t z := by
  simp only [pow19_5, pow19_10_q, f, pow19_10, pow19_10_mul_t]
  
  ring

theorem pow19_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow19_5 z * pow19_5 z = pow19_10_q z * f z + pow19_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow19_10_mul_integer z


theorem pow19_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow19_5 z * pow19_5 z = pow19_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_10_mul z


theorem pow19_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u18 z ^ 10 = pow19_10 z := by
  calc
    _ = u18 z ^ 5 * u18 z ^ 5 := by ring
    _ = pow19_5 z * pow19_5 z := by rw [pow19_5_pow z hz]
    _ = _ := pow19_10_root z hz


theorem pow19_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_10 z * pow19_10 z = pow19_20_q z * f z + pow19_20 z + (41 : R) * pow19_20_mul_t z := by
  simp only [pow19_10, pow19_20_q, f, pow19_20, pow19_20_mul_t]
  
  ring

theorem pow19_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow19_10 z * pow19_10 z = pow19_20_q z * f z + pow19_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow19_20_mul_integer z


theorem pow19_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow19_10 z * pow19_10 z = pow19_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_20_mul z


theorem pow19_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u18 z ^ 20 = pow19_20 z := by
  calc
    _ = u18 z ^ 10 * u18 z ^ 10 := by ring
    _ = pow19_10 z * pow19_10 z := by rw [pow19_10_pow z hz]
    _ = _ := pow19_20_root z hz


theorem pow19_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_20 z * pow19_20 z = pow19_40_q z * f z + pow19_40 z + (41 : R) * pow19_40_mul_t z := by
  simp only [pow19_20, pow19_40_q, f, pow19_40, pow19_40_mul_t]
  
  ring

theorem pow19_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow19_20 z * pow19_20 z = pow19_40_q z * f z + pow19_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow19_40_mul_integer z


theorem pow19_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow19_20 z * pow19_20 z = pow19_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_40_mul z


theorem pow19_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u18 z ^ 40 = pow19_40 z := by
  calc
    _ = u18 z ^ 20 * u18 z ^ 20 := by ring
    _ = pow19_20 z * pow19_20 z := by rw [pow19_20_pow z hz]
    _ = _ := pow19_40_root z hz


theorem pow19_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow19_40 z * u18 z = pow19_41_q z * f z + pow19_41 z + (41 : R) * pow19_41_mul_t z := by
  simp only [pow19_40, u18, pow19_41_q, f, pow19_41, pow19_41_mul_t]
  simp only [pow18_41]
  ring

theorem pow19_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow19_40 z * u18 z = pow19_41_q z * f z + pow19_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow19_41_mul_integer z


theorem pow19_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow19_40 z * u18 z = pow19_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow19_41_mul z


theorem pow19_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u18 z ^ 41 = pow19_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow19_40_pow z hz]
  exact pow19_41_root z hz


theorem pow20_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u19 z * u19 z = pow20_2_q z * f z + pow20_2 z + (41 : R) * pow20_2_mul_t z := by
  simp only [u19, pow20_2_q, f, pow20_2, pow20_2_mul_t]
  simp only [pow19_41]
  ring

theorem pow20_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u19 z * u19 z = pow20_2_q z * f z + pow20_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow20_2_mul_integer z


theorem pow20_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u19 z * u19 z = pow20_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow20_2_mul z


theorem pow20_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u19 z ^ 2 = pow20_2 z := by
  calc
    _ = u19 z ^ 1 * u19 z ^ 1 := by ring
    _ = u19 z * u19 z := by simp only [pow_one]
    _ = _ := pow20_2_root z hz


theorem pow20_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow20_2 z * pow20_2 z = pow20_4_q z * f z + pow20_4 z + (41 : R) * pow20_4_mul_t z := by
  simp only [pow20_2, pow20_4_q, f, pow20_4, pow20_4_mul_t]
  
  ring

theorem pow20_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow20_2 z * pow20_2 z = pow20_4_q z * f z + pow20_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow20_4_mul_integer z


theorem pow20_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow20_2 z * pow20_2 z = pow20_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow20_4_mul z


theorem pow20_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u19 z ^ 4 = pow20_4 z := by
  calc
    _ = u19 z ^ 2 * u19 z ^ 2 := by ring
    _ = pow20_2 z * pow20_2 z := by rw [pow20_2_pow z hz]
    _ = _ := pow20_4_root z hz


theorem pow20_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow20_4 z * u19 z = pow20_5_q z * f z + pow20_5 z + (41 : R) * pow20_5_mul_t z := by
  simp only [pow20_4, u19, pow20_5_q, f, pow20_5, pow20_5_mul_t]
  simp only [pow19_41]
  ring

theorem pow20_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow20_4 z * u19 z = pow20_5_q z * f z + pow20_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow20_5_mul_integer z


theorem pow20_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow20_4 z * u19 z = pow20_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow20_5_mul z


theorem pow20_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u19 z ^ 5 = pow20_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow20_4_pow z hz]
  exact pow20_5_root z hz


theorem pow20_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow20_5 z * pow20_5 z = pow20_10_q z * f z + pow20_10 z + (41 : R) * pow20_10_mul_t z := by
  simp only [pow20_5, pow20_10_q, f, pow20_10, pow20_10_mul_t]
  
  ring

theorem pow20_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow20_5 z * pow20_5 z = pow20_10_q z * f z + pow20_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow20_10_mul_integer z


theorem pow20_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow20_5 z * pow20_5 z = pow20_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow20_10_mul z


theorem pow20_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u19 z ^ 10 = pow20_10 z := by
  calc
    _ = u19 z ^ 5 * u19 z ^ 5 := by ring
    _ = pow20_5 z * pow20_5 z := by rw [pow20_5_pow z hz]
    _ = _ := pow20_10_root z hz


theorem pow20_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow20_10 z * pow20_10 z = pow20_20_q z * f z + pow20_20 z + (41 : R) * pow20_20_mul_t z := by
  simp only [pow20_10, pow20_20_q, f, pow20_20, pow20_20_mul_t]
  
  ring

theorem pow20_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow20_10 z * pow20_10 z = pow20_20_q z * f z + pow20_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow20_20_mul_integer z


theorem pow20_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow20_10 z * pow20_10 z = pow20_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow20_20_mul z


theorem pow20_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u19 z ^ 20 = pow20_20 z := by
  calc
    _ = u19 z ^ 10 * u19 z ^ 10 := by ring
    _ = pow20_10 z * pow20_10 z := by rw [pow20_10_pow z hz]
    _ = _ := pow20_20_root z hz


theorem pow20_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow20_20 z * pow20_20 z = pow20_40_q z * f z + pow20_40 z + (41 : R) * pow20_40_mul_t z := by
  simp only [pow20_20, pow20_40_q, f, pow20_40, pow20_40_mul_t]
  
  ring

theorem pow20_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow20_20 z * pow20_20 z = pow20_40_q z * f z + pow20_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow20_40_mul_integer z


theorem pow20_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow20_20 z * pow20_20 z = pow20_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow20_40_mul z


theorem pow20_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u19 z ^ 40 = pow20_40 z := by
  calc
    _ = u19 z ^ 20 * u19 z ^ 20 := by ring
    _ = pow20_20 z * pow20_20 z := by rw [pow20_20_pow z hz]
    _ = _ := pow20_40_root z hz


abbrev pow20_41 {R : Type*} [CommRing R] (z : R) : R := u0 z

theorem pow20_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow20_40 z * u19 z = pow20_41_q z * f z + pow20_41 z + (41 : R) * pow20_41_mul_t z := by
  simp only [pow20_40, u19, pow20_41_q, f, pow20_41, pow20_41_mul_t]
  simp only [pow19_41, u0]
  ring

theorem pow20_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow20_40 z * u19 z = pow20_41_q z * f z + pow20_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow20_41_mul_integer z


theorem pow20_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow20_40 z * u19 z = pow20_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow20_41_mul z


theorem pow20_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u19 z ^ 41 = pow20_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow20_40_pow z hz]
  exact pow20_41_root z hz


abbrev u20 {R : Type*} [CommRing R] (z : R) : R := u0 z

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_IntegerPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Polynomial Matrix
namespace DimensionTen.Border
lemma F_degree : F.natDegree = 20 := FP_degree.natDegree_eq

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_BorderData
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

lemma commute_02_row0 : ∀ k : Fin 20, (B0 * B2) 0 k = (B2 * B0) 0 k := by decide +kernel
lemma commute_02_row1 : ∀ k : Fin 20, (B0 * B2) 1 k = (B2 * B0) 1 k := by decide +kernel
lemma commute_02_row10 : ∀ k : Fin 20, (B0 * B2) 10 k = (B2 * B0) 10 k := by decide +kernel

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_PolynomialData
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

lemma W0_eq : W0 = e0 := by decide +kernel

lemma W_step0 : B0 *ᵥ W0 + (-665456935831295645613234276870960 : ℤ) • e0 = W1 := by decide +kernel

lemma W_step1 : B0 *ᵥ W1 + (-70575490389691608208970825963579579734790687104242531156794252400 : ℤ) • e0 = W2 := by decide +kernel

lemma W_step2 : B0 *ᵥ W2 + (145204575748123705650598860122042297964140180806502873813425954437770925496552439336297911807152000 : ℤ) • e0 = W3 := by decide +kernel

lemma W_step3 : B0 *ᵥ W3 + (-35324838830202393213114710617144206880545881202172927720865474148390980209388806187550300213113700416597412380444619467558313120000 : ℤ) • e0 = W4 := by decide +kernel

lemma W_step4 : B0 *ᵥ W4 + (373565650934774887461173450615958673493665750145833416276706195065625377037257320323651912502138867646885039242665453554378883071785987397285956044288246752000000 : ℤ) • e0 = W5 := by decide +kernel

lemma W_step5 : B0 *ᵥ W5 + (1221247532914883428738232812315046413061003261754365921877331401690772085408337009866167041104811173917721563989083295894997519285879820644602218589359930080044045784701600336896172318351552000000 : ℤ) • e0 = W6 := by decide +kernel

lemma W_step6 : B0 *ᵥ W6 + (-248227637152475705027939375857278526128191272750984168929977414072990649655673065160190565283923935144328649963473688624322944637031495498096318971767466342970191076754053510390097551205920734946099494349011595986009016320000000 : ℤ) • e0 = W7 := by decide +kernel

lemma W_step7 : B0 *ᵥ W7 + (23987898748033982540672860523700865395338187584784902027097207883389242545617842033943633110512117271742643190645306300993695952546671697315106563700443682653623151506540994176376096734479969113402657992738820843936302180323975678376815544328820255590400000000 : ℤ) • e0 = W8 := by decide +kernel

lemma W_step8 : B0 *ᵥ W8 + (-1171308828589766784667174319064418542798135133484982791854491081649943231360093785409472006445243262855246426572170988410104927443954726055604498601479060662278001768673622504306995915615815163705741569269783733808816002389524109550321410806269620903448193875229330238654480165635072000000000 : ℤ) • e0 = W9 := by decide +kernel

lemma W_step9 : B0 *ᵥ W9 + (9418076163852223744432430014364091808485209898268329041429484569331398431107415197968026807215347240401736075163106970860375437764441639386759444924342265991793540088391019157445548247844788073792441943995585891632831540649213169911827703330754567896340380609774093821467596292667988969060929685782740051333867520000000000 : ℤ) • e0 = W10 := by decide +kernel

lemma W_step10 : B0 *ᵥ W10 + (2379351982660918187351912781958188527717967481429203927909200858573699275008394894183277671168447409642612098439982572413522546000040986498273641717234153243897007250606150778122646421703817983494954617791128567739285620364189110954410697514797765886291714388494664729026689529953663266988303413000134427206176735476450561111234207094565608243200000000000 : ℤ) • e0 = W11 := by decide +kernel

lemma W_step11 : B0 *ᵥ W11 + (-156443788709025742196345911143201398522107585903943872656350511938867845971206431668038085111377071526334593976793592772236822162619007312610358668945562381934474011199900422427845078146852059081562149156225635557185181304351482728149253212060717470179340715966538846953566303581355673324261441159585174786519237690702352218433699357759363998509903389517501570746482257203200000000000000 : ℤ) • e0 = W12 := by decide +kernel

lemma W_step12 : B0 *ᵥ W12 + (4900890101564280273384249662632200864363178448207658026058163336136819615272493885470202054565224538142000936511937843307007141485106069287814351270516554069895222315717069012981831431598688971184588468042505208877149369556657292564526267236422804943134514567637453529579229073192380181445210152334600678520463948715012876905929334440543179125298895959992011293893481380162364702394538413670540082328535040000000000000 : ℤ) • e0 = W13 := by decide +kernel

lemma W_step13 : B0 *ᵥ W13 + (-84104307174298673686167552255023640494586429007832021068263654225131496108888450236021703884431876764525210998671836899723767574650679562923240549613170660460307111553062077806825303303373793065431974171250181275915638689447630046090976265566391394588988957333827128766847100966792731531401924178962941086742313997809833999852121787629675539133006863302099166667861554529199671567381395010640407518426305516067478326139731889369074892800000000000000 : ℤ) • e0 = W14 := by decide +kernel

lemma W_step14 : B0 *ᵥ W14 + (675860552142364300469163135239922215844669725914434221808961587832864654839688852714377465846874183474661558953416089505955745772157789761536300845401390976278172003633735629354916823207663419987549669250042714970662428618786997007804393564088687435177258735743667457380692013561927748177389045537156630683615468224776124736218311770991358194005151667711594323471452495210584512969519473278662518864183000362256079240789122668752515792267237678356626639740742926336000000000000000 : ℤ) • e0 = W15 := by decide +kernel

lemma W_step15 : B0 *ᵥ W15 + (464264497883407444747214497780812992686704524760753459744647662220415750416845824659077752493206710993356675945744931523943090697063536003409707838510945285234954377033375647019503467236967613563967236378430128420958879199174432425365805238966092079988382033895233428997733820972532862160052383779427027697929911022006616671493677356268258333730255560145075340313333181727787699892890692686951362386275741868725537594362933484314558383739147305382918898686952977786128912938230214944318784798720000000000000000 : ℤ) • e0 = W16 := by decide +kernel

lemma W_step16 : B0 *ᵥ W16 + (-46078962234330275978393081039900872188683319775920327128308452687890209275764118451319687474009314096598155961959548923384930131718444660825818480828257818821039017264033763526190311506189940321255132637170583750838824867220822705767283964636390962873055630047046796945200799791451986485780961563108553013724002067700649315332952049979688029591671182364417015107032858404981473456796680608866020804392285926068306658664953047502713815667799656452571900290324373867393260683805253816278147547319199730096639224635584878424883200000000000000000 : ℤ) • e0 = W17 := by decide +kernel

lemma W_step17 : B0 *ᵥ W17 + (229540072167944847226680415208013118338761677374944768373442556047077491167862762106359122660044266376402295481008188646997320599898453491372250113733518589454936121739510066262153803563671695844108844188342855909377211756360861260377168676543780626494372504766738464872238720120608406900323489717675021679247953712129677892949203666168430318973900550171283869938908653927859069485683785552618689290268121667910013497695005067467335610102307071987167020413797861407454637885276358908659560709050422061741810597789529542860159000644434640948505635320758272000000000000000000 : ℤ) • e0 = W18 := by decide +kernel

lemma W_step18 : B0 *ᵥ W18 + (50511259664407229159646828548337393831498164764442804655127386655612901648776121372469336914091639720740949450692522422501871756701072556552050895980619323103036951478408656634191362563383127130617057997298235140794077506240567579912973487530312823172729903267062062135892781938802036475675819137510666873059408131836941370912492276716379814401275115222108476610434649500821249715911952605938441183268983422802130006238945591464489363332367504221919288966190285721674362152675650209632960747379797873753029847424190752816297979945928310952397381467134670500671900306775579122183700480000000000000000000 : ℤ) • e0 = W19 := by decide +kernel

lemma W_step19 : B0 *ᵥ W19 + (-1424105438854051274637383580879187889947095521139556310680850766315834321551239556574203521562568408091279110770199392239672103401933480228396676040102864674581064663417300893715619893996546336746566239320115175015022647808252252957375990525415013961893949766339014426315700834891145618186295338735724851165176076792616990913196521711297962346422135606209029955414419424094778362387247876506714514958332570454743222106183632267250532813404938217795375126355778437850775218722352764943835257588425767268897713027152377493877523758390937382693586850604084390990278979077079727932490410447293788987687686157708243763200000000000000000000 : ℤ) • e0 = W20 := by decide +kernel

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Annihilator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

lemma aeval_F {R : Type*} [Ring R] [Algebra ℤ R] (z : R) : aeval z F = FP z := by
  exact (map_FP (aeval z).toRingHom (X : ℤ[X])).trans (congrArg (FP (R := R)) (aeval_X (R := ℤ) z))

lemma FP_commute {R : Type*} [Ring R] {x y : R} (h : Commute x y) :
    Commute (FP x) y := by
  rw [← aeval_F, Polynomial.aeval_eq_smeval]
  exact Polynomial.smeval_commute_left ℤ F h

lemma W_add_step0 : (-665456935831295645613234276870960 : ℤ) • e0 + B0 *ᵥ e0 = W1 := by
  simpa only [W0_eq, add_comm] using W_step0

lemma W_add_step1 : (-70575490389691608208970825963579579734790687104242531156794252400 : ℤ) • e0 + B0 *ᵥ W1 = W2 := by
  simpa only [W0_eq, add_comm] using W_step1

lemma W_add_step2 : (145204575748123705650598860122042297964140180806502873813425954437770925496552439336297911807152000 : ℤ) • e0 + B0 *ᵥ W2 = W3 := by
  simpa only [W0_eq, add_comm] using W_step2

lemma W_add_step3 : (-35324838830202393213114710617144206880545881202172927720865474148390980209388806187550300213113700416597412380444619467558313120000 : ℤ) • e0 + B0 *ᵥ W3 = W4 := by
  simpa only [W0_eq, add_comm] using W_step3

lemma W_add_step4 : (373565650934774887461173450615958673493665750145833416276706195065625377037257320323651912502138867646885039242665453554378883071785987397285956044288246752000000 : ℤ) • e0 + B0 *ᵥ W4 = W5 := by
  simpa only [W0_eq, add_comm] using W_step4

lemma W_add_step5 : (1221247532914883428738232812315046413061003261754365921877331401690772085408337009866167041104811173917721563989083295894997519285879820644602218589359930080044045784701600336896172318351552000000 : ℤ) • e0 + B0 *ᵥ W5 = W6 := by
  simpa only [W0_eq, add_comm] using W_step5

lemma W_add_step6 : (-248227637152475705027939375857278526128191272750984168929977414072990649655673065160190565283923935144328649963473688624322944637031495498096318971767466342970191076754053510390097551205920734946099494349011595986009016320000000 : ℤ) • e0 + B0 *ᵥ W6 = W7 := by
  simpa only [W0_eq, add_comm] using W_step6

lemma W_add_step7 : (23987898748033982540672860523700865395338187584784902027097207883389242545617842033943633110512117271742643190645306300993695952546671697315106563700443682653623151506540994176376096734479969113402657992738820843936302180323975678376815544328820255590400000000 : ℤ) • e0 + B0 *ᵥ W7 = W8 := by
  simpa only [W0_eq, add_comm] using W_step7

lemma W_add_step8 : (-1171308828589766784667174319064418542798135133484982791854491081649943231360093785409472006445243262855246426572170988410104927443954726055604498601479060662278001768673622504306995915615815163705741569269783733808816002389524109550321410806269620903448193875229330238654480165635072000000000 : ℤ) • e0 + B0 *ᵥ W8 = W9 := by
  simpa only [W0_eq, add_comm] using W_step8

lemma W_add_step9 : (9418076163852223744432430014364091808485209898268329041429484569331398431107415197968026807215347240401736075163106970860375437764441639386759444924342265991793540088391019157445548247844788073792441943995585891632831540649213169911827703330754567896340380609774093821467596292667988969060929685782740051333867520000000000 : ℤ) • e0 + B0 *ᵥ W9 = W10 := by
  simpa only [W0_eq, add_comm] using W_step9

lemma W_add_step10 : (2379351982660918187351912781958188527717967481429203927909200858573699275008394894183277671168447409642612098439982572413522546000040986498273641717234153243897007250606150778122646421703817983494954617791128567739285620364189110954410697514797765886291714388494664729026689529953663266988303413000134427206176735476450561111234207094565608243200000000000 : ℤ) • e0 + B0 *ᵥ W10 = W11 := by
  simpa only [W0_eq, add_comm] using W_step10

lemma W_add_step11 : (-156443788709025742196345911143201398522107585903943872656350511938867845971206431668038085111377071526334593976793592772236822162619007312610358668945562381934474011199900422427845078146852059081562149156225635557185181304351482728149253212060717470179340715966538846953566303581355673324261441159585174786519237690702352218433699357759363998509903389517501570746482257203200000000000000 : ℤ) • e0 + B0 *ᵥ W11 = W12 := by
  simpa only [W0_eq, add_comm] using W_step11

lemma W_add_step12 : (4900890101564280273384249662632200864363178448207658026058163336136819615272493885470202054565224538142000936511937843307007141485106069287814351270516554069895222315717069012981831431598688971184588468042505208877149369556657292564526267236422804943134514567637453529579229073192380181445210152334600678520463948715012876905929334440543179125298895959992011293893481380162364702394538413670540082328535040000000000000 : ℤ) • e0 + B0 *ᵥ W12 = W13 := by
  simpa only [W0_eq, add_comm] using W_step12

lemma W_add_step13 : (-84104307174298673686167552255023640494586429007832021068263654225131496108888450236021703884431876764525210998671836899723767574650679562923240549613170660460307111553062077806825303303373793065431974171250181275915638689447630046090976265566391394588988957333827128766847100966792731531401924178962941086742313997809833999852121787629675539133006863302099166667861554529199671567381395010640407518426305516067478326139731889369074892800000000000000 : ℤ) • e0 + B0 *ᵥ W13 = W14 := by
  simpa only [W0_eq, add_comm] using W_step13

lemma W_add_step14 : (675860552142364300469163135239922215844669725914434221808961587832864654839688852714377465846874183474661558953416089505955745772157789761536300845401390976278172003633735629354916823207663419987549669250042714970662428618786997007804393564088687435177258735743667457380692013561927748177389045537156630683615468224776124736218311770991358194005151667711594323471452495210584512969519473278662518864183000362256079240789122668752515792267237678356626639740742926336000000000000000 : ℤ) • e0 + B0 *ᵥ W14 = W15 := by
  simpa only [W0_eq, add_comm] using W_step14

lemma W_add_step15 : (464264497883407444747214497780812992686704524760753459744647662220415750416845824659077752493206710993356675945744931523943090697063536003409707838510945285234954377033375647019503467236967613563967236378430128420958879199174432425365805238966092079988382033895233428997733820972532862160052383779427027697929911022006616671493677356268258333730255560145075340313333181727787699892890692686951362386275741868725537594362933484314558383739147305382918898686952977786128912938230214944318784798720000000000000000 : ℤ) • e0 + B0 *ᵥ W15 = W16 := by
  simpa only [W0_eq, add_comm] using W_step15

lemma W_add_step16 : (-46078962234330275978393081039900872188683319775920327128308452687890209275764118451319687474009314096598155961959548923384930131718444660825818480828257818821039017264033763526190311506189940321255132637170583750838824867220822705767283964636390962873055630047046796945200799791451986485780961563108553013724002067700649315332952049979688029591671182364417015107032858404981473456796680608866020804392285926068306658664953047502713815667799656452571900290324373867393260683805253816278147547319199730096639224635584878424883200000000000000000 : ℤ) • e0 + B0 *ᵥ W16 = W17 := by
  simpa only [W0_eq, add_comm] using W_step16

lemma W_add_step17 : (229540072167944847226680415208013118338761677374944768373442556047077491167862762106359122660044266376402295481008188646997320599898453491372250113733518589454936121739510066262153803563671695844108844188342855909377211756360861260377168676543780626494372504766738464872238720120608406900323489717675021679247953712129677892949203666168430318973900550171283869938908653927859069485683785552618689290268121667910013497695005067467335610102307071987167020413797861407454637885276358908659560709050422061741810597789529542860159000644434640948505635320758272000000000000000000 : ℤ) • e0 + B0 *ᵥ W17 = W18 := by
  simpa only [W0_eq, add_comm] using W_step17

lemma W_add_step18 : (50511259664407229159646828548337393831498164764442804655127386655612901648776121372469336914091639720740949450692522422501871756701072556552050895980619323103036951478408656634191362563383127130617057997298235140794077506240567579912973487530312823172729903267062062135892781938802036475675819137510666873059408131836941370912492276716379814401275115222108476610434649500821249715911952605938441183268983422802130006238945591464489363332367504221919288966190285721674362152675650209632960747379797873753029847424190752816297979945928310952397381467134670500671900306775579122183700480000000000000000000 : ℤ) • e0 + B0 *ᵥ W18 = W19 := by
  simpa only [W0_eq, add_comm] using W_step18

lemma W_add_step19 : (-1424105438854051274637383580879187889947095521139556310680850766315834321551239556574203521562568408091279110770199392239672103401933480228396676040102864674581064663417300893715619893996546336746566239320115175015022647808252252957375990525415013961893949766339014426315700834891145618186295338735724851165176076792616990913196521711297962346422135606209029955414419424094778362387247876506714514958332570454743222106183632267250532813404938217795375126355778437850775218722352764943835257588425767268897713027152377493877523758390937382693586850604084390990278979077079727932490410447293788987687686157708243763200000000000000000000 : ℤ) • e0 + B0 *ᵥ W19 = W20 := by
  simpa only [W0_eq, add_comm] using W_step19

lemma FP_annihilates_e0 : (FP B0) *ᵥ e0 = 0 := by
  simp only [FP, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.intCast_mulVec,
    Int.cast_id, Matrix.one_mulVec, W_add_step0, W_add_step1, W_add_step2, W_add_step3, W_add_step4, W_add_step5, W_add_step6, W_add_step7, W_add_step8, W_add_step9, W_add_step10, W_add_step11, W_add_step12, W_add_step13, W_add_step14, W_add_step15, W_add_step16, W_add_step17, W_add_step18, W_add_step19, W20_eq]

lemma shift_1 : B2 *ᵥ (Pi.single 0 1 : Fin 20 → ℤ) = d • Pi.single 1 1 := by decide +kernel

lemma annihilate_0 : (FP B0) *ᵥ (Pi.single 0 1 : Fin 20 → ℤ) = 0 := by
  exact FP_annihilates_e0

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_GaloisField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Polynomial Matrix
namespace DimensionTen.Border

abbrev K := fQ.SplittingField

end DimensionTen.Border

end
end

end OAI
end


