-- Prove2me | Definitions.Def_OAIQ033D010
-- name    : OAIQ033D010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T01:50:35.533703+00:00
-- url     : https://prove2.me/theorems/52771582-bd39-4188-b832-993f23392b59
-- title:
--   Definitions bundle OAIQ033D010 of the split of OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DimensionTen.main_pair`, carved from OpenAI's openai/math development (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 287 declarations of OpenAI's Lean: 287 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Quantum/DimensionTen, in whole or in part: [`Quantum_DimensionTen_Mod41Powers02`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod41Powers02.lean), [`Quantum_DimensionTen_Mod41Powers03`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod41Powers03.lean), [`Quantum_DimensionTen_Mod41Powers04`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod41Powers04.lean), [`Quantum_DimensionTen_Mod41Powers05`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod41Powers05.lean), [`Quantum_DimensionTen_Mod41Powers06`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod41Powers06.lean), [`Quantum_DimensionTen_Mod41Powers07`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod41Powers07.lean), [`Quantum_DimensionTen_Mod41Powers08`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod41Powers08.lean), [`Quantum_DimensionTen_Mod41Result`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Quantum/DimensionTen/Quantum/DimensionTen/Mod41Result.lean).
--
--   **Imports.** It imports the bundles `OAIQ033D000`, `OAIQ033D001` and `OAIQ033D002` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ033D014`.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Quantum/DimensionTen at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ033D000
import Definitions.Def_OAIQ033D001
import Definitions.Def_OAIQ033D002

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod41Powers02
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41


theorem pow4_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow4_4 z * u3 z = pow4_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_5_mul z


theorem pow4_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u3 z ^ 5 = pow4_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow4_4_pow z hz]
  exact pow4_5_root z hz


theorem pow4_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u3 z ^ 10 = pow4_10 z := by
  calc
    _ = u3 z ^ 5 * u3 z ^ 5 := by ring
    _ = pow4_5 z * pow4_5 z := by rw [pow4_5_pow z hz]
    _ = _ := pow4_10_root z hz


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


theorem pow4_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow4_40 z * u3 z = pow4_41_q z * f z + pow4_41 z + (41 : R) * pow4_41_mul_t z := by
  simp only [pow4_40, u3, pow4_41_q, f, pow4_41, pow4_41_mul_t]
  simp only [pow3_41]
  ring

theorem pow4_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow4_40 z * u3 z = pow4_41_q z * f z + pow4_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow4_41_mul_integer z


theorem pow4_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow4_40 z * u3 z = pow4_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow4_41_mul z


theorem pow4_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u3 z ^ 41 = pow4_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow4_40_pow z hz]
  exact pow4_41_root z hz


theorem iterate4 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 4) = u4 z := by
  calc
    _ = (z ^ (41 ^ 3)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u3 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate3 z hz)
    _ = _ := pow4_41_pow z hz

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod41Powers03
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41

theorem pow5_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u4 z * u4 z = pow5_2_q z * f z + pow5_2 z + (41 : R) * pow5_2_mul_t z := by
  simp only [u4, pow5_2_q, f, pow5_2, pow5_2_mul_t]
  simp only [pow4_41]
  ring

theorem pow5_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u4 z * u4 z = pow5_2_q z * f z + pow5_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow5_2_mul_integer z


theorem pow5_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u4 z * u4 z = pow5_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_2_mul z


theorem pow5_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u4 z ^ 2 = pow5_2 z := by
  calc
    _ = u4 z ^ 1 * u4 z ^ 1 := by ring
    _ = u4 z * u4 z := by simp only [pow_one]
    _ = _ := pow5_2_root z hz


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


theorem pow5_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u4 z ^ 4 = pow5_4 z := by
  calc
    _ = u4 z ^ 2 * u4 z ^ 2 := by ring
    _ = pow5_2 z * pow5_2 z := by rw [pow5_2_pow z hz]
    _ = _ := pow5_4_root z hz


theorem pow5_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_4 z * u4 z = pow5_5_q z * f z + pow5_5 z + (41 : R) * pow5_5_mul_t z := by
  simp only [pow5_4, u4, pow5_5_q, f, pow5_5, pow5_5_mul_t]
  simp only [pow4_41]
  ring

theorem pow5_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow5_4 z * u4 z = pow5_5_q z * f z + pow5_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow5_5_mul_integer z


theorem pow5_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow5_4 z * u4 z = pow5_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_5_mul z


theorem pow5_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u4 z ^ 5 = pow5_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow5_4_pow z hz]
  exact pow5_5_root z hz


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


theorem pow5_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u4 z ^ 10 = pow5_10 z := by
  calc
    _ = u4 z ^ 5 * u4 z ^ 5 := by ring
    _ = pow5_5 z * pow5_5 z := by rw [pow5_5_pow z hz]
    _ = _ := pow5_10_root z hz


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


theorem pow5_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u4 z ^ 20 = pow5_20 z := by
  calc
    _ = u4 z ^ 10 * u4 z ^ 10 := by ring
    _ = pow5_10 z * pow5_10 z := by rw [pow5_10_pow z hz]
    _ = _ := pow5_20_root z hz


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


theorem pow5_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u4 z ^ 40 = pow5_40 z := by
  calc
    _ = u4 z ^ 20 * u4 z ^ 20 := by ring
    _ = pow5_20 z * pow5_20 z := by rw [pow5_20_pow z hz]
    _ = _ := pow5_40_root z hz


theorem pow5_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow5_40 z * u4 z = pow5_41_q z * f z + pow5_41 z + (41 : R) * pow5_41_mul_t z := by
  simp only [pow5_40, u4, pow5_41_q, f, pow5_41, pow5_41_mul_t]
  simp only [pow4_41]
  ring

theorem pow5_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow5_40 z * u4 z = pow5_41_q z * f z + pow5_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow5_41_mul_integer z


theorem pow5_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow5_40 z * u4 z = pow5_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow5_41_mul z


theorem pow5_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u4 z ^ 41 = pow5_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow5_40_pow z hz]
  exact pow5_41_root z hz


theorem iterate5 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 5) = u5 z := by
  calc
    _ = (z ^ (41 ^ 4)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u4 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate4 z hz)
    _ = _ := pow5_41_pow z hz


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


theorem iterate6 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 6) = u6 z := by
  calc
    _ = (z ^ (41 ^ 5)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u5 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate5 z hz)
    _ = _ := pow6_41_pow z hz

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod41Powers04
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41

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


theorem iterate7 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 7) = u7 z := by
  calc
    _ = (z ^ (41 ^ 6)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u6 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate6 z hz)
    _ = _ := pow7_41_pow z hz


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


theorem pow8_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u7 z ^ 10 = pow8_10 z := by
  calc
    _ = u7 z ^ 5 * u7 z ^ 5 := by ring
    _ = pow8_5 z * pow8_5 z := by rw [pow8_5_pow z hz]
    _ = _ := pow8_10_root z hz


theorem pow8_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_10 z * pow8_10 z = pow8_20_q z * f z + pow8_20 z + (41 : R) * pow8_20_mul_t z := by
  simp only [pow8_10, pow8_20_q, f, pow8_20, pow8_20_mul_t]
  
  ring

theorem pow8_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow8_10 z * pow8_10 z = pow8_20_q z * f z + pow8_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow8_20_mul_integer z


theorem pow8_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow8_10 z * pow8_10 z = pow8_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_20_mul z


theorem pow8_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u7 z ^ 20 = pow8_20 z := by
  calc
    _ = u7 z ^ 10 * u7 z ^ 10 := by ring
    _ = pow8_10 z * pow8_10 z := by rw [pow8_10_pow z hz]
    _ = _ := pow8_20_root z hz


theorem pow8_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_20 z * pow8_20 z = pow8_40_q z * f z + pow8_40 z + (41 : R) * pow8_40_mul_t z := by
  simp only [pow8_20, pow8_40_q, f, pow8_40, pow8_40_mul_t]
  
  ring

theorem pow8_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow8_20 z * pow8_20 z = pow8_40_q z * f z + pow8_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow8_40_mul_integer z


theorem pow8_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow8_20 z * pow8_20 z = pow8_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_40_mul z


theorem pow8_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u7 z ^ 40 = pow8_40 z := by
  calc
    _ = u7 z ^ 20 * u7 z ^ 20 := by ring
    _ = pow8_20 z * pow8_20 z := by rw [pow8_20_pow z hz]
    _ = _ := pow8_40_root z hz


theorem pow8_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow8_40 z * u7 z = pow8_41_q z * f z + pow8_41 z + (41 : R) * pow8_41_mul_t z := by
  simp only [pow8_40, u7, pow8_41_q, f, pow8_41, pow8_41_mul_t]
  simp only [pow7_41]
  ring

theorem pow8_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow8_40 z * u7 z = pow8_41_q z * f z + pow8_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow8_41_mul_integer z


theorem pow8_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow8_40 z * u7 z = pow8_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow8_41_mul z


theorem pow8_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u7 z ^ 41 = pow8_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow8_40_pow z hz]
  exact pow8_41_root z hz


theorem iterate8 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 8) = u8 z := by
  calc
    _ = (z ^ (41 ^ 7)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u7 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate7 z hz)
    _ = _ := pow8_41_pow z hz

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod41Powers05
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41

theorem pow9_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u8 z * u8 z = pow9_2_q z * f z + pow9_2 z + (41 : R) * pow9_2_mul_t z := by
  simp only [u8, pow9_2_q, f, pow9_2, pow9_2_mul_t]
  simp only [pow8_41]
  ring

theorem pow9_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u8 z * u8 z = pow9_2_q z * f z + pow9_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow9_2_mul_integer z


theorem pow9_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u8 z * u8 z = pow9_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_2_mul z


theorem pow9_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u8 z ^ 2 = pow9_2 z := by
  calc
    _ = u8 z ^ 1 * u8 z ^ 1 := by ring
    _ = u8 z * u8 z := by simp only [pow_one]
    _ = _ := pow9_2_root z hz


theorem pow9_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_2 z * pow9_2 z = pow9_4_q z * f z + pow9_4 z + (41 : R) * pow9_4_mul_t z := by
  simp only [pow9_2, pow9_4_q, f, pow9_4, pow9_4_mul_t]
  
  ring

theorem pow9_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow9_2 z * pow9_2 z = pow9_4_q z * f z + pow9_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow9_4_mul_integer z


theorem pow9_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow9_2 z * pow9_2 z = pow9_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_4_mul z


theorem pow9_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u8 z ^ 4 = pow9_4 z := by
  calc
    _ = u8 z ^ 2 * u8 z ^ 2 := by ring
    _ = pow9_2 z * pow9_2 z := by rw [pow9_2_pow z hz]
    _ = _ := pow9_4_root z hz


theorem pow9_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_4 z * u8 z = pow9_5_q z * f z + pow9_5 z + (41 : R) * pow9_5_mul_t z := by
  simp only [pow9_4, u8, pow9_5_q, f, pow9_5, pow9_5_mul_t]
  simp only [pow8_41]
  ring

theorem pow9_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow9_4 z * u8 z = pow9_5_q z * f z + pow9_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow9_5_mul_integer z


theorem pow9_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow9_4 z * u8 z = pow9_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_5_mul z


theorem pow9_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u8 z ^ 5 = pow9_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow9_4_pow z hz]
  exact pow9_5_root z hz


theorem pow9_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_5 z * pow9_5 z = pow9_10_q z * f z + pow9_10 z + (41 : R) * pow9_10_mul_t z := by
  simp only [pow9_5, pow9_10_q, f, pow9_10, pow9_10_mul_t]
  
  ring

theorem pow9_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow9_5 z * pow9_5 z = pow9_10_q z * f z + pow9_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow9_10_mul_integer z


theorem pow9_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow9_5 z * pow9_5 z = pow9_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_10_mul z


theorem pow9_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u8 z ^ 10 = pow9_10 z := by
  calc
    _ = u8 z ^ 5 * u8 z ^ 5 := by ring
    _ = pow9_5 z * pow9_5 z := by rw [pow9_5_pow z hz]
    _ = _ := pow9_10_root z hz


theorem pow9_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_10 z * pow9_10 z = pow9_20_q z * f z + pow9_20 z + (41 : R) * pow9_20_mul_t z := by
  simp only [pow9_10, pow9_20_q, f, pow9_20, pow9_20_mul_t]
  
  ring

theorem pow9_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow9_10 z * pow9_10 z = pow9_20_q z * f z + pow9_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow9_20_mul_integer z


theorem pow9_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow9_10 z * pow9_10 z = pow9_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_20_mul z


theorem pow9_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u8 z ^ 20 = pow9_20 z := by
  calc
    _ = u8 z ^ 10 * u8 z ^ 10 := by ring
    _ = pow9_10 z * pow9_10 z := by rw [pow9_10_pow z hz]
    _ = _ := pow9_20_root z hz


theorem pow9_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_20 z * pow9_20 z = pow9_40_q z * f z + pow9_40 z + (41 : R) * pow9_40_mul_t z := by
  simp only [pow9_20, pow9_40_q, f, pow9_40, pow9_40_mul_t]
  
  ring

theorem pow9_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow9_20 z * pow9_20 z = pow9_40_q z * f z + pow9_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow9_40_mul_integer z


theorem pow9_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow9_20 z * pow9_20 z = pow9_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_40_mul z


theorem pow9_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u8 z ^ 40 = pow9_40 z := by
  calc
    _ = u8 z ^ 20 * u8 z ^ 20 := by ring
    _ = pow9_20 z * pow9_20 z := by rw [pow9_20_pow z hz]
    _ = _ := pow9_40_root z hz


theorem pow9_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow9_40 z * u8 z = pow9_41_q z * f z + pow9_41 z + (41 : R) * pow9_41_mul_t z := by
  simp only [pow9_40, u8, pow9_41_q, f, pow9_41, pow9_41_mul_t]
  simp only [pow8_41]
  ring

theorem pow9_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow9_40 z * u8 z = pow9_41_q z * f z + pow9_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow9_41_mul_integer z


theorem pow9_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow9_40 z * u8 z = pow9_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow9_41_mul z


theorem pow9_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u8 z ^ 41 = pow9_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow9_40_pow z hz]
  exact pow9_41_root z hz


theorem iterate9 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 9) = u9 z := by
  calc
    _ = (z ^ (41 ^ 8)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u8 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate8 z hz)
    _ = _ := pow9_41_pow z hz


theorem pow10_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u9 z * u9 z = pow10_2_q z * f z + pow10_2 z + (41 : R) * pow10_2_mul_t z := by
  simp only [u9, pow10_2_q, f, pow10_2, pow10_2_mul_t]
  simp only [pow9_41]
  ring

theorem pow10_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u9 z * u9 z = pow10_2_q z * f z + pow10_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow10_2_mul_integer z


theorem pow10_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u9 z * u9 z = pow10_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_2_mul z


theorem pow10_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u9 z ^ 2 = pow10_2 z := by
  calc
    _ = u9 z ^ 1 * u9 z ^ 1 := by ring
    _ = u9 z * u9 z := by simp only [pow_one]
    _ = _ := pow10_2_root z hz


theorem pow10_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_2 z * pow10_2 z = pow10_4_q z * f z + pow10_4 z + (41 : R) * pow10_4_mul_t z := by
  simp only [pow10_2, pow10_4_q, f, pow10_4, pow10_4_mul_t]
  
  ring

theorem pow10_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow10_2 z * pow10_2 z = pow10_4_q z * f z + pow10_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow10_4_mul_integer z


theorem pow10_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow10_2 z * pow10_2 z = pow10_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_4_mul z


theorem pow10_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u9 z ^ 4 = pow10_4 z := by
  calc
    _ = u9 z ^ 2 * u9 z ^ 2 := by ring
    _ = pow10_2 z * pow10_2 z := by rw [pow10_2_pow z hz]
    _ = _ := pow10_4_root z hz


theorem pow10_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_4 z * u9 z = pow10_5_q z * f z + pow10_5 z + (41 : R) * pow10_5_mul_t z := by
  simp only [pow10_4, u9, pow10_5_q, f, pow10_5, pow10_5_mul_t]
  simp only [pow9_41]
  ring

theorem pow10_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow10_4 z * u9 z = pow10_5_q z * f z + pow10_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow10_5_mul_integer z


theorem pow10_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow10_4 z * u9 z = pow10_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_5_mul z


theorem pow10_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u9 z ^ 5 = pow10_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow10_4_pow z hz]
  exact pow10_5_root z hz


theorem pow10_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_5 z * pow10_5 z = pow10_10_q z * f z + pow10_10 z + (41 : R) * pow10_10_mul_t z := by
  simp only [pow10_5, pow10_10_q, f, pow10_10, pow10_10_mul_t]
  
  ring

theorem pow10_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow10_5 z * pow10_5 z = pow10_10_q z * f z + pow10_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow10_10_mul_integer z


theorem pow10_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow10_5 z * pow10_5 z = pow10_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_10_mul z


theorem pow10_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u9 z ^ 10 = pow10_10 z := by
  calc
    _ = u9 z ^ 5 * u9 z ^ 5 := by ring
    _ = pow10_5 z * pow10_5 z := by rw [pow10_5_pow z hz]
    _ = _ := pow10_10_root z hz


theorem pow10_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_10 z * pow10_10 z = pow10_20_q z * f z + pow10_20 z + (41 : R) * pow10_20_mul_t z := by
  simp only [pow10_10, pow10_20_q, f, pow10_20, pow10_20_mul_t]
  
  ring

theorem pow10_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow10_10 z * pow10_10 z = pow10_20_q z * f z + pow10_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow10_20_mul_integer z


theorem pow10_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow10_10 z * pow10_10 z = pow10_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_20_mul z


theorem pow10_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u9 z ^ 20 = pow10_20 z := by
  calc
    _ = u9 z ^ 10 * u9 z ^ 10 := by ring
    _ = pow10_10 z * pow10_10 z := by rw [pow10_10_pow z hz]
    _ = _ := pow10_20_root z hz


theorem pow10_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_20 z * pow10_20 z = pow10_40_q z * f z + pow10_40 z + (41 : R) * pow10_40_mul_t z := by
  simp only [pow10_20, pow10_40_q, f, pow10_40, pow10_40_mul_t]
  
  ring

theorem pow10_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow10_20 z * pow10_20 z = pow10_40_q z * f z + pow10_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow10_40_mul_integer z


theorem pow10_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow10_20 z * pow10_20 z = pow10_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_40_mul z


theorem pow10_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u9 z ^ 40 = pow10_40 z := by
  calc
    _ = u9 z ^ 20 * u9 z ^ 20 := by ring
    _ = pow10_20 z * pow10_20 z := by rw [pow10_20_pow z hz]
    _ = _ := pow10_40_root z hz


theorem pow10_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow10_40 z * u9 z = pow10_41_q z * f z + pow10_41 z + (41 : R) * pow10_41_mul_t z := by
  simp only [pow10_40, u9, pow10_41_q, f, pow10_41, pow10_41_mul_t]
  simp only [pow9_41]
  ring

theorem pow10_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow10_40 z * u9 z = pow10_41_q z * f z + pow10_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow10_41_mul_integer z


theorem pow10_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow10_40 z * u9 z = pow10_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow10_41_mul z


theorem pow10_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u9 z ^ 41 = pow10_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow10_40_pow z hz]
  exact pow10_41_root z hz


theorem iterate10 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 10) = u10 z := by
  calc
    _ = (z ^ (41 ^ 9)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u9 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate9 z hz)
    _ = _ := pow10_41_pow z hz

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod41Powers06
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41

theorem pow11_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u10 z * u10 z = pow11_2_q z * f z + pow11_2 z + (41 : R) * pow11_2_mul_t z := by
  simp only [u10, pow11_2_q, f, pow11_2, pow11_2_mul_t]
  simp only [pow10_41]
  ring

theorem pow11_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u10 z * u10 z = pow11_2_q z * f z + pow11_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow11_2_mul_integer z


theorem pow11_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u10 z * u10 z = pow11_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_2_mul z


theorem pow11_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u10 z ^ 2 = pow11_2 z := by
  calc
    _ = u10 z ^ 1 * u10 z ^ 1 := by ring
    _ = u10 z * u10 z := by simp only [pow_one]
    _ = _ := pow11_2_root z hz


theorem pow11_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_2 z * pow11_2 z = pow11_4_q z * f z + pow11_4 z + (41 : R) * pow11_4_mul_t z := by
  simp only [pow11_2, pow11_4_q, f, pow11_4, pow11_4_mul_t]
  
  ring

theorem pow11_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow11_2 z * pow11_2 z = pow11_4_q z * f z + pow11_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow11_4_mul_integer z


theorem pow11_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow11_2 z * pow11_2 z = pow11_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_4_mul z


theorem pow11_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u10 z ^ 4 = pow11_4 z := by
  calc
    _ = u10 z ^ 2 * u10 z ^ 2 := by ring
    _ = pow11_2 z * pow11_2 z := by rw [pow11_2_pow z hz]
    _ = _ := pow11_4_root z hz


theorem pow11_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_4 z * u10 z = pow11_5_q z * f z + pow11_5 z + (41 : R) * pow11_5_mul_t z := by
  simp only [pow11_4, u10, pow11_5_q, f, pow11_5, pow11_5_mul_t]
  simp only [pow10_41]
  ring

theorem pow11_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow11_4 z * u10 z = pow11_5_q z * f z + pow11_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow11_5_mul_integer z


theorem pow11_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow11_4 z * u10 z = pow11_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_5_mul z


theorem pow11_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u10 z ^ 5 = pow11_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow11_4_pow z hz]
  exact pow11_5_root z hz


theorem pow11_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_5 z * pow11_5 z = pow11_10_q z * f z + pow11_10 z + (41 : R) * pow11_10_mul_t z := by
  simp only [pow11_5, pow11_10_q, f, pow11_10, pow11_10_mul_t]
  
  ring

theorem pow11_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow11_5 z * pow11_5 z = pow11_10_q z * f z + pow11_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow11_10_mul_integer z


theorem pow11_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow11_5 z * pow11_5 z = pow11_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_10_mul z


theorem pow11_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u10 z ^ 10 = pow11_10 z := by
  calc
    _ = u10 z ^ 5 * u10 z ^ 5 := by ring
    _ = pow11_5 z * pow11_5 z := by rw [pow11_5_pow z hz]
    _ = _ := pow11_10_root z hz


theorem pow11_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_10 z * pow11_10 z = pow11_20_q z * f z + pow11_20 z + (41 : R) * pow11_20_mul_t z := by
  simp only [pow11_10, pow11_20_q, f, pow11_20, pow11_20_mul_t]
  
  ring

theorem pow11_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow11_10 z * pow11_10 z = pow11_20_q z * f z + pow11_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow11_20_mul_integer z


theorem pow11_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow11_10 z * pow11_10 z = pow11_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_20_mul z


theorem pow11_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u10 z ^ 20 = pow11_20 z := by
  calc
    _ = u10 z ^ 10 * u10 z ^ 10 := by ring
    _ = pow11_10 z * pow11_10 z := by rw [pow11_10_pow z hz]
    _ = _ := pow11_20_root z hz


theorem pow11_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_20 z * pow11_20 z = pow11_40_q z * f z + pow11_40 z + (41 : R) * pow11_40_mul_t z := by
  simp only [pow11_20, pow11_40_q, f, pow11_40, pow11_40_mul_t]
  
  ring

theorem pow11_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow11_20 z * pow11_20 z = pow11_40_q z * f z + pow11_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow11_40_mul_integer z


theorem pow11_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow11_20 z * pow11_20 z = pow11_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_40_mul z


theorem pow11_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u10 z ^ 40 = pow11_40 z := by
  calc
    _ = u10 z ^ 20 * u10 z ^ 20 := by ring
    _ = pow11_20 z * pow11_20 z := by rw [pow11_20_pow z hz]
    _ = _ := pow11_40_root z hz


theorem pow11_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow11_40 z * u10 z = pow11_41_q z * f z + pow11_41 z + (41 : R) * pow11_41_mul_t z := by
  simp only [pow11_40, u10, pow11_41_q, f, pow11_41, pow11_41_mul_t]
  simp only [pow10_41]
  ring

theorem pow11_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow11_40 z * u10 z = pow11_41_q z * f z + pow11_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow11_41_mul_integer z


theorem pow11_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow11_40 z * u10 z = pow11_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow11_41_mul z


theorem pow11_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u10 z ^ 41 = pow11_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow11_40_pow z hz]
  exact pow11_41_root z hz


theorem iterate11 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 11) = u11 z := by
  calc
    _ = (z ^ (41 ^ 10)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u10 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate10 z hz)
    _ = _ := pow11_41_pow z hz


theorem pow12_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u11 z * u11 z = pow12_2_q z * f z + pow12_2 z + (41 : R) * pow12_2_mul_t z := by
  simp only [u11, pow12_2_q, f, pow12_2, pow12_2_mul_t]
  simp only [pow11_41]
  ring

theorem pow12_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u11 z * u11 z = pow12_2_q z * f z + pow12_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow12_2_mul_integer z


theorem pow12_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u11 z * u11 z = pow12_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_2_mul z


theorem pow12_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u11 z ^ 2 = pow12_2 z := by
  calc
    _ = u11 z ^ 1 * u11 z ^ 1 := by ring
    _ = u11 z * u11 z := by simp only [pow_one]
    _ = _ := pow12_2_root z hz


theorem pow12_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_2 z * pow12_2 z = pow12_4_q z * f z + pow12_4 z + (41 : R) * pow12_4_mul_t z := by
  simp only [pow12_2, pow12_4_q, f, pow12_4, pow12_4_mul_t]
  
  ring

theorem pow12_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow12_2 z * pow12_2 z = pow12_4_q z * f z + pow12_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow12_4_mul_integer z


theorem pow12_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow12_2 z * pow12_2 z = pow12_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_4_mul z


theorem pow12_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u11 z ^ 4 = pow12_4 z := by
  calc
    _ = u11 z ^ 2 * u11 z ^ 2 := by ring
    _ = pow12_2 z * pow12_2 z := by rw [pow12_2_pow z hz]
    _ = _ := pow12_4_root z hz


theorem pow12_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_4 z * u11 z = pow12_5_q z * f z + pow12_5 z + (41 : R) * pow12_5_mul_t z := by
  simp only [pow12_4, u11, pow12_5_q, f, pow12_5, pow12_5_mul_t]
  simp only [pow11_41]
  ring

theorem pow12_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow12_4 z * u11 z = pow12_5_q z * f z + pow12_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow12_5_mul_integer z


theorem pow12_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow12_4 z * u11 z = pow12_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_5_mul z


theorem pow12_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u11 z ^ 5 = pow12_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow12_4_pow z hz]
  exact pow12_5_root z hz


theorem pow12_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_5 z * pow12_5 z = pow12_10_q z * f z + pow12_10 z + (41 : R) * pow12_10_mul_t z := by
  simp only [pow12_5, pow12_10_q, f, pow12_10, pow12_10_mul_t]
  
  ring

theorem pow12_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow12_5 z * pow12_5 z = pow12_10_q z * f z + pow12_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow12_10_mul_integer z


theorem pow12_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow12_5 z * pow12_5 z = pow12_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_10_mul z


theorem pow12_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u11 z ^ 10 = pow12_10 z := by
  calc
    _ = u11 z ^ 5 * u11 z ^ 5 := by ring
    _ = pow12_5 z * pow12_5 z := by rw [pow12_5_pow z hz]
    _ = _ := pow12_10_root z hz


theorem pow12_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_10 z * pow12_10 z = pow12_20_q z * f z + pow12_20 z + (41 : R) * pow12_20_mul_t z := by
  simp only [pow12_10, pow12_20_q, f, pow12_20, pow12_20_mul_t]
  
  ring

theorem pow12_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow12_10 z * pow12_10 z = pow12_20_q z * f z + pow12_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow12_20_mul_integer z


theorem pow12_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow12_10 z * pow12_10 z = pow12_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_20_mul z


theorem pow12_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u11 z ^ 20 = pow12_20 z := by
  calc
    _ = u11 z ^ 10 * u11 z ^ 10 := by ring
    _ = pow12_10 z * pow12_10 z := by rw [pow12_10_pow z hz]
    _ = _ := pow12_20_root z hz


theorem pow12_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_20 z * pow12_20 z = pow12_40_q z * f z + pow12_40 z + (41 : R) * pow12_40_mul_t z := by
  simp only [pow12_20, pow12_40_q, f, pow12_40, pow12_40_mul_t]
  
  ring

theorem pow12_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow12_20 z * pow12_20 z = pow12_40_q z * f z + pow12_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow12_40_mul_integer z


theorem pow12_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow12_20 z * pow12_20 z = pow12_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_40_mul z


theorem pow12_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u11 z ^ 40 = pow12_40 z := by
  calc
    _ = u11 z ^ 20 * u11 z ^ 20 := by ring
    _ = pow12_20 z * pow12_20 z := by rw [pow12_20_pow z hz]
    _ = _ := pow12_40_root z hz


theorem pow12_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow12_40 z * u11 z = pow12_41_q z * f z + pow12_41 z + (41 : R) * pow12_41_mul_t z := by
  simp only [pow12_40, u11, pow12_41_q, f, pow12_41, pow12_41_mul_t]
  simp only [pow11_41]
  ring

theorem pow12_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow12_40 z * u11 z = pow12_41_q z * f z + pow12_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow12_41_mul_integer z


theorem pow12_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow12_40 z * u11 z = pow12_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow12_41_mul z


theorem pow12_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u11 z ^ 41 = pow12_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow12_40_pow z hz]
  exact pow12_41_root z hz


theorem iterate12 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 12) = u12 z := by
  calc
    _ = (z ^ (41 ^ 11)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u11 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate11 z hz)
    _ = _ := pow12_41_pow z hz

end DimensionTen.Mod41

end

end OAI
end

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

theorem pow13_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u12 z * u12 z = pow13_2_q z * f z + pow13_2 z + (41 : R) * pow13_2_mul_t z := by
  simp only [u12, pow13_2_q, f, pow13_2, pow13_2_mul_t]
  simp only [pow12_41]
  ring

theorem pow13_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u12 z * u12 z = pow13_2_q z * f z + pow13_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow13_2_mul_integer z


theorem pow13_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u12 z * u12 z = pow13_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_2_mul z


theorem pow13_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u12 z ^ 2 = pow13_2 z := by
  calc
    _ = u12 z ^ 1 * u12 z ^ 1 := by ring
    _ = u12 z * u12 z := by simp only [pow_one]
    _ = _ := pow13_2_root z hz


theorem pow13_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_2 z * pow13_2 z = pow13_4_q z * f z + pow13_4 z + (41 : R) * pow13_4_mul_t z := by
  simp only [pow13_2, pow13_4_q, f, pow13_4, pow13_4_mul_t]
  
  ring

theorem pow13_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow13_2 z * pow13_2 z = pow13_4_q z * f z + pow13_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow13_4_mul_integer z


theorem pow13_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow13_2 z * pow13_2 z = pow13_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_4_mul z


theorem pow13_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u12 z ^ 4 = pow13_4 z := by
  calc
    _ = u12 z ^ 2 * u12 z ^ 2 := by ring
    _ = pow13_2 z * pow13_2 z := by rw [pow13_2_pow z hz]
    _ = _ := pow13_4_root z hz


theorem pow13_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_4 z * u12 z = pow13_5_q z * f z + pow13_5 z + (41 : R) * pow13_5_mul_t z := by
  simp only [pow13_4, u12, pow13_5_q, f, pow13_5, pow13_5_mul_t]
  simp only [pow12_41]
  ring

theorem pow13_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow13_4 z * u12 z = pow13_5_q z * f z + pow13_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow13_5_mul_integer z


theorem pow13_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow13_4 z * u12 z = pow13_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_5_mul z


theorem pow13_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u12 z ^ 5 = pow13_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow13_4_pow z hz]
  exact pow13_5_root z hz


theorem pow13_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_5 z * pow13_5 z = pow13_10_q z * f z + pow13_10 z + (41 : R) * pow13_10_mul_t z := by
  simp only [pow13_5, pow13_10_q, f, pow13_10, pow13_10_mul_t]
  
  ring

theorem pow13_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow13_5 z * pow13_5 z = pow13_10_q z * f z + pow13_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow13_10_mul_integer z


theorem pow13_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow13_5 z * pow13_5 z = pow13_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_10_mul z


theorem pow13_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u12 z ^ 10 = pow13_10 z := by
  calc
    _ = u12 z ^ 5 * u12 z ^ 5 := by ring
    _ = pow13_5 z * pow13_5 z := by rw [pow13_5_pow z hz]
    _ = _ := pow13_10_root z hz


theorem pow13_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_10 z * pow13_10 z = pow13_20_q z * f z + pow13_20 z + (41 : R) * pow13_20_mul_t z := by
  simp only [pow13_10, pow13_20_q, f, pow13_20, pow13_20_mul_t]
  
  ring

theorem pow13_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow13_10 z * pow13_10 z = pow13_20_q z * f z + pow13_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow13_20_mul_integer z


theorem pow13_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow13_10 z * pow13_10 z = pow13_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_20_mul z


theorem pow13_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u12 z ^ 20 = pow13_20 z := by
  calc
    _ = u12 z ^ 10 * u12 z ^ 10 := by ring
    _ = pow13_10 z * pow13_10 z := by rw [pow13_10_pow z hz]
    _ = _ := pow13_20_root z hz


theorem pow13_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_20 z * pow13_20 z = pow13_40_q z * f z + pow13_40 z + (41 : R) * pow13_40_mul_t z := by
  simp only [pow13_20, pow13_40_q, f, pow13_40, pow13_40_mul_t]
  
  ring

theorem pow13_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow13_20 z * pow13_20 z = pow13_40_q z * f z + pow13_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow13_40_mul_integer z


theorem pow13_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow13_20 z * pow13_20 z = pow13_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_40_mul z


theorem pow13_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u12 z ^ 40 = pow13_40 z := by
  calc
    _ = u12 z ^ 20 * u12 z ^ 20 := by ring
    _ = pow13_20 z * pow13_20 z := by rw [pow13_20_pow z hz]
    _ = _ := pow13_40_root z hz


theorem pow13_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow13_40 z * u12 z = pow13_41_q z * f z + pow13_41 z + (41 : R) * pow13_41_mul_t z := by
  simp only [pow13_40, u12, pow13_41_q, f, pow13_41, pow13_41_mul_t]
  simp only [pow12_41]
  ring

theorem pow13_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow13_40 z * u12 z = pow13_41_q z * f z + pow13_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow13_41_mul_integer z


theorem pow13_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow13_40 z * u12 z = pow13_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow13_41_mul z


theorem pow13_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u12 z ^ 41 = pow13_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow13_40_pow z hz]
  exact pow13_41_root z hz


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

theorem pow15_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_2 z * pow15_2 z = pow15_4_q z * f z + pow15_4 z + (41 : R) * pow15_4_mul_t z := by
  simp only [pow15_2, pow15_4_q, f, pow15_4, pow15_4_mul_t]
  
  ring

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

theorem bezout10_integer {R : Type*} [CommRing R] (z : R) :
    a10 z * f z + b10 z * (u10 z - z) = g10 z + (41 : R) * bezout10_t z := by
  simp only [a10, b10, f, u10, g10, bezout10_t]
  simp only [pow10_41, pow1_20_q]
  ring

theorem bezout10 {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    a10 z * f z + b10 z * (u10 z - z) = g10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using bezout10_integer z

end DimensionTen.Mod41

section
noncomputable section
open Polynomial
namespace DimensionTen.Mod41


lemma map_f {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (z : R) :
    φ (f z) = f (φ z) := by simp only [f, map_add, map_mul, map_ofNat, map_one]

lemma map_u4 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (z : R) :
    φ (u4 z) = u4 (φ z) := by simp only [u4, pow4_41, map_add, map_mul, map_ofNat]

section Field
variable (k : Type*) [Field k] [CharP k 41]

omit [CharP k 41] in
lemma root_f : f (AdjoinRoot.root (f (X : k[X]))) = 0 := by
  rw [← AdjoinRoot.mk_X, ← map_f]
  exact AdjoinRoot.mk_self

attribute [local instance] OAI.DimensionTen.Mod41.charP_root
lemma divides_four : f (X : k[X]) ∣ X ^ 41 ^ 4 - u4 X := by
  apply AdjoinRoot.mk_eq_zero.mp
  simp only [map_sub, map_pow, map_u4, AdjoinRoot.mk_X]
  rw [iterate4 _ (root_f k), sub_self]

lemma divides_ten : f (X : k[X]) ∣ X ^ 41 ^ 10 - u10 X := by
  apply AdjoinRoot.mk_eq_zero.mp
  simp only [map_sub, map_pow, map_u10, AdjoinRoot.mk_X]
  rw [iterate10 _ (root_f k), sub_self]

lemma coprime_remainder_ten {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    IsCoprime (f z) (u10 z-z) := ⟨a10 z, b10 z, bezout10 z⟩

lemma coprime_four : IsCoprime (f (X : k[X])) (X ^ 41 ^ 4 - X) :=
  coprime_of_equiv_sub_poly (f (X : k[X])) (X ^ 41 ^ 4) (u4 X) X
    (coprime_remainder_four (X : k[X])) (divides_four k)

lemma coprime_ten : IsCoprime (f (X : k[X])) (X ^ 41 ^ 10 - X) :=
  coprime_of_equiv_sub_poly (f (X : k[X])) (X ^ 41 ^ 10) (u10 X) X
    (coprime_remainder_ten (X : k[X])) (divides_ten k)



end Field

end DimensionTen.Mod41

end
end

end

end OAI
end


