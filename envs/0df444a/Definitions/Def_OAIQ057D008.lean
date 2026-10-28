-- Prove2me | Definitions.Def_OAIQ057D008
-- name    : OAIQ057D008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T20:50:10.885602+00:00
-- url     : https://prove2.me/theorems/8c38432a-8b4c-4bdc-944a-b2306c6a963e
-- title:
--   Definitions bundle OAIQ057D008 of the split of OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DimensionTen.exists_channel_fin21`, carved from OpenAI's openai/math development (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 378 declarations of OpenAI's Lean: 2 definitions, 1 instance and 375 theorems. The definitions and types are `OAI.DimensionTen.Mod41.g10`, `OAI.ZeroKey.Explicit.Q`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, lean/OAI/InformationTheory, in whole or in part: `Quantum_DimensionTen_IntegerPolynomials`, `Quantum_DimensionTen_Mod41Model`, `Quantum_DimensionTen_Mod41Powers01`, `Quantum_DimensionTen_Mod41Powers02`, `Quantum_DimensionTen_Mod41Powers03`, `Quantum_DimensionTen_Mod41Powers04`, `Quantum_DimensionTen_Mod41Powers05`, `Quantum_DimensionTen_Mod41Powers06`, `Quantum_DimensionTen_Mod41Powers07`, `Quantum_DimensionTen_Mod41Powers08`, `Quantum_DimensionTen_Mod41Powers09`, `Quantum_DimensionTen_Mod41Result`, `Quantum_DimensionTen_PolynomialData`, `SecretKey_Model`.
--
--   **Imports.** It imports the bundles `OAIQ057D000`, `OAIQ057D001`, `OAIQ057D002`, `OAIQ057D003` and `OAIQ057D006` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ057D011`.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis, lean/OAI/InformationTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ057D000
import Definitions.Def_OAIQ057D001
import Definitions.Def_OAIQ057D002
import Definitions.Def_OAIQ057D003
import Definitions.Def_OAIQ057D006

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Model
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41

theorem initial {R : Type*} [CommRing R] (z : R) : z ^ (41 ^ 0) = u0 z := by simp [u0]

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Powers01
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41

theorem pow1_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u0 z * u0 z = pow1_2_q z * f z + pow1_2 z + (41 : R) * pow1_2_mul_t z := by
  simp only [u0, pow1_2_q, f, pow1_2, pow1_2_mul_t]
  
  ring

theorem pow1_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u0 z * u0 z = pow1_2_q z * f z + pow1_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow1_2_mul_integer z


theorem pow1_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u0 z * u0 z = pow1_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_2_mul z


theorem pow1_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u0 z ^ 2 = pow1_2 z := by
  calc
    _ = u0 z ^ 1 * u0 z ^ 1 := by ring
    _ = u0 z * u0 z := by simp only [pow_one]
    _ = _ := pow1_2_root z hz


theorem pow1_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_2 z * pow1_2 z = pow1_4_q z * f z + pow1_4 z + (41 : R) * pow1_4_mul_t z := by
  simp only [pow1_2, pow1_4_q, f, pow1_4, pow1_4_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow1_2 z * pow1_2 z = pow1_4_q z * f z + pow1_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow1_4_mul_integer z


theorem pow1_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow1_2 z * pow1_2 z = pow1_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_4_mul z


theorem pow1_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u0 z ^ 4 = pow1_4 z := by
  calc
    _ = u0 z ^ 2 * u0 z ^ 2 := by ring
    _ = pow1_2 z * pow1_2 z := by rw [pow1_2_pow z hz]
    _ = _ := pow1_4_root z hz


theorem pow1_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_4 z * u0 z = pow1_5_q z * f z + pow1_5 z + (41 : R) * pow1_5_mul_t z := by
  simp only [pow1_4, u0, pow1_5_q, f, pow1_5, pow1_5_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow1_4 z * u0 z = pow1_5_q z * f z + pow1_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow1_5_mul_integer z


theorem pow1_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow1_4 z * u0 z = pow1_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_5_mul z


theorem pow1_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u0 z ^ 5 = pow1_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow1_4_pow z hz]
  exact pow1_5_root z hz


theorem pow1_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_5 z * pow1_5 z = pow1_10_q z * f z + pow1_10 z + (41 : R) * pow1_10_mul_t z := by
  simp only [pow1_5, pow1_10_q, f, pow1_10, pow1_10_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow1_5 z * pow1_5 z = pow1_10_q z * f z + pow1_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow1_10_mul_integer z


theorem pow1_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow1_5 z * pow1_5 z = pow1_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_10_mul z


theorem pow1_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u0 z ^ 10 = pow1_10 z := by
  calc
    _ = u0 z ^ 5 * u0 z ^ 5 := by ring
    _ = pow1_5 z * pow1_5 z := by rw [pow1_5_pow z hz]
    _ = _ := pow1_10_root z hz


theorem pow1_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_10 z * pow1_10 z = pow1_20_q z * f z + pow1_20 z + (41 : R) * pow1_20_mul_t z := by
  simp only [pow1_10, pow1_20_q, f, pow1_20, pow1_20_mul_t]
  
  ring

theorem pow1_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow1_10 z * pow1_10 z = pow1_20_q z * f z + pow1_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow1_20_mul_integer z


theorem pow1_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow1_10 z * pow1_10 z = pow1_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_20_mul z


theorem pow1_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u0 z ^ 20 = pow1_20 z := by
  calc
    _ = u0 z ^ 10 * u0 z ^ 10 := by ring
    _ = pow1_10 z * pow1_10 z := by rw [pow1_10_pow z hz]
    _ = _ := pow1_20_root z hz


theorem pow1_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_20 z * pow1_20 z = pow1_40_q z * f z + pow1_40 z + (41 : R) * pow1_40_mul_t z := by
  simp only [pow1_20, pow1_40_q, f, pow1_40, pow1_40_mul_t]
  
  ring

theorem pow1_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow1_20 z * pow1_20 z = pow1_40_q z * f z + pow1_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow1_40_mul_integer z


theorem pow1_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow1_20 z * pow1_20 z = pow1_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_40_mul z


theorem pow1_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u0 z ^ 40 = pow1_40 z := by
  calc
    _ = u0 z ^ 20 * u0 z ^ 20 := by ring
    _ = pow1_20 z * pow1_20 z := by rw [pow1_20_pow z hz]
    _ = _ := pow1_40_root z hz


theorem pow1_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_40 z * u0 z = pow1_41_q z * f z + pow1_41 z + (41 : R) * pow1_41_mul_t z := by
  simp only [pow1_40, u0, pow1_41_q, f, pow1_41, pow1_41_mul_t]
  
  ring

theorem pow1_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow1_40 z * u0 z = pow1_41_q z * f z + pow1_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow1_41_mul_integer z


theorem pow1_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow1_40 z * u0 z = pow1_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_41_mul z


theorem pow1_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u0 z ^ 41 = pow1_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow1_40_pow z hz]
  exact pow1_41_root z hz


theorem iterate1 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 1) = u1 z := by
  calc
    _ = (z ^ (41 ^ 0)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u0 z ^ 41 := congrArg (fun x : R => x ^ 41) (initial z )
    _ = _ := pow1_41_pow z hz


theorem pow2_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u1 z * u1 z = pow2_2_q z * f z + pow2_2 z + (41 : R) * pow2_2_mul_t z := by
  simp only [u1, pow2_2_q, f, pow2_2, pow2_2_mul_t]
  simp only [pow1_41]
  ring

theorem pow2_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u1 z * u1 z = pow2_2_q z * f z + pow2_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow2_2_mul_integer z


theorem pow2_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u1 z * u1 z = pow2_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_2_mul z


theorem pow2_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u1 z ^ 2 = pow2_2 z := by
  calc
    _ = u1 z ^ 1 * u1 z ^ 1 := by ring
    _ = u1 z * u1 z := by simp only [pow_one]
    _ = _ := pow2_2_root z hz


theorem pow2_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u1 z ^ 4 = pow2_4 z := by
  calc
    _ = u1 z ^ 2 * u1 z ^ 2 := by ring
    _ = pow2_2 z * pow2_2 z := by rw [pow2_2_pow z hz]
    _ = _ := pow2_4_root z hz


theorem pow2_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_4 z * u1 z = pow2_5_q z * f z + pow2_5 z + (41 : R) * pow2_5_mul_t z := by
  simp only [pow2_4, u1, pow2_5_q, f, pow2_5, pow2_5_mul_t]
  simp only [pow1_41]
  ring

theorem pow2_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow2_4 z * u1 z = pow2_5_q z * f z + pow2_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow2_5_mul_integer z


theorem pow2_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow2_4 z * u1 z = pow2_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_5_mul z


theorem pow2_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u1 z ^ 5 = pow2_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow2_4_pow z hz]
  exact pow2_5_root z hz


theorem pow2_10_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_5 z * pow2_5 z = pow2_10_q z * f z + pow2_10 z + (41 : R) * pow2_10_mul_t z := by
  simp only [pow2_5, pow2_10_q, f, pow2_10, pow2_10_mul_t]
  
  ring

theorem pow2_10_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow2_5 z * pow2_5 z = pow2_10_q z * f z + pow2_10 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow2_10_mul_integer z


theorem pow2_10_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow2_5 z * pow2_5 z = pow2_10 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_10_mul z


theorem pow2_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u1 z ^ 10 = pow2_10 z := by
  calc
    _ = u1 z ^ 5 * u1 z ^ 5 := by ring
    _ = pow2_5 z * pow2_5 z := by rw [pow2_5_pow z hz]
    _ = _ := pow2_10_root z hz


theorem pow2_20_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_10 z * pow2_10 z = pow2_20_q z * f z + pow2_20 z + (41 : R) * pow2_20_mul_t z := by
  simp only [pow2_10, pow2_20_q, f, pow2_20, pow2_20_mul_t]
  
  ring

theorem pow2_20_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow2_10 z * pow2_10 z = pow2_20_q z * f z + pow2_20 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow2_20_mul_integer z


theorem pow2_20_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow2_10 z * pow2_10 z = pow2_20 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_20_mul z


theorem pow2_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u1 z ^ 20 = pow2_20 z := by
  calc
    _ = u1 z ^ 10 * u1 z ^ 10 := by ring
    _ = pow2_10 z * pow2_10 z := by rw [pow2_10_pow z hz]
    _ = _ := pow2_20_root z hz


theorem pow2_40_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_20 z * pow2_20 z = pow2_40_q z * f z + pow2_40 z + (41 : R) * pow2_40_mul_t z := by
  simp only [pow2_20, pow2_40_q, f, pow2_40, pow2_40_mul_t]
  
  ring

theorem pow2_40_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow2_20 z * pow2_20 z = pow2_40_q z * f z + pow2_40 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow2_40_mul_integer z


theorem pow2_40_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow2_20 z * pow2_20 z = pow2_40 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_40_mul z


theorem pow2_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u1 z ^ 40 = pow2_40 z := by
  calc
    _ = u1 z ^ 20 * u1 z ^ 20 := by ring
    _ = pow2_20 z * pow2_20 z := by rw [pow2_20_pow z hz]
    _ = _ := pow2_40_root z hz


theorem pow2_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow2_40 z * u1 z = pow2_41_q z * f z + pow2_41 z + (41 : R) * pow2_41_mul_t z := by
  simp only [pow2_40, u1, pow2_41_q, f, pow2_41, pow2_41_mul_t]
  simp only [pow1_41]
  ring

theorem pow2_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow2_40 z * u1 z = pow2_41_q z * f z + pow2_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow2_41_mul_integer z


theorem pow2_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow2_40 z * u1 z = pow2_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow2_41_mul z


theorem pow2_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u1 z ^ 41 = pow2_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow2_40_pow z hz]
  exact pow2_41_root z hz


theorem iterate2 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 2) = u2 z := by
  calc
    _ = (z ^ (41 ^ 1)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u1 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate1 z hz)
    _ = _ := pow2_41_pow z hz

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Powers02
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41

theorem pow3_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u2 z * u2 z = pow3_2_q z * f z + pow3_2 z + (41 : R) * pow3_2_mul_t z := by
  simp only [u2, pow3_2_q, f, pow3_2, pow3_2_mul_t]
  simp only [pow2_41]
  ring

theorem pow3_2_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    u2 z * u2 z = pow3_2_q z * f z + pow3_2 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow3_2_mul_integer z


theorem pow3_2_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u2 z * u2 z = pow3_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_2_mul z


theorem pow3_2_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u2 z ^ 2 = pow3_2 z := by
  calc
    _ = u2 z ^ 1 * u2 z ^ 1 := by ring
    _ = u2 z * u2 z := by simp only [pow_one]
    _ = _ := pow3_2_root z hz


theorem pow3_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u2 z ^ 4 = pow3_4 z := by
  calc
    _ = u2 z ^ 2 * u2 z ^ 2 := by ring
    _ = pow3_2 z * pow3_2 z := by rw [pow3_2_pow z hz]
    _ = _ := pow3_4_root z hz


theorem pow3_5_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_4 z * u2 z = pow3_5_q z * f z + pow3_5 z + (41 : R) * pow3_5_mul_t z := by
  simp only [pow3_4, u2, pow3_5_q, f, pow3_5, pow3_5_mul_t]
  simp only [pow2_41]
  ring

theorem pow3_5_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow3_4 z * u2 z = pow3_5_q z * f z + pow3_5 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow3_5_mul_integer z


theorem pow3_5_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow3_4 z * u2 z = pow3_5 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_5_mul z


theorem pow3_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u2 z ^ 5 = pow3_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow3_4_pow z hz]
  exact pow3_5_root z hz


theorem pow3_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u2 z ^ 10 = pow3_10 z := by
  calc
    _ = u2 z ^ 5 * u2 z ^ 5 := by ring
    _ = pow3_5 z * pow3_5 z := by rw [pow3_5_pow z hz]
    _ = _ := pow3_10_root z hz


theorem pow3_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u2 z ^ 20 = pow3_20 z := by
  calc
    _ = u2 z ^ 10 * u2 z ^ 10 := by ring
    _ = pow3_10 z * pow3_10 z := by rw [pow3_10_pow z hz]
    _ = _ := pow3_20_root z hz


theorem pow3_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u2 z ^ 40 = pow3_40 z := by
  calc
    _ = u2 z ^ 20 * u2 z ^ 20 := by ring
    _ = pow3_20 z * pow3_20 z := by rw [pow3_20_pow z hz]
    _ = _ := pow3_40_root z hz


theorem pow3_41_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow3_40 z * u2 z = pow3_41_q z * f z + pow3_41 z + (41 : R) * pow3_41_mul_t z := by
  simp only [pow3_40, u2, pow3_41_q, f, pow3_41, pow3_41_mul_t]
  simp only [pow2_41]
  ring

theorem pow3_41_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow3_40 z * u2 z = pow3_41_q z * f z + pow3_41 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow3_41_mul_integer z


theorem pow3_41_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow3_40 z * u2 z = pow3_41 z := by
  simpa only [hz, mul_zero, zero_add] using pow3_41_mul z


theorem pow3_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u2 z ^ 41 = pow3_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow3_40_pow z hz]
  exact pow3_41_root z hz


theorem iterate3 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 3) = u3 z := by
  calc
    _ = (z ^ (41 ^ 2)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u2 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate2 z hz)
    _ = _ := pow3_41_pow z hz


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
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Powers03
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


theorem pow5_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u4 z ^ 10 = pow5_10 z := by
  calc
    _ = u4 z ^ 5 * u4 z ^ 5 := by ring
    _ = pow5_5 z * pow5_5 z := by rw [pow5_5_pow z hz]
    _ = _ := pow5_10_root z hz


theorem pow5_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u4 z ^ 20 = pow5_20 z := by
  calc
    _ = u4 z ^ 10 * u4 z ^ 10 := by ring
    _ = pow5_10 z * pow5_10 z := by rw [pow5_10_pow z hz]
    _ = _ := pow5_20_root z hz


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
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Powers04
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41

theorem iterate7 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 7) = u7 z := by
  calc
    _ = (z ^ (41 ^ 6)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u6 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate6 z hz)
    _ = _ := pow7_41_pow z hz


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
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Powers05
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
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Powers06
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
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Powers07
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


theorem iterate13 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 13) = u13 z := by
  calc
    _ = (z ^ (41 ^ 12)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u12 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate12 z hz)
    _ = _ := pow13_41_pow z hz


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


theorem iterate14 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 14) = u14 z := by
  calc
    _ = (z ^ (41 ^ 13)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u13 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate13 z hz)
    _ = _ := pow14_41_pow z hz

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Powers08
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


theorem pow15_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow15_2 z * pow15_2 z = pow15_4_q z * f z + pow15_4 z + (41 : R) * pow15_4_mul_t z := by
  simp only [pow15_2, pow15_4_q, f, pow15_4, pow15_4_mul_t]
  
  ring

theorem pow15_4_mul {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    pow15_2 z * pow15_2 z = pow15_4_q z * f z + pow15_4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using pow15_4_mul_integer z


theorem pow15_4_root {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : pow15_2 z * pow15_2 z = pow15_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow15_4_mul z


theorem pow15_4_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u14 z ^ 4 = pow15_4 z := by
  calc
    _ = u14 z ^ 2 * u14 z ^ 2 := by ring
    _ = pow15_2 z * pow15_2 z := by rw [pow15_2_pow z hz]
    _ = _ := pow15_4_root z hz


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


theorem pow15_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u14 z ^ 5 = pow15_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow15_4_pow z hz]
  exact pow15_5_root z hz


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


theorem pow15_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u14 z ^ 10 = pow15_10 z := by
  calc
    _ = u14 z ^ 5 * u14 z ^ 5 := by ring
    _ = pow15_5 z * pow15_5 z := by rw [pow15_5_pow z hz]
    _ = _ := pow15_10_root z hz


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


theorem pow15_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u14 z ^ 20 = pow15_20 z := by
  calc
    _ = u14 z ^ 10 * u14 z ^ 10 := by ring
    _ = pow15_10 z * pow15_10 z := by rw [pow15_10_pow z hz]
    _ = _ := pow15_20_root z hz


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


theorem pow15_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u14 z ^ 40 = pow15_40 z := by
  calc
    _ = u14 z ^ 20 * u14 z ^ 20 := by ring
    _ = pow15_20 z * pow15_20 z := by rw [pow15_20_pow z hz]
    _ = _ := pow15_40_root z hz


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


theorem pow15_41_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u14 z ^ 41 = pow15_41 z := by
  rw [show 41 = 40 + 1 by rfl, pow_succ, pow15_40_pow z hz]
  exact pow15_41_root z hz


theorem iterate15 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 15) = u15 z := by
  calc
    _ = (z ^ (41 ^ 14)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u14 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate14 z hz)
    _ = _ := pow15_41_pow z hz


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


theorem iterate16 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 16) = u16 z := by
  calc
    _ = (z ^ (41 ^ 15)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u15 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate15 z hz)
    _ = _ := pow16_41_pow z hz

end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Powers09
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

theorem bezout4_integer {R : Type*} [CommRing R] (z : R) :
    a4 z * f z + b4 z * (u4 z - z) = g4 z + (41 : R) * bezout4_t z := by
  simp only [a4, b4, f, u4, g4, bezout4_t]
  simp only [pow4_41, pow1_20_q]
  ring

theorem bezout4 {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    a4 z * f z + b4 z * (u4 z - z) = g4 z := by
  have h : (41 : R) = 0 := CharP.cast_eq_zero R 41
  simpa only [h, zero_mul, add_zero] using bezout4_integer z


abbrev g10 {R : Type*} [CommRing R] (z : R) : R := pow1_20_q z

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

lemma map_u4 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (z : R) :
    φ (u4 z) = u4 (φ z) := by simp only [u4, pow4_41, map_add, map_mul, map_ofNat]
lemma map_u10 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (z : R) :
    φ (u10 z) = u10 (φ z) := by simp only [u10, pow10_41, map_add, map_mul, map_ofNat, map_one, map_zero]

lemma degree_f {R : Type*} [CommRing R] [Nontrivial R] :
    (f (X : R[X])).IsMonicOfDegree 20 := by
  unfold f
  repeat' apply horner_monic_degree
  exact ⟨natDegree_one, monic_one⟩

section Field
variable (k : Type*) [Field k] [CharP k 41]

local instance nontrivial_root : Nontrivial (AdjoinRoot (f (X : k[X]))) :=
  AdjoinRoot.nontrivial _ (by
    rw [degree_eq_natDegree degree_f.monic.ne_zero, degree_f.natDegree_eq]
    norm_num)

local instance charP_root : CharP (AdjoinRoot (f (X : k[X]))) 41 :=
  charP_of_injective_algebraMap (algebraMap k _).injective 41

lemma divides_four : f (X : k[X]) ∣ X ^ 41 ^ 4 - u4 X := by
  apply AdjoinRoot.mk_eq_zero.mp
  simp only [map_sub, map_pow, map_u4, AdjoinRoot.mk_X]
  rw [iterate4 _ (root_f k), sub_self]

lemma divides_ten : f (X : k[X]) ∣ X ^ 41 ^ 10 - u10 X := by
  apply AdjoinRoot.mk_eq_zero.mp
  simp only [map_sub, map_pow, map_u10, AdjoinRoot.mk_X]
  rw [iterate10 _ (root_f k), sub_self]

lemma coprime_remainder_four {R : Type*} [CommRing R] [CharP R 41] (z : R) :
    IsCoprime (f z) (u4 z-z) := ⟨a4 z, b4 z, bezout4 z⟩

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

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_IntegerPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Polynomial Matrix
namespace DimensionTen.Border

lemma F_reduction_41 : F.map (Int.castRingHom (ZMod 41)) = Mod41.f X := by
  rw [F_map]
  simp only [FP, ← C_eq_intCast, coef_41_0, coef_41_1, coef_41_2, coef_41_3, coef_41_4, coef_41_5, coef_41_6, coef_41_7, coef_41_8, coef_41_9, coef_41_10, coef_41_11, coef_41_12, coef_41_13, coef_41_14, coef_41_15, coef_41_16, coef_41_17, coef_41_18, coef_41_19,
    map_ofNat, map_one, Mod41.f, mul_one]

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_PolynomialData
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

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.SecretKey_Model
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ZeroKey

open Matrix

open scoped MatrixOrder ComplexOrder Kronecker

namespace Explicit

section

@[irreducible] def Q : ℕ := b^3

universe v1312_0 v1312_1

universe v1552_0

universe v1965_0

universe v1995_0

open Finset

end

universe v2431_0

universe v2545_0

end Explicit

open scoped MatrixOrder ComplexOrder Kronecker

open Matrix

universe v2604_0 v2604_1

open Finset

open scoped ComplexOrder MatrixOrder Kronecker

open Matrix

end ZeroKey

namespace ZeroKey

section

open Matrix MeasureTheory ProbabilityTheory Filter

section

universe u

attribute [instance] QuantumMemory.additive QuantumMemory.complexModule QuantumMemory.unit QuantumMemory.order

instance instCoeSortQuantumMemoryType : CoeSort QuantumMemory (Type u) := ⟨QuantumMemory.Carrier⟩

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


