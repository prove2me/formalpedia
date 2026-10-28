-- Prove2me | Definitions.Def_OAIQ057D009
-- name    : OAIQ057D009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T20:58:04.53967+00:00
-- url     : https://prove2.me/theorems/5e8e66be-b69e-4f77-85c5-795c43f19af2
-- title:
--   Definitions bundle OAIQ057D009 of the split of OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DimensionTen.exists_channel_fin21`, carved from OpenAI's openai/math development (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 263 declarations of OpenAI's Lean: 50 definitions, 2 instances and 211 theorems. The definitions and types are `OAI.DimensionTen.Border.K`, `OAI.DimensionTen.Border.NB`, `OAI.DimensionTen.Border.cofactorKernel`, `OAI.DimensionTen.Border.minor`, `OAI.DimensionTen.Mod131.pow1_4_q`, `OAI.DimensionTen.Mod131.pow1_8_q`, `OAI.DimensionTen.Mod131.u10`, `OAI.DimensionTen.Mod131.u11`, `OAI.DimensionTen.Mod131.u12`, `OAI.DimensionTen.Mod131.u13`, `OAI.DimensionTen.Mod131.u15`, `OAI.DimensionTen.Mod131.u16`, `OAI.DimensionTen.Mod131.u17`, `OAI.DimensionTen.Mod131.u2`, `OAI.DimensionTen.Mod131.u3`, `OAI.DimensionTen.Mod131.u4`, `OAI.DimensionTen.Mod131.u5`, `OAI.DimensionTen.Mod131.u6`, `OAI.DimensionTen.Mod131.u7`, `OAI.DimensionTen.Mod131.u8`, `OAI.DimensionTen.Mod131.u9`, `OAI.DimensionTen.Mod139.pow1_16_q`, `OAI.DimensionTen.Mod139.pow1_17_q`, `OAI.DimensionTen.Mod139.pow1_4_q`, `OAI.DimensionTen.Mod139.pow1_8_q`, `OAI.DimensionTen.Mod139.u10`, `OAI.DimensionTen.Mod139.u11`, `OAI.DimensionTen.Mod139.u12`, `OAI.DimensionTen.Mod139.u13`, `OAI.DimensionTen.Mod139.u14`, `OAI.DimensionTen.Mod139.u15`, `OAI.DimensionTen.Mod139.u16`, `OAI.DimensionTen.Mod139.u17`, `OAI.DimensionTen.PPT`, `OAI.DimensionTen.asLinearMap`, `OAI.DimensionTen.blocks`, `OAI.DimensionTen.complementaryKraus`, `OAI.DimensionTen.complementaryMap`, `OAI.DimensionTen.exteriorKraus`, `OAI.DimensionTen.exteriorMap` and 10 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, lean/OAI/InformationTheory, in whole or in part: `Quantum_DimensionTen_Annihilator`, `Quantum_DimensionTen_BorderData`, `Quantum_DimensionTen_BorderField`, `Quantum_DimensionTen_Channel`, `Quantum_DimensionTen_ChoiPairing`, `Quantum_DimensionTen_Cofactors`, `Quantum_DimensionTen_ExteriorMaps`, `Quantum_DimensionTen_GaloisField`, `Quantum_DimensionTen_IntegerPolynomials`, `Quantum_DimensionTen_Kraus`, `Quantum_DimensionTen_MinorData`, `Quantum_DimensionTen_Mod131Powers01`, `Quantum_DimensionTen_Mod131Powers02`, `Quantum_DimensionTen_Mod131Powers03`, `Quantum_DimensionTen_Mod131Powers04`, `Quantum_DimensionTen_Mod131Powers05`, `Quantum_DimensionTen_Mod131Powers06`, `Quantum_DimensionTen_Mod131Powers07`, `Quantum_DimensionTen_Mod131Powers08`, `Quantum_DimensionTen_Mod131Powers09`, `Quantum_DimensionTen_Mod139Powers01`, `Quantum_DimensionTen_Mod139Powers05`, `Quantum_DimensionTen_Mod139Powers06`, `Quantum_DimensionTen_Mod139Powers07`, `Quantum_DimensionTen_Mod139Powers08`, `Quantum_DimensionTen_Mod139Powers09`, `Quantum_DimensionTen_Mod41Powers09`, `Quantum_DimensionTen_Mod41Powers10`, `Quantum_DimensionTen_NormalizedMatrices`, `Quantum_DimensionTen_PencilKraus`, `Quantum_DimensionTen_PencilModel`, `Quantum_DimensionTen_PolynomialData`.
--
--   **Imports.** It imports the published bundle `Def_DimensionTenChannel`; the bundles `OAIQ057D000`, `OAIQ057D001`, `OAIQ057D002`, `OAIQ057D003`, `OAIQ057D004`, `OAIQ057D005`, `OAIQ057D006` and `OAIQ057D007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ057D011` and `OAIQ057D012`; the statements `OAI_DimensionTen_Mod131_iterate13`, `OAI.DimensionTen.Mod131.iterate13_s2`, `OAI_DimensionTen_Mod139_iterate14` and `OAI.DimensionTen.Mod139.iterate14_s2`; the proofs of `OAI_DimensionTen_Mod131_iterate13`, `OAI.DimensionTen.Mod131.iterate13_s2`, `OAI_DimensionTen_Mod139_iterate14`, `OAI.DimensionTen.Mod139.iterate14_s2`, `OAI_DimensionTen_fixed_mod131`, `OAI.DimensionTen.fixed_mod131_s2`, `OAI_DimensionTen_fixed_mod139`, `OAI.DimensionTen.fixed_mod139_s2`, `OAI_DimensionTen_pow_mod139` and `OAI.DimensionTen.pow_mod139_s2`.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis, lean/OAI/InformationTheory at commit adc7f12

import Mathlib
import Definitions.Def_DimensionTenChannel
import Definitions.Def_OAIQ057D000
import Definitions.Def_OAIQ057D001
import Definitions.Def_OAIQ057D002
import Definitions.Def_OAIQ057D003
import Definitions.Def_OAIQ057D004
import Definitions.Def_OAIQ057D005
import Definitions.Def_OAIQ057D006
import Definitions.Def_OAIQ057D007

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Powers01
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131

abbrev pow1_4_q {R : Type*} [CommRing R] (z : R) : R := pow1_2_q z

abbrev pow1_8_q {R : Type*} [CommRing R] (z : R) : R := pow1_2_q z


abbrev u2 {R : Type*} [CommRing R] (z : R) : R := pow2_131 z

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Powers02
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131


abbrev u3 {R : Type*} [CommRing R] (z : R) : R := pow3_131 z


abbrev u4 {R : Type*} [CommRing R] (z : R) : R := pow4_131 z

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Powers03
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131


abbrev u5 {R : Type*} [CommRing R] (z : R) : R := pow5_131 z


abbrev u6 {R : Type*} [CommRing R] (z : R) : R := pow6_131 z

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Powers04
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131


abbrev u7 {R : Type*} [CommRing R] (z : R) : R := pow7_131 z


abbrev u8 {R : Type*} [CommRing R] (z : R) : R := pow8_131 z

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Powers05
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131


abbrev u9 {R : Type*} [CommRing R] (z : R) : R := pow9_131 z


abbrev u10 {R : Type*} [CommRing R] (z : R) : R := pow10_131 z

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Powers06
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131


abbrev u11 {R : Type*} [CommRing R] (z : R) : R := pow11_131 z


abbrev u12 {R : Type*} [CommRing R] (z : R) : R := pow12_131 z

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Powers07
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131


abbrev u13 {R : Type*} [CommRing R] (z : R) : R := pow13_131 z

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Powers08
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131


abbrev u15 {R : Type*} [CommRing R] (z : R) : R := pow15_131 z


abbrev u16 {R : Type*} [CommRing R] (z : R) : R := pow16_131 z

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod131Powers09
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod131


abbrev u17 {R : Type*} [CommRing R] (z : R) : R := pow17_131 z

end DimensionTen.Mod131

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Powers09
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod41

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
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod41Powers10
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
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


end DimensionTen.Mod41

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_IntegerPolynomials
attribute [-instance] _root_.OAI.ZeroKey.matrixMeasurableSpace
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
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_BorderData
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

lemma commute_01_row0 : ∀ k : Fin 20, (B0 * B1) 0 k = (B1 * B0) 0 k := by decide +kernel
lemma commute_01_row1 : ∀ k : Fin 20, (B0 * B1) 1 k = (B1 * B0) 1 k := by decide +kernel
lemma commute_01_row2 : ∀ k : Fin 20, (B0 * B1) 2 k = (B1 * B0) 2 k := by decide +kernel
lemma commute_01_row3 : ∀ k : Fin 20, (B0 * B1) 3 k = (B1 * B0) 3 k := by decide +kernel
lemma commute_01_row4 : ∀ k : Fin 20, (B0 * B1) 4 k = (B1 * B0) 4 k := by decide +kernel
lemma commute_01_row5 : ∀ k : Fin 20, (B0 * B1) 5 k = (B1 * B0) 5 k := by decide +kernel
lemma commute_01_row6 : ∀ k : Fin 20, (B0 * B1) 6 k = (B1 * B0) 6 k := by decide +kernel
lemma commute_01_row7 : ∀ k : Fin 20, (B0 * B1) 7 k = (B1 * B0) 7 k := by decide +kernel
lemma commute_01_row8 : ∀ k : Fin 20, (B0 * B1) 8 k = (B1 * B0) 8 k := by decide +kernel
lemma commute_01_row9 : ∀ k : Fin 20, (B0 * B1) 9 k = (B1 * B0) 9 k := by decide +kernel
lemma commute_01_row10 : ∀ k : Fin 20, (B0 * B1) 10 k = (B1 * B0) 10 k := by decide +kernel
lemma commute_01_row11 : ∀ k : Fin 20, (B0 * B1) 11 k = (B1 * B0) 11 k := by decide +kernel
lemma commute_01_row12 : ∀ k : Fin 20, (B0 * B1) 12 k = (B1 * B0) 12 k := by decide +kernel
lemma commute_01_row13 : ∀ k : Fin 20, (B0 * B1) 13 k = (B1 * B0) 13 k := by decide +kernel
lemma commute_01_row14 : ∀ k : Fin 20, (B0 * B1) 14 k = (B1 * B0) 14 k := by decide +kernel
lemma commute_01_row15 : ∀ k : Fin 20, (B0 * B1) 15 k = (B1 * B0) 15 k := by decide +kernel
lemma commute_01_row16 : ∀ k : Fin 20, (B0 * B1) 16 k = (B1 * B0) 16 k := by decide +kernel
lemma commute_01_row17 : ∀ k : Fin 20, (B0 * B1) 17 k = (B1 * B0) 17 k := by decide +kernel
lemma commute_01_row18 : ∀ k : Fin 20, (B0 * B1) 18 k = (B1 * B0) 18 k := by decide +kernel
lemma commute_01_row19 : ∀ k : Fin 20, (B0 * B1) 19 k = (B1 * B0) 19 k := by decide +kernel
lemma commute_01 : B0 * B1 = B1 * B0 := by
  ext i j
  fin_cases i
  · exact commute_01_row0 j
  · exact commute_01_row1 j
  · exact commute_01_row2 j
  · exact commute_01_row3 j
  · exact commute_01_row4 j
  · exact commute_01_row5 j
  · exact commute_01_row6 j
  · exact commute_01_row7 j
  · exact commute_01_row8 j
  · exact commute_01_row9 j
  · exact commute_01_row10 j
  · exact commute_01_row11 j
  · exact commute_01_row12 j
  · exact commute_01_row13 j
  · exact commute_01_row14 j
  · exact commute_01_row15 j
  · exact commute_01_row16 j
  · exact commute_01_row17 j
  · exact commute_01_row18 j
  · exact commute_01_row19 j

lemma commute_02_row0 : ∀ k : Fin 20, (B0 * B2) 0 k = (B2 * B0) 0 k := by decide +kernel
lemma commute_02_row1 : ∀ k : Fin 20, (B0 * B2) 1 k = (B2 * B0) 1 k := by decide +kernel
lemma commute_02_row2 : ∀ k : Fin 20, (B0 * B2) 2 k = (B2 * B0) 2 k := by decide +kernel
lemma commute_02_row3 : ∀ k : Fin 20, (B0 * B2) 3 k = (B2 * B0) 3 k := by decide +kernel
lemma commute_02_row4 : ∀ k : Fin 20, (B0 * B2) 4 k = (B2 * B0) 4 k := by decide +kernel
lemma commute_02_row5 : ∀ k : Fin 20, (B0 * B2) 5 k = (B2 * B0) 5 k := by decide +kernel
lemma commute_02_row6 : ∀ k : Fin 20, (B0 * B2) 6 k = (B2 * B0) 6 k := by decide +kernel
lemma commute_02_row7 : ∀ k : Fin 20, (B0 * B2) 7 k = (B2 * B0) 7 k := by decide +kernel
lemma commute_02_row8 : ∀ k : Fin 20, (B0 * B2) 8 k = (B2 * B0) 8 k := by decide +kernel
lemma commute_02_row9 : ∀ k : Fin 20, (B0 * B2) 9 k = (B2 * B0) 9 k := by decide +kernel
lemma commute_02_row10 : ∀ k : Fin 20, (B0 * B2) 10 k = (B2 * B0) 10 k := by decide +kernel
lemma commute_02_row11 : ∀ k : Fin 20, (B0 * B2) 11 k = (B2 * B0) 11 k := by decide +kernel
lemma commute_02_row12 : ∀ k : Fin 20, (B0 * B2) 12 k = (B2 * B0) 12 k := by decide +kernel
lemma commute_02_row13 : ∀ k : Fin 20, (B0 * B2) 13 k = (B2 * B0) 13 k := by decide +kernel
lemma commute_02_row14 : ∀ k : Fin 20, (B0 * B2) 14 k = (B2 * B0) 14 k := by decide +kernel
lemma commute_02_row15 : ∀ k : Fin 20, (B0 * B2) 15 k = (B2 * B0) 15 k := by decide +kernel
lemma commute_02_row16 : ∀ k : Fin 20, (B0 * B2) 16 k = (B2 * B0) 16 k := by decide +kernel
lemma commute_02_row17 : ∀ k : Fin 20, (B0 * B2) 17 k = (B2 * B0) 17 k := by decide +kernel
lemma commute_02_row18 : ∀ k : Fin 20, (B0 * B2) 18 k = (B2 * B0) 18 k := by decide +kernel
lemma commute_02_row19 : ∀ k : Fin 20, (B0 * B2) 19 k = (B2 * B0) 19 k := by decide +kernel
lemma commute_02 : B0 * B2 = B2 * B0 := by
  ext i j
  fin_cases i
  · exact commute_02_row0 j
  · exact commute_02_row1 j
  · exact commute_02_row2 j
  · exact commute_02_row3 j
  · exact commute_02_row4 j
  · exact commute_02_row5 j
  · exact commute_02_row6 j
  · exact commute_02_row7 j
  · exact commute_02_row8 j
  · exact commute_02_row9 j
  · exact commute_02_row10 j
  · exact commute_02_row11 j
  · exact commute_02_row12 j
  · exact commute_02_row13 j
  · exact commute_02_row14 j
  · exact commute_02_row15 j
  · exact commute_02_row16 j
  · exact commute_02_row17 j
  · exact commute_02_row18 j
  · exact commute_02_row19 j

lemma commute_12_row0 : ∀ k : Fin 20, (B1 * B2) 0 k = (B2 * B1) 0 k := by decide +kernel
lemma commute_12_row1 : ∀ k : Fin 20, (B1 * B2) 1 k = (B2 * B1) 1 k := by decide +kernel
lemma commute_12_row2 : ∀ k : Fin 20, (B1 * B2) 2 k = (B2 * B1) 2 k := by decide +kernel
lemma commute_12_row3 : ∀ k : Fin 20, (B1 * B2) 3 k = (B2 * B1) 3 k := by decide +kernel
lemma commute_12_row4 : ∀ k : Fin 20, (B1 * B2) 4 k = (B2 * B1) 4 k := by decide +kernel
lemma commute_12_row5 : ∀ k : Fin 20, (B1 * B2) 5 k = (B2 * B1) 5 k := by decide +kernel
lemma commute_12_row6 : ∀ k : Fin 20, (B1 * B2) 6 k = (B2 * B1) 6 k := by decide +kernel
lemma commute_12_row7 : ∀ k : Fin 20, (B1 * B2) 7 k = (B2 * B1) 7 k := by decide +kernel
lemma commute_12_row8 : ∀ k : Fin 20, (B1 * B2) 8 k = (B2 * B1) 8 k := by decide +kernel
lemma commute_12_row9 : ∀ k : Fin 20, (B1 * B2) 9 k = (B2 * B1) 9 k := by decide +kernel
lemma commute_12_row10 : ∀ k : Fin 20, (B1 * B2) 10 k = (B2 * B1) 10 k := by decide +kernel
lemma commute_12_row11 : ∀ k : Fin 20, (B1 * B2) 11 k = (B2 * B1) 11 k := by decide +kernel
lemma commute_12_row12 : ∀ k : Fin 20, (B1 * B2) 12 k = (B2 * B1) 12 k := by decide +kernel
lemma commute_12_row13 : ∀ k : Fin 20, (B1 * B2) 13 k = (B2 * B1) 13 k := by decide +kernel
lemma commute_12_row14 : ∀ k : Fin 20, (B1 * B2) 14 k = (B2 * B1) 14 k := by decide +kernel
lemma commute_12_row15 : ∀ k : Fin 20, (B1 * B2) 15 k = (B2 * B1) 15 k := by decide +kernel
lemma commute_12_row16 : ∀ k : Fin 20, (B1 * B2) 16 k = (B2 * B1) 16 k := by decide +kernel
lemma commute_12_row17 : ∀ k : Fin 20, (B1 * B2) 17 k = (B2 * B1) 17 k := by decide +kernel
lemma commute_12_row18 : ∀ k : Fin 20, (B1 * B2) 18 k = (B2 * B1) 18 k := by decide +kernel
lemma commute_12_row19 : ∀ k : Fin 20, (B1 * B2) 19 k = (B2 * B1) 19 k := by decide +kernel
lemma commute_12 : B1 * B2 = B2 * B1 := by
  ext i j
  fin_cases i
  · exact commute_12_row0 j
  · exact commute_12_row1 j
  · exact commute_12_row2 j
  · exact commute_12_row3 j
  · exact commute_12_row4 j
  · exact commute_12_row5 j
  · exact commute_12_row6 j
  · exact commute_12_row7 j
  · exact commute_12_row8 j
  · exact commute_12_row9 j
  · exact commute_12_row10 j
  · exact commute_12_row11 j
  · exact commute_12_row12 j
  · exact commute_12_row13 j
  · exact commute_12_row14 j
  · exact commute_12_row15 j
  · exact commute_12_row16 j
  · exact commute_12_row17 j
  · exact commute_12_row18 j
  · exact commute_12_row19 j

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_PolynomialData
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

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
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Annihilator
attribute [-instance] _root_.OAI.ZeroKey.matrixMeasurableSpace
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

lemma propagate_zero {T B : Matrix (Fin 20) (Fin 20) ℤ} {u v : Fin 20 → ℤ}
    (hc : Commute T B) (hu : T *ᵥ u = 0) (hb : B *ᵥ u = d • v) : T *ᵥ v = 0 := by
  have hd : d ≠ 0 := by norm_num [d, PencilAlgebra.denominator]
  have h : d • (T *ᵥ v) = 0 := by
    rw [← Matrix.mulVec_smul, ← hb, Matrix.mulVec_mulVec, hc.eq,
      ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero]
  exact (smul_eq_zero.mp h).resolve_left hd

lemma shift_1 : B2 *ᵥ (Pi.single 0 1 : Fin 20 → ℤ) = d • Pi.single 1 1 := by decide +kernel
lemma shift_2 : B1 *ᵥ (Pi.single 0 1 : Fin 20 → ℤ) = d • Pi.single 2 1 := by decide +kernel
lemma shift_3 : B0 *ᵥ (Pi.single 0 1 : Fin 20 → ℤ) = d • Pi.single 3 1 := by decide +kernel
lemma shift_4 : B2 *ᵥ (Pi.single 1 1 : Fin 20 → ℤ) = d • Pi.single 4 1 := by decide +kernel
lemma shift_5 : B1 *ᵥ (Pi.single 1 1 : Fin 20 → ℤ) = d • Pi.single 5 1 := by decide +kernel
lemma shift_6 : B1 *ᵥ (Pi.single 2 1 : Fin 20 → ℤ) = d • Pi.single 6 1 := by decide +kernel
lemma shift_7 : B0 *ᵥ (Pi.single 1 1 : Fin 20 → ℤ) = d • Pi.single 7 1 := by decide +kernel
lemma shift_8 : B0 *ᵥ (Pi.single 2 1 : Fin 20 → ℤ) = d • Pi.single 8 1 := by decide +kernel
lemma shift_9 : B0 *ᵥ (Pi.single 3 1 : Fin 20 → ℤ) = d • Pi.single 9 1 := by decide +kernel
lemma shift_10 : B2 *ᵥ (Pi.single 4 1 : Fin 20 → ℤ) = d • Pi.single 10 1 := by decide +kernel
lemma shift_11 : B1 *ᵥ (Pi.single 4 1 : Fin 20 → ℤ) = d • Pi.single 11 1 := by decide +kernel
lemma shift_12 : B1 *ᵥ (Pi.single 5 1 : Fin 20 → ℤ) = d • Pi.single 12 1 := by decide +kernel
lemma shift_13 : B1 *ᵥ (Pi.single 6 1 : Fin 20 → ℤ) = d • Pi.single 13 1 := by decide +kernel
lemma shift_14 : B0 *ᵥ (Pi.single 4 1 : Fin 20 → ℤ) = d • Pi.single 14 1 := by decide +kernel
lemma shift_15 : B0 *ᵥ (Pi.single 5 1 : Fin 20 → ℤ) = d • Pi.single 15 1 := by decide +kernel
lemma shift_16 : B0 *ᵥ (Pi.single 6 1 : Fin 20 → ℤ) = d • Pi.single 16 1 := by decide +kernel
lemma shift_17 : B0 *ᵥ (Pi.single 7 1 : Fin 20 → ℤ) = d • Pi.single 17 1 := by decide +kernel
lemma shift_18 : B0 *ᵥ (Pi.single 8 1 : Fin 20 → ℤ) = d • Pi.single 18 1 := by decide +kernel
lemma shift_19 : B0 *ᵥ (Pi.single 9 1 : Fin 20 → ℤ) = d • Pi.single 19 1 := by decide +kernel

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_NormalizedMatrices
attribute [-instance] _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

def NB (i : Fin 3) : Matrix (Fin 20) (Fin 20) ℚ :=
  ((d : ℚ)⁻¹) • ((![B0, B1, B2] i).map (Int.castRingHom ℚ))

lemma dQ_ne_zero : (d : ℚ) ≠ 0 := by norm_num [d, PencilAlgebra.denominator]

lemma NB_commute (i j : Fin 3) : Commute (NB i) (NB j) := by
  change Commute ((d : ℚ)⁻¹ • _) ((d : ℚ)⁻¹ • _)
  apply Commute.smul_right
  apply Commute.smul_left
  have h01 : Commute (B0.map (Int.castRingHom ℚ)) (B1.map (Int.castRingHom ℚ)) :=
    (show Commute B0 B1 from commute_01).map (Int.castRingHom ℚ).mapMatrix
  have h02 : Commute (B0.map (Int.castRingHom ℚ)) (B2.map (Int.castRingHom ℚ)) :=
    (show Commute B0 B2 from commute_02).map (Int.castRingHom ℚ).mapMatrix
  have h12 : Commute (B1.map (Int.castRingHom ℚ)) (B2.map (Int.castRingHom ℚ)) :=
    (show Commute B1 B2 from commute_12).map (Int.castRingHom ℚ).mapMatrix
  fin_cases i <;> fin_cases j
  · exact Commute.refl _
  · exact h01
  · exact h02
  · exact h01.symm
  · exact Commute.refl _
  · exact h12
  · exact h02.symm
  · exact h12.symm
  · exact Commute.refl _

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_BorderField
attribute [-instance] _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

lemma fQ_degree : fQ.natDegree = 20 := by
  rw [F_monic.natDegree_map]
  exact F_degree

lemma eQ_ne : eQ 0 ≠ 0 := by
  intro h
  have hh := congrFun h 0
  simp [eQ] at hh

lemma QB_eq : B0.map (Int.castRingHom ℚ) = (d : ℚ) • NB 0 := by
  change _ = (d : ℚ) • ((d : ℚ)⁻¹ • B0.map (Int.castRingHom ℚ))
  rw [smul_smul, mul_inv_cancel₀ dQ_ne_zero, one_smul]

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_PencilModel
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
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

def blocks (i : Fin 4) : Matrix (Fin 6) (Fin 4) ℂ :=
  (blocksZ i).map (Int.castRingHom ℂ)


def pencilMap (A : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ i : Fin 4, ∑ j : Fin 4, A i j • ((blocks i)ᵀ * blocks j)


def PPT {a b : ℕ} (F : Mat a → Mat b) : Prop :=
  IsComplexLinear F ∧ CompletelyPositive F ∧
    CompletelyPositive (fun X => (F X)ᵀ)


def tensorMap {a b c d : ℕ} (F : Mat a → Mat b) (G : Mat c → Mat d)
    (X : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    Matrix (Fin b × Fin d) (Fin b × Fin d) ℂ :=
  ∑ i : Fin c, ∑ j : Fin c,
    Matrix.kronecker (F (fun a b => X (a, i) (b, j))) (G (Matrix.single i j 1))


def hsAdjoint {a b : ℕ} (F : Mat a → Mat b) (Y : Mat b) : Mat a :=
  fun i j => ∑ u : Fin b, ∑ v : Fin b, star (F (Matrix.single i j 1) u v) * Y u v

def hodgeComplement : Mat 6 :=
  ![ ![0,0,0,0,0,1], ![0,0,0,0,-1,0], ![0,0,0,1,0,0],
     ![0,0,1,0,0,0], ![0,-1,0,0,0,0], ![1,0,0,0,0,0] ]

def exteriorMap (A : Mat 10) : Mat 6 :=
  exteriorIsometryᴴ *
    tensorMap pencilMap pencilMap (symmetricIsometry * A * symmetricIsometryᴴ) *
      exteriorIsometry

def complementaryMap (A : Mat 10) : Mat 6 :=
  hodgeComplement * (exteriorMap A)ᵀ * hodgeComplementᴴ

def phiOne (A : Mat 10) : Mat 10 :=
  firstSix * exteriorMap Aᵀ * firstSixᴴ

def phiTwo (B : Mat 10) : Mat 10 :=
  hsAdjoint complementaryMap (firstSixᴴ * B * firstSix)

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Kraus
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
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

lemma krausMap_add {r a b : Type*} [Fintype r] [Fintype a]
    (Q : r → Matrix b a ℂ) (A B : Matrix a a ℂ) :
    krausMap Q (A + B) = krausMap Q A + krausMap Q B := by
  simp [krausMap, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

lemma krausMap_smul {r a b : Type*} [Fintype r] [Fintype a]
    (Q : r → Matrix b a ℂ) (c : ℂ) (A : Matrix a a ℂ) :
    krausMap Q (c • A) = c • krausMap Q A := by
  simp [krausMap, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

lemma krausMap_linear {r : Type*} [Fintype r] {a b : ℕ}
    (Q : r → Matrix (Fin b) (Fin a) ℂ) : IsComplexLinear (krausMap Q) :=
  ⟨krausMap_add Q, krausMap_smul Q⟩

lemma krausMap_positive {r a b : Type*} [Fintype r] [Fintype a] [Finite b]
    (Q : r → Matrix b a ℂ) (A : Matrix a a ℂ) (hA : A.PosSemidef) :
    (krausMap Q A).PosSemidef := by
  exact posSemidef_sum _ (fun k => hA.mul_mul_conjTranspose_same (Q k))

lemma krausMap_entry {r a b : Type*} [Fintype r] [Fintype a]
    (Q : r → Matrix b a ℂ) (A : Matrix a a ℂ) (u v : b) :
    krausMap Q A u v = ∑ k, ∑ i, ∑ j, Q k u i * A i j * star (Q k v j) := by
  simp only [krausMap, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]

lemma amplify_kraus {r : Type*} [Fintype r] {a b : ℕ}
    (Q : r → Matrix (Fin b) (Fin a) ℂ) (k : ℕ)
    (X : Matrix (Fin k × Fin a) (Fin k × Fin a) ℂ) :
    amplify (krausMap Q) k X = krausMap (fun r => (1 : Mat k) ⊗ₖ Q r) X := by
  ext u v
  change krausMap Q (fun i j => X (u.1, i) (v.1, j)) u.2 v.2 =
    krausMap (fun r => (1 : Mat k) ⊗ₖ Q r) X u v
  erw [krausMap_entry, krausMap_entry]
  have hentry (r : r) (u : Fin k × Fin b) (v : Fin k × Fin a) :
      ((1 : Mat k) ⊗ₖ Q r) u v = if u.1 = v.1 then Q r u.2 v.2 else 0 := by
    change (if u.1 = v.1 then (1 : ℂ) else 0) * Q r u.2 v.2 = _
    split <;> simp_all
  simp only [hentry]
  simp [Fintype.sum_prod_type, apply_ite star, ite_mul, mul_ite]

lemma krausMap_cp {r : Type*} [Fintype r] {a b : ℕ}
    (Q : r → Matrix (Fin b) (Fin a) ℂ) : CompletelyPositive (krausMap Q) := by
  intro k hk X hX
  rw [amplify_kraus]
  exact krausMap_positive _ X hX

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_ChoiPairing
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

def asLinearMap {a b : ℕ} (F : Mat a → Mat b) (hF : IsComplexLinear F) :
    Mat a →ₗ[ℂ] Mat b where
  toFun := F
  map_add' := hF.1
  map_smul' := hF.2

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_MinorData
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

def minor {R : Type*} [CommRing R] (x : Fin 4 → R) (i : Fin 15) : R :=
  ((pencilR x).submatrix (rowChoices i) id).det

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_PencilKraus
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

def pencilKraus (r : Fin 6) : Mat 4 := fun i j => blocks j r i

lemma pencilKraus_real (r : Fin 6) (i j : Fin 4) : star (pencilKraus r i j) = pencilKraus r i j := by
  simp [pencilKraus, blocks]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_ExteriorMaps
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

def exteriorKraus (p : Fin 6 × Fin 6) : Matrix (Fin 6) (Fin 10) ℂ :=
  exteriorIsometryᴴ * (pencilKraus p.1 ⊗ₖ pencilKraus p.2) * symmetricIsometry

def complementaryKraus (p : Fin 6 × Fin 6) : Matrix (Fin 6) (Fin 10) ℂ :=
  hodgeComplement * exteriorKraus p

def phiOneKraus (p : Fin 6 × Fin 6) : Mat 10 := firstSix * exteriorKraus p

def phiTwoKraus (p : Fin 6 × Fin 6) : Mat 10 := (complementaryKraus p)ᴴ * firstSixᴴ

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Cofactors
attribute [-instance] _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

def cofactorKernel {R : Type*} [CommRing R] (x : Fin 4 → R) : Fin 4 → R :=
  fun j => ((pencilR x).submatrix (rowChoices 0) id).adjugate j 3

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Powers01
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139

abbrev pow1_4_q {R : Type*} [CommRing R] (z : R) : R := pow1_2_q z

abbrev pow1_8_q {R : Type*} [CommRing R] (z : R) : R := pow1_2_q z

abbrev pow1_16_q {R : Type*} [CommRing R] (z : R) : R := pow1_2_q z

abbrev pow1_17_q {R : Type*} [CommRing R] (z : R) : R := pow1_2_q z

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Powers05
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139


abbrev u10 {R : Type*} [CommRing R] (z : R) : R := pow10_139 z

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Powers06
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139


abbrev u11 {R : Type*} [CommRing R] (z : R) : R := pow11_139 z


abbrev u12 {R : Type*} [CommRing R] (z : R) : R := pow12_139 z

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Powers07
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139


abbrev u13 {R : Type*} [CommRing R] (z : R) : R := pow13_139 z


abbrev u14 {R : Type*} [CommRing R] (z : R) : R := pow14_139 z

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Powers08
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139


abbrev u15 {R : Type*} [CommRing R] (z : R) : R := pow15_139 z


abbrev u16 {R : Type*} [CommRing R] (z : R) : R := pow16_139 z

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Powers09
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139


abbrev u17 {R : Type*} [CommRing R] (z : R) : R := pow17_139 z

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_GaloisField
attribute [-instance] _root_.OAI.ZeroKey.matrixMeasurableSpace
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
instance instNumberFieldK : NumberField K := NumberField.of_module_finite ℚ K
instance instIsSplittingFieldRatKFQ : IsSplittingField ℚ K fQ := IsSplittingField.splittingField fQ

lemma F_map_K : F.map (algebraMap ℤ K) = fQ.map (algebraMap ℚ K) := by
  change F.map (algebraMap ℤ K) = (F.map (algebraMap ℤ ℚ)).map (algebraMap ℚ K)
  rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℤ ℚ K]
lemma F_splits_K : (F.map (algebraMap ℤ K)).Splits := by
  rw [F_map_K]; exact SplittingField.splits fQ

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Channel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A trace-preserving PPT channel with an entangled square, from the dimension-ten pair. -/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
open Matrix

namespace DimensionTen

def phiOneLinear : ChannelCompletion.Map (Fin 10) (Fin 10) :=
  ∑ p : Fin 6 × Fin 6, ChannelCompletion.ad (phiOneKraus p)

end DimensionTen

end

end OAI
end


