-- Prove2me | Definitions.Def_OAIQ033D014
-- name    : OAIQ033D014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T02:34:44.753988+00:00
-- url     : https://prove2.me/theorems/cb3464fe-e19e-476e-8c9c-7596194e2c1b
-- title:
--   Definitions bundle OAIQ033D014 of the split of OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DimensionTen.main_pair`, carved from OpenAI's openai/math development (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 76 declarations of OpenAI's Lean: 11 definitions, 5 instances and 60 theorems. The definitions and types are `OAI.DimensionTen.Border.E`, `OAI.DimensionTen.Border.alpha`, `OAI.DimensionTen.Border.basis`, `OAI.DimensionTen.Border.complexEmbedding`, `OAI.DimensionTen.Border.embeddingRootEquiv`, `OAI.DimensionTen.Border.embeddingsC`, `OAI.DimensionTen.Border.embeddingsK`, `OAI.DimensionTen.Border.evaluationMatrix`, `OAI.DimensionTen.Border.points`, `OAI.DimensionTen.Border.quadraticEquiv`, `OAI.DimensionTen.Border.rho`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Quantum/DimensionTen, in whole or in part: `Quantum_DimensionTen_Annihilator`, `Quantum_DimensionTen_BorderData`, `Quantum_DimensionTen_BorderField`, `Quantum_DimensionTen_EvaluationMinors`, `Quantum_DimensionTen_GaloisField`, `Quantum_DimensionTen_IntegerPolynomials`, `Quantum_DimensionTen_LowBasis`, `Quantum_DimensionTen_Mod41Powers07`, `Quantum_DimensionTen_Mod41Powers08`, `Quantum_DimensionTen_Mod41Powers09`, `Quantum_DimensionTen_Mod41Powers10`, `Quantum_DimensionTen_Mod41Result`, `Quantum_DimensionTen_NormalizedMatrices`, `Quantum_DimensionTen_QuadraticBounds`.
--
--   **Imports.** It imports the bundles `OAIQ033D010`, `OAIQ033D011`, `OAIQ033D012` and `OAIQ033D013` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.DimensionTen.Border.minors_embedding` and `OAI.DimensionTen.Border.quadratic_zero_bound`; the proofs of `OAI.DimensionTen.Border.minors_embedding`, `OAI.DimensionTen.Border.quadratic_zero_bound` and `OAI.DimensionTen.main_pair`.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Quantum/DimensionTen at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ033D010
import Definitions.Def_OAIQ033D011
import Definitions.Def_OAIQ033D012
import Definitions.Def_OAIQ033D013

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

theorem iterate13 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 13) = u13 z := by
  calc
    _ = (z ^ (41 ^ 12)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u12 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate12 z hz)
    _ = _ := pow13_41_pow z hz


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


theorem pow15_5_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u14 z ^ 5 = pow15_5 z := by
  rw [show 5 = 4 + 1 by rfl, pow_succ, pow15_4_pow z hz]
  exact pow15_5_root z hz


theorem pow15_10_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u14 z ^ 10 = pow15_10 z := by
  calc
    _ = u14 z ^ 5 * u14 z ^ 5 := by ring
    _ = pow15_5 z * pow15_5 z := by rw [pow15_5_pow z hz]
    _ = _ := pow15_10_root z hz


theorem pow15_20_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u14 z ^ 20 = pow15_20 z := by
  calc
    _ = u14 z ^ 10 * u14 z ^ 10 := by ring
    _ = pow15_10 z * pow15_10 z := by rw [pow15_10_pow z hz]
    _ = _ := pow15_20_root z hz


theorem pow15_40_pow {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : u14 z ^ 40 = pow15_40 z := by
  calc
    _ = u14 z ^ 20 * u14 z ^ 20 := by ring
    _ = pow15_20 z * pow15_20 z := by rw [pow15_20_pow z hz]
    _ = _ := pow15_40_root z hz


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

theorem iterate17 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 17) = u17 z := by
  calc
    _ = (z ^ (41 ^ 16)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u16 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate16 z hz)
    _ = _ := pow17_41_pow z hz


theorem iterate18 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 18) = u18 z := by
  calc
    _ = (z ^ (41 ^ 17)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u17 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate17 z hz)
    _ = _ := pow18_41_pow z hz

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

theorem iterate19 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 19) = u19 z := by
  calc
    _ = (z ^ (41 ^ 18)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u18 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate18 z hz)
    _ = _ := pow19_41_pow z hz


theorem iterate20 {R : Type*} [CommRing R] [CharP R 41]
    (z : R) (hz : f z = 0) : z ^ (41 ^ 20) = u20 z := by
  calc
    _ = (z ^ (41 ^ 19)) ^ 41 := by rw [← pow_mul]; rfl
    _ = u19 z ^ 41 := congrArg (fun x : R => x ^ 41) (iterate19 z hz)
    _ = _ := pow20_41_pow z hz

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

section
noncomputable section
open Polynomial
namespace DimensionTen.Mod41

section Field
variable (k : Type*) [Field k] [CharP k 41]

attribute [local instance] OAI.DimensionTen.Mod41.charP_root
lemma divides_twenty : f (X : k[X]) ∣ X ^ 41 ^ 20 - X := by
  apply AdjoinRoot.mk_eq_zero.mp
  simp only [map_sub, map_pow, AdjoinRoot.mk_X]
  rw [iterate20 _ (root_f k)]
  simp only [u20, u0, mul_one, zero_add, sub_self]


theorem irreducible_f_of_card [Finite k] (hc : Nat.card k = 41) :
    Irreducible (f (X : k[X])) := by
  apply irreducible_degree_twenty _ degree_f.natDegree_eq
  · simpa only [hc] using divides_twenty k
  · simpa only [hc] using coprime_four k
  · simpa only [hc] using coprime_ten k

end Field

theorem irreducible_f : Irreducible (f (X : (ZMod 41)[X])) :=
  irreducible_f_of_card (ZMod 41) (by simp)

end DimensionTen.Mod41

end
end

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

lemma F_irreducible : Irreducible (F.map (algebraMap ℤ ℚ)) := by
  apply F_monic.irreducible_iff_irreducible_map_fraction_map.mp
  apply Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 41)) F F_monic
  rw [F_reduction_41]
  exact Mod41.irreducible_f

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

lemma annihilate_1 : (FP B0) *ᵥ (Pi.single 1 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute ((show Commute B0 B2 from commute_02))) annihilate_0 shift_1
lemma annihilate_2 : (FP B0) *ᵥ (Pi.single 2 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute ((show Commute B0 B1 from commute_01))) annihilate_0 shift_2
lemma annihilate_3 : (FP B0) *ᵥ (Pi.single 3 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute (Commute.refl B0)) annihilate_0 shift_3
lemma annihilate_4 : (FP B0) *ᵥ (Pi.single 4 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute ((show Commute B0 B2 from commute_02))) annihilate_1 shift_4
lemma annihilate_5 : (FP B0) *ᵥ (Pi.single 5 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute ((show Commute B0 B1 from commute_01))) annihilate_1 shift_5
lemma annihilate_6 : (FP B0) *ᵥ (Pi.single 6 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute ((show Commute B0 B1 from commute_01))) annihilate_2 shift_6
lemma annihilate_7 : (FP B0) *ᵥ (Pi.single 7 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute (Commute.refl B0)) annihilate_1 shift_7
lemma annihilate_8 : (FP B0) *ᵥ (Pi.single 8 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute (Commute.refl B0)) annihilate_2 shift_8
lemma annihilate_9 : (FP B0) *ᵥ (Pi.single 9 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute (Commute.refl B0)) annihilate_3 shift_9
lemma annihilate_10 : (FP B0) *ᵥ (Pi.single 10 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute ((show Commute B0 B2 from commute_02))) annihilate_4 shift_10
lemma annihilate_11 : (FP B0) *ᵥ (Pi.single 11 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute ((show Commute B0 B1 from commute_01))) annihilate_4 shift_11
lemma annihilate_12 : (FP B0) *ᵥ (Pi.single 12 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute ((show Commute B0 B1 from commute_01))) annihilate_5 shift_12
lemma annihilate_13 : (FP B0) *ᵥ (Pi.single 13 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute ((show Commute B0 B1 from commute_01))) annihilate_6 shift_13
lemma annihilate_14 : (FP B0) *ᵥ (Pi.single 14 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute (Commute.refl B0)) annihilate_4 shift_14
lemma annihilate_15 : (FP B0) *ᵥ (Pi.single 15 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute (Commute.refl B0)) annihilate_5 shift_15
lemma annihilate_16 : (FP B0) *ᵥ (Pi.single 16 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute (Commute.refl B0)) annihilate_6 shift_16
lemma annihilate_17 : (FP B0) *ᵥ (Pi.single 17 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute (Commute.refl B0)) annihilate_7 shift_17
lemma annihilate_18 : (FP B0) *ᵥ (Pi.single 18 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute (Commute.refl B0)) annihilate_8 shift_18
lemma annihilate_19 : (FP B0) *ᵥ (Pi.single 19 1 : Fin 20 → ℤ) = 0 := by
  exact propagate_zero (FP_commute (Commute.refl B0)) annihilate_9 shift_19

lemma FP_B0 : FP B0 = 0 := by
  have h (j : Fin 20) : (FP B0) *ᵥ Pi.single j 1 = 0 := by
    fin_cases j
    · exact annihilate_0
    · exact annihilate_1
    · exact annihilate_2
    · exact annihilate_3
    · exact annihilate_4
    · exact annihilate_5
    · exact annihilate_6
    · exact annihilate_7
    · exact annihilate_8
    · exact annihilate_9
    · exact annihilate_10
    · exact annihilate_11
    · exact annihilate_12
    · exact annihilate_13
    · exact annihilate_14
    · exact annihilate_15
    · exact annihilate_16
    · exact annihilate_17
    · exact annihilate_18
    · exact annihilate_19

  ext i j
  have hh := congrFun (h j) i
  simpa [Matrix.mulVec_single] using hh

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_NormalizedMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

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

lemma QB_annihilator : aeval (B0.map (Int.castRingHom ℚ)) (F.map (algebraMap ℤ ℚ)) = 0 := by
  rw [Polynomial.aeval_map_algebraMap, aeval_F]
  have h := congrArg (Int.castRingHom ℚ).mapMatrix FP_B0
  simpa only [map_FP, map_zero, RingHom.mapMatrix_apply] using h

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_BorderField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border

instance instFactIrreduciblePolynomialRatFQ : Fact (Irreducible fQ) := ⟨F_irreducible⟩
instance instFiniteDimensionalRatL : FiniteDimensional ℚ L := (AdjoinRoot.powerBasis F_irreducible.ne_zero).finite

lemma fQ_degree : fQ.natDegree = 20 := by
  rw [F_monic.natDegree_map]
  exact F_degree

lemma representation_exists :
    ∃ ρ : L →ₐ[ℚ] Matrix (Fin 20) (Fin 20) ℚ,
      ρ (AdjoinRoot.root fQ) = B0.map (Int.castRingHom ℚ) ∧
      Function.Bijective (fun a => ρ a *ᵥ eQ 0) :=
  Arithmetic.field_representation fQ F_irreducible fQ_degree _ QB_annihilator _ eQ_ne

def rho : L →ₐ[ℚ] Matrix (Fin 20) (Fin 20) ℚ := representation_exists.choose

lemma rho_root : rho (AdjoinRoot.root fQ) = B0.map (Int.castRingHom ℚ) :=
  representation_exists.choose_spec.1

lemma rho_eval_bijective : Function.Bijective (fun a => rho a *ᵥ eQ 0) :=
  representation_exists.choose_spec.2

def E : L →ₗ[ℚ] (Fin 20 → ℚ) :=
  { toFun := fun a => rho a *ᵥ eQ 0
    map_add' := fun a b => by simp only [map_add, Matrix.add_mulVec]
    map_smul' := fun c a => by simp only [map_smul, RingHom.id_apply, Matrix.smul_mulVec] }

lemma E_injective : Function.Injective E := rho_eval_bijective.1
lemma E_surjective : Function.Surjective E := rho_eval_bijective.2

lemma NB_in_image (i : Fin 3) : ∃ a : L, rho a = NB i := by
  have hc : Commute (rho (AdjoinRoot.root fQ)) (NB i) := by
    rw [rho_root, QB_eq]
    exact (NB_commute 0 i).smul_left _
  exact Arithmetic.centralizer_in_image fQ rho (eQ 0) rho_eval_bijective.2 (NB i) hc

def alpha : Fin 3 → L :=
  ![(d : ℚ)⁻¹ • AdjoinRoot.root fQ, (NB_in_image 1).choose, (NB_in_image 2).choose]

end DimensionTen.Border

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_LowBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Polynomial
namespace DimensionTen.Border


def basis : Module.Basis (Fin 20) ℚ L :=
  (Pi.basisFun ℚ (Fin 20)).map (LinearEquiv.ofBijective E ⟨E_injective, E_surjective⟩).symm

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

instance instNumberFieldK : NumberField K := NumberField.of_module_finite ℚ K
instance instIsSplittingFieldRatKFQ : IsSplittingField ℚ K fQ := IsSplittingField.splittingField fQ
instance instIsGaloisRatK : IsGalois ℚ K := IsGalois.of_separable_splitting_field (p := fQ) F_irreducible.separable

lemma F_map_K : F.map (algebraMap ℤ K) = fQ.map (algebraMap ℚ K) := by
  change F.map (algebraMap ℤ K) = (F.map (algebraMap ℤ ℚ)).map (algebraMap ℚ K)
  rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℤ ℚ K]
lemma F_separable_K : (F.map (algebraMap ℤ K)).Separable := by
  rw [F_map_K]; exact F_irreducible.separable.map
lemma F_splits_K : (F.map (algebraMap ℤ K)).Splits := by
  rw [F_map_K]; exact SplittingField.splits fQ
lemma roots_card_K : Fintype.card (F.rootSet K) = 20 :=
  (roots_card_int F F_monic F_separable_K F_splits_K).trans F_degree

lemma aroot_iff_root {R : Type*} [Field R] [Algebra ℚ R] (x : R) :
    x ∈ fQ.aroots R ↔ x ∈ F.rootSet R := by
  let : CharZero R := Algebra.charZero_of_charZero ℚ R
  rw [mem_aroots, mem_rootSet]
  have h : aeval x fQ = aeval x F := by
    rw [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq ℤ ℚ R, aeval_def]
  constructor
  · intro hx; exact ⟨F_monic.ne_zero, h ▸ hx.2⟩
  · intro hx; exact ⟨F_irreducible.ne_zero, h.symm ▸ hx.2⟩

def embeddingRootEquiv {R : Type*} [Field R] [Algebra ℚ R] :
    (L →ₐ[ℚ] R) ≃ F.rootSet R :=
  (AdjoinRoot.equiv R ℚ fQ F_irreducible.ne_zero).trans
    (Equiv.subtypeEquivRight aroot_iff_root)

lemma embeddings_card_K : Fintype.card (L →ₐ[ℚ] K) = 20 :=
  (Fintype.card_congr (embeddingRootEquiv (R := K))).trans roots_card_K

def embeddingsK : Fin 20 ≃ (L →ₐ[ℚ] K) :=
  (Fintype.equivFinOfCardEq embeddings_card_K).symm

def complexEmbedding : K →ₐ[ℚ] ℂ := IsAlgClosed.lift

lemma finrank_L : Module.finrank ℚ L = 20 := by
  simpa using Module.finrank_eq_card_basis basis

lemma embeddings_card_complex : Fintype.card (L →ₐ[ℚ] ℂ) = 20 :=
  (AlgHom.card ℚ L ℂ).trans finrank_L

lemma complex_embeddings_bijective :
    Function.Bijective (fun i : Fin 20 => complexEmbedding.comp (embeddingsK i)) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, by simpa using embeddings_card_complex.symm⟩
  intro i j hij
  apply embeddingsK.injective
  apply DFunLike.ext
  intro a
  exact complexEmbedding.injective (congrArg (fun σ : L →ₐ[ℚ] ℂ => σ a) hij)

def embeddingsC : Fin 20 ≃ (L →ₐ[ℚ] ℂ) :=
  Equiv.ofBijective _ complex_embeddings_bijective

end DimensionTen.Border

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

def evaluationMatrix : Matrix (Fin 20) (Fin 20) K :=
  fun i j => embeddingsK j (low alpha i)

def points (i : Fin 20) : Fin 3 → ℂ := fun j => embeddingsC i (alpha j)

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

def quadraticEquiv : Fin 10 ≃ QuadraticIndex := Equiv.ofBijective quadraticIndex quadraticIndex_bijective

end DimensionTen.Border

end
end

end OAI
end


