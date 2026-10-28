-- Prove2me | Definitions.Def_OAIQ084L022
-- name    : OAIQ084L022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:34:30.342669+00:00
-- url     : https://prove2.me/theorems/4fa936fa-7a7a-4dbf-8b22-2966ecdc2917
-- title:
--   Definitions bundle OAIQ084L022 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 89 declarations of OpenAI's Lean: 58 definitions and 31 theorems. The definitions and types are `OAI.LaughlinFock.collectedFourData_11`, `OAI.LaughlinFock.collectedFourData_11_0`, `OAI.LaughlinFock.collectedFourData_11_2`, `OAI.LaughlinFock.collectedFourData_11_3`, `OAI.LaughlinFock.collectedFourData_11_4`, `OAI.LaughlinFock.collectedFourData_13`, `OAI.LaughlinFock.collectedFourData_13_0`, `OAI.LaughlinFock.collectedFourData_13_3`, `OAI.LaughlinFock.collectedFourData_14`, `OAI.LaughlinFock.collectedFourData_14_3`, `OAI.LaughlinFock.collectedFourData_15`, `OAI.LaughlinFock.collectedFourData_16`, `OAI.LaughlinFock.collectedFourData_8`, `OAI.LaughlinFock.collectedFourData_8_1`, `OAI.LaughlinFock.collectedFourData_8_4`, `OAI.LaughlinFock.collectedFourData_9`, `OAI.LaughlinFock.collectedFourData_9_0`, `OAI.LaughlinFock.collectedFourData_9_3`, `OAI.LaughlinFock.collectedFourData_9_7`, `OAI.LaughlinFock.collectedFourTrace`, `OAI.LaughlinFock.composedCoupledVector`, `OAI.LaughlinFock.composedCouplingMatrix`, `OAI.LaughlinFock.composedFourAnnihilator`, `OAI.LaughlinFock.composedFourWedgeColumn`, `OAI.LaughlinFock.coupledBasis`, `OAI.LaughlinFock.coupledEuclidean`, `OAI.LaughlinFock.coupledSpinMatrix`, `OAI.LaughlinFock.coupledVector`, `OAI.LaughlinFock.finiteThreeTarget`, `OAI.LaughlinFock.fourCopyColumns`, `OAI.LaughlinFock.fourCopyLift`, `OAI.LaughlinFock.fourCopyWedge`, `OAI.LaughlinFock.fourCoupledAnnihilator`, `OAI.LaughlinFock.fourCoupledWedgeMatrix`, `OAI.LaughlinFock.fourCouplingMatrix`, `OAI.LaughlinFock.fourFactorEmbedding`, `OAI.LaughlinFock.fourHighestCache_17`, `OAI.LaughlinFock.fourHighestCache_19`, `OAI.LaughlinFock.fourHighestCache_20`, `OAI.LaughlinFock.fourHighestCache_21` and 18 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `LaughlinFock_Certificate07`, `LaughlinFock_Certificate09`, `LaughlinFock_Certificate10Data`, `LaughlinFock_Certificate16Data`, `LaughlinFock_Certificate17`, `LaughlinFock_Certificate19`, `LaughlinFock_Certificate19Data`, `LaughlinFock_Certificate20`, `LaughlinFock_Certificate20Data`, `LaughlinFock_Certificate21`, `LaughlinFock_Certificate21Data`, `LaughlinFock_Certificate22`, `LaughlinFock_Certificate22Data`, `LaughlinFock_Certificate23`, `LaughlinFock_CopyNormalization`, `LaughlinFock_CopyVectors`, `LaughlinFock_CoupledLie`, `LaughlinFock_FiniteComparison`, `LaughlinFock_FourBasis`, `LaughlinFock_FourCopies`, `LaughlinFock_FourTrace`, `LaughlinFock_LadderCalculus`, `LaughlinFock_PairDecomposition`, `LaughlinFock_Sparse0807`, `LaughlinFock_Sparse0821`, `LaughlinFock_Sparse0833`, `LaughlinFock_Sparse0903`, `LaughlinFock_Sparse0915`, `LaughlinFock_Sparse0930`, `LaughlinFock_Sparse1102`, `LaughlinFock_Sparse1108`, `LaughlinFock_Sparse1111`, `LaughlinFock_Sparse1115`, `LaughlinFock_Sparse1124`, `LaughlinFock_Sparse1302`, `LaughlinFock_Sparse1308`, `LaughlinFock_Sparse1317`, `LaughlinFock_Sparse1406`, `LaughlinFock_Sparse1413`, `LaughlinFock_Sparse1508`, `LaughlinFock_Sparse1605`, `LaughlinFock_SparseTrace`, `LaughlinFock_TensorBasis`, `LaughlinFock_ThreeSpectrum`.
--
--   **Imports.** It imports the published bundle `Def_LaughlinFock`; the bundles `OAIQ084L002`, `OAIQ084L003`, `OAIQ084L004`, `OAIQ084L005`, `OAIQ084L006`, `OAIQ084L007`, `OAIQ084L008`, `OAIQ084L009`, `OAIQ084L010`, `OAIQ084L011`, `OAIQ084L012`, `OAIQ084L013`, `OAIQ084L014`, `OAIQ084L015`, `OAIQ084L016`, `OAIQ084L017`, `OAIQ084L018`, `OAIQ084L019`, `OAIQ084L020` and `OAIQ084L021` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ084L043`; the statements `OAI.LaughlinFock.fourHighestNumber_20_1`, `OAI.LaughlinFock.fourHighestNumber_20_11`, `OAI.LaughlinFock.fourHighestNumber_20_13`, `OAI.LaughlinFock.fourHighestNumber_20_15`, `OAI.LaughlinFock.fourHighestNumber_20_17`, `OAI.LaughlinFock.fourHighestNumber_20_19`, `OAI.LaughlinFock.fourHighestNumber_20_3`, `OAI.LaughlinFock.fourHighestNumber_20_5`, `OAI.LaughlinFock.fourHighestNumber_20_7`, `OAI.LaughlinFock.fourHighestNumber_20_9`, `OAI.LaughlinFock.fourHighestNumber_21_1`, `OAI.LaughlinFock.fourHighestNumber_21_11`, `OAI.LaughlinFock.fourHighestNumber_21_13`, `OAI.LaughlinFock.fourHighestNumber_21_15`, `OAI.LaughlinFock.fourHighestNumber_21_17`, `OAI.LaughlinFock.fourHighestNumber_21_19`, `OAI.LaughlinFock.fourHighestNumber_21_21`, `OAI.LaughlinFock.fourHighestNumber_21_3`, `OAI.LaughlinFock.fourHighestNumber_21_5`, `OAI.LaughlinFock.fourHighestNumber_21_7`, `OAI.LaughlinFock.fourHighestNumber_21_9`, `OAI.LaughlinFock.fourHighestNumber_22_1`, `OAI.LaughlinFock.fourHighestNumber_22_11`, `OAI.LaughlinFock.fourHighestNumber_22_13`, `OAI.LaughlinFock.fourHighestNumber_22_15`, `OAI.LaughlinFock.fourHighestNumber_22_17`, `OAI.LaughlinFock.fourHighestNumber_22_19`, `OAI.LaughlinFock.fourHighestNumber_22_21`, `OAI.LaughlinFock.fourHighestNumber_22_3`, `OAI.LaughlinFock.fourHighestNumber_22_5`, `OAI.LaughlinFock.fourHighestNumber_22_7`, `OAI.LaughlinFock.fourHighestNumber_22_9`, `OAI.LaughlinFock.fourHighestNumber_23_1`, `OAI.LaughlinFock.fourHighestNumber_23_11`, `OAI.LaughlinFock.fourHighestNumber_23_13`, `OAI.LaughlinFock.fourHighestNumber_23_15`, `OAI.LaughlinFock.fourHighestNumber_23_17`, `OAI.LaughlinFock.fourHighestNumber_23_19`, `OAI.LaughlinFock.fourHighestNumber_23_21`, `OAI.LaughlinFock.fourHighestNumber_23_23`, `OAI.LaughlinFock.fourHighestNumber_23_3`, `OAI.LaughlinFock.fourHighestNumber_23_5`, `OAI.LaughlinFock.fourHighestNumber_23_7`, `OAI.LaughlinFock.fourHighestNumber_23_9`, `OAI.LaughlinFock.fourYNumber_11_11_1`, `OAI.LaughlinFock.fourYNumber_11_11_11`, `OAI.LaughlinFock.fourYNumber_11_11_3`, `OAI.LaughlinFock.fourYNumber_11_11_5`, `OAI.LaughlinFock.fourYNumber_11_11_7`, `OAI.LaughlinFock.fourYNumber_11_11_9`, `OAI.LaughlinFock.fourYNumber_11_3_1`, `OAI.LaughlinFock.fourYNumber_11_3_3`, `OAI.LaughlinFock.fourYNumber_11_5_3`, `OAI.LaughlinFock.fourYNumber_11_5_5`, `OAI.LaughlinFock.fourYNumber_11_7_3`, `OAI.LaughlinFock.fourYNumber_11_7_7`, `OAI.LaughlinFock.fourYNumber_11_9_3`, `OAI.LaughlinFock.fourYNumber_11_9_7`, `OAI.LaughlinFock.fourYNumber_11_9_9`, `OAI.LaughlinFock.fourYNumber_13_11_1`, `OAI.LaughlinFock.fourYNumber_13_11_11`, `OAI.LaughlinFock.fourYNumber_13_11_3`, `OAI.LaughlinFock.fourYNumber_13_11_5`, `OAI.LaughlinFock.fourYNumber_13_11_7`, `OAI.LaughlinFock.fourYNumber_13_13_1`, `OAI.LaughlinFock.fourYNumber_13_13_11`, `OAI.LaughlinFock.fourYNumber_13_13_13`, `OAI.LaughlinFock.fourYNumber_13_13_3`, `OAI.LaughlinFock.fourYNumber_13_13_9`, `OAI.LaughlinFock.fourYNumber_13_5_1`, `OAI.LaughlinFock.fourYNumber_13_7_1`, `OAI.LaughlinFock.fourYNumber_13_7_3`, `OAI.LaughlinFock.fourYNumber_13_9_1`, `OAI.LaughlinFock.fourYNumber_13_9_7`, `OAI.LaughlinFock.fourYNumber_14_11_11`, `OAI.LaughlinFock.fourYNumber_14_11_3`, `OAI.LaughlinFock.fourYNumber_14_13_13`, `OAI.LaughlinFock.fourYNumber_14_13_3`, `OAI.LaughlinFock.fourYNumber_14_13_5`, `OAI.LaughlinFock.fourYNumber_14_1_1`, `OAI.LaughlinFock.fourYNumber_14_3_1`, `OAI.LaughlinFock.fourYNumber_14_5_1`, `OAI.LaughlinFock.fourYNumber_14_5_5`, `OAI.LaughlinFock.fourYNumber_14_7_1`, `OAI.LaughlinFock.fourYNumber_14_7_7`, `OAI.LaughlinFock.fourYNumber_15_11_1`, `OAI.LaughlinFock.fourYNumber_15_13_13`, `OAI.LaughlinFock.fourYNumber_15_15_1`, `OAI.LaughlinFock.fourYNumber_15_15_11`, `OAI.LaughlinFock.fourYNumber_15_15_13`, `OAI.LaughlinFock.fourYNumber_15_15_15`, `OAI.LaughlinFock.fourYNumber_15_15_3`, `OAI.LaughlinFock.fourYNumber_8_1_1`, `OAI.LaughlinFock.fourYNumber_8_3_3`, `OAI.LaughlinFock.fourYNumber_8_5_3`, `OAI.LaughlinFock.fourYNumber_8_5_5`, `OAI.LaughlinFock.fourYNumber_8_7_1`, `OAI.LaughlinFock.fourYNumber_8_7_3`, `OAI.LaughlinFock.fourYNumber_8_7_7`, `OAI.LaughlinFock.fourYNumber_9_1_1`, `OAI.LaughlinFock.fourYNumber_9_3_1`, `OAI.LaughlinFock.fourYNumber_9_3_3`, `OAI.LaughlinFock.fourYNumber_9_5_3`, `OAI.LaughlinFock.fourYNumber_9_5_5`, `OAI.LaughlinFock.fourYNumber_9_7_1`, `OAI.LaughlinFock.fourYNumber_9_7_7`, `OAI.LaughlinFock.fourYNumber_9_9_1`, `OAI.LaughlinFock.fourYNumber_9_9_3`, `OAI.LaughlinFock.fourYNumber_9_9_7` and `OAI.LaughlinFock.fourYNumber_9_9_9`; the proofs of `OAI.LaughlinFock.fourHighestNumber_20_1`, `OAI.LaughlinFock.fourHighestNumber_20_11`, `OAI.LaughlinFock.fourHighestNumber_20_13`, `OAI.LaughlinFock.fourHighestNumber_20_15`, `OAI.LaughlinFock.fourHighestNumber_20_17`, `OAI.LaughlinFock.fourHighestNumber_20_19`, `OAI.LaughlinFock.fourHighestNumber_20_3`, `OAI.LaughlinFock.fourHighestNumber_20_5`, `OAI.LaughlinFock.fourHighestNumber_20_7`, `OAI.LaughlinFock.fourHighestNumber_20_9`, `OAI.LaughlinFock.fourHighestNumber_21_1`, `OAI.LaughlinFock.fourHighestNumber_21_11`, `OAI.LaughlinFock.fourHighestNumber_21_13`, `OAI.LaughlinFock.fourHighestNumber_21_15`, `OAI.LaughlinFock.fourHighestNumber_21_17`, `OAI.LaughlinFock.fourHighestNumber_21_19`, `OAI.LaughlinFock.fourHighestNumber_21_21`, `OAI.LaughlinFock.fourHighestNumber_21_3`, `OAI.LaughlinFock.fourHighestNumber_21_5`, `OAI.LaughlinFock.fourHighestNumber_21_7`, `OAI.LaughlinFock.fourHighestNumber_21_9`, `OAI.LaughlinFock.fourHighestNumber_22_1`, `OAI.LaughlinFock.fourHighestNumber_22_11`, `OAI.LaughlinFock.fourHighestNumber_22_13`, `OAI.LaughlinFock.fourHighestNumber_22_15`, `OAI.LaughlinFock.fourHighestNumber_22_17`, `OAI.LaughlinFock.fourHighestNumber_22_19`, `OAI.LaughlinFock.fourHighestNumber_22_21`, `OAI.LaughlinFock.fourHighestNumber_22_3`, `OAI.LaughlinFock.fourHighestNumber_22_5`, `OAI.LaughlinFock.fourHighestNumber_22_7`, `OAI.LaughlinFock.fourHighestNumber_22_9`, `OAI.LaughlinFock.fourHighestNumber_23_1`, `OAI.LaughlinFock.fourHighestNumber_23_11`, `OAI.LaughlinFock.fourHighestNumber_23_13`, `OAI.LaughlinFock.fourHighestNumber_23_15`, `OAI.LaughlinFock.fourHighestNumber_23_17`, `OAI.LaughlinFock.fourHighestNumber_23_19`, `OAI.LaughlinFock.fourHighestNumber_23_21`, `OAI.LaughlinFock.fourHighestNumber_23_23`, `OAI.LaughlinFock.fourHighestNumber_23_3`, `OAI.LaughlinFock.fourHighestNumber_23_5`, `OAI.LaughlinFock.fourHighestNumber_23_7`, `OAI.LaughlinFock.fourHighestNumber_23_9`, `OAI.LaughlinFock.fourYNumber_11_11_1`, `OAI.LaughlinFock.fourYNumber_11_11_11`, `OAI.LaughlinFock.fourYNumber_11_11_3`, `OAI.LaughlinFock.fourYNumber_11_11_5`, `OAI.LaughlinFock.fourYNumber_11_11_7`, `OAI.LaughlinFock.fourYNumber_11_11_9`, `OAI.LaughlinFock.fourYNumber_11_3_1`, `OAI.LaughlinFock.fourYNumber_11_3_3`, `OAI.LaughlinFock.fourYNumber_11_5_3`, `OAI.LaughlinFock.fourYNumber_11_5_5`, `OAI.LaughlinFock.fourYNumber_11_7_3`, `OAI.LaughlinFock.fourYNumber_11_7_7`, `OAI.LaughlinFock.fourYNumber_11_9_3`, `OAI.LaughlinFock.fourYNumber_11_9_7`, `OAI.LaughlinFock.fourYNumber_11_9_9`, `OAI.LaughlinFock.fourYNumber_13_11_1`, `OAI.LaughlinFock.fourYNumber_13_11_11`, `OAI.LaughlinFock.fourYNumber_13_11_3`, `OAI.LaughlinFock.fourYNumber_13_11_5`, `OAI.LaughlinFock.fourYNumber_13_11_7`, `OAI.LaughlinFock.fourYNumber_13_13_1`, `OAI.LaughlinFock.fourYNumber_13_13_11`, `OAI.LaughlinFock.fourYNumber_13_13_13`, `OAI.LaughlinFock.fourYNumber_13_13_3`, `OAI.LaughlinFock.fourYNumber_13_13_9`, `OAI.LaughlinFock.fourYNumber_13_5_1`, `OAI.LaughlinFock.fourYNumber_13_7_1`, `OAI.LaughlinFock.fourYNumber_13_7_3`, `OAI.LaughlinFock.fourYNumber_13_9_1`, `OAI.LaughlinFock.fourYNumber_13_9_7`, `OAI.LaughlinFock.fourYNumber_14_11_11`, `OAI.LaughlinFock.fourYNumber_14_11_3`, `OAI.LaughlinFock.fourYNumber_14_13_13`, `OAI.LaughlinFock.fourYNumber_14_13_3`, `OAI.LaughlinFock.fourYNumber_14_13_5`, `OAI.LaughlinFock.fourYNumber_14_1_1`, `OAI.LaughlinFock.fourYNumber_14_3_1`, `OAI.LaughlinFock.fourYNumber_14_5_1`, `OAI.LaughlinFock.fourYNumber_14_5_5`, `OAI.LaughlinFock.fourYNumber_14_7_1`, `OAI.LaughlinFock.fourYNumber_14_7_7`, `OAI.LaughlinFock.fourYNumber_15_11_1`, `OAI.LaughlinFock.fourYNumber_15_13_13`, `OAI.LaughlinFock.fourYNumber_15_15_1`, `OAI.LaughlinFock.fourYNumber_15_15_11`, `OAI.LaughlinFock.fourYNumber_15_15_13`, `OAI.LaughlinFock.fourYNumber_15_15_15`, `OAI.LaughlinFock.fourYNumber_15_15_3`, `OAI.LaughlinFock.fourYNumber_8_1_1`, `OAI.LaughlinFock.fourYNumber_8_3_3`, `OAI.LaughlinFock.fourYNumber_8_5_3`, `OAI.LaughlinFock.fourYNumber_8_5_5`, `OAI.LaughlinFock.fourYNumber_8_7_1`, `OAI.LaughlinFock.fourYNumber_8_7_3`, `OAI.LaughlinFock.fourYNumber_8_7_7`, `OAI.LaughlinFock.fourYNumber_9_1_1`, `OAI.LaughlinFock.fourYNumber_9_3_1`, `OAI.LaughlinFock.fourYNumber_9_3_3`, `OAI.LaughlinFock.fourYNumber_9_5_3`, `OAI.LaughlinFock.fourYNumber_9_5_5`, `OAI.LaughlinFock.fourYNumber_9_7_1`, `OAI.LaughlinFock.fourYNumber_9_7_7`, `OAI.LaughlinFock.fourYNumber_9_9_1`, `OAI.LaughlinFock.fourYNumber_9_9_3`, `OAI.LaughlinFock.fourYNumber_9_9_7` and `OAI.LaughlinFock.fourYNumber_9_9_9`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L002
import Definitions.Def_OAIQ084L003
import Definitions.Def_OAIQ084L004
import Definitions.Def_OAIQ084L005
import Definitions.Def_OAIQ084L006
import Definitions.Def_OAIQ084L007
import Definitions.Def_OAIQ084L008
import Definitions.Def_OAIQ084L009
import Definitions.Def_OAIQ084L010
import Definitions.Def_OAIQ084L011
import Definitions.Def_OAIQ084L012
import Definitions.Def_OAIQ084L013
import Definitions.Def_OAIQ084L014
import Definitions.Def_OAIQ084L015
import Definitions.Def_OAIQ084L016
import Definitions.Def_OAIQ084L017
import Definitions.Def_OAIQ084L018
import Definitions.Def_OAIQ084L019
import Definitions.Def_OAIQ084L020
import Definitions.Def_OAIQ084L021

section
-- module Solutions.OAIQ084_LF.LaughlinFock_LadderCalculus
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ladder Calculus. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators



theorem gridLower_smul (n m : ℕ) (c : ℝ) (f : GridVector) :
    gridLower n m (c • f) = c • gridLower n m f := by
  funext p q
  simp only [gridLower, Pi.smul_apply, smul_eq_mul]
  ring

theorem gridRaise_smul (n m : ℕ) (c : ℝ) (f : GridVector) :
    gridRaise n m (c • f) = c • gridRaise n m f := by
  funext p q
  simp only [gridRaise, Pi.smul_apply, smul_eq_mul]
  ring

@[simp] theorem gridLower_zero (n m : ℕ) : gridLower n m 0 = 0 := by
  funext p q
  simp [gridLower]

@[simp] theorem gridRaise_zero (n m : ℕ) : gridRaise n m 0 = 0 := by
  funext p q
  simp [gridRaise]

theorem gridLower_supported {n m : ℕ} {f : GridVector} (hf : GridSupported n m f) :
    GridSupported n m (gridLower n m f) := by
  intro p q h
  rcases h with hp | hq
  · simp only [gridLower, spinStep_cutoff n p hp, zero_mul, zero_add,
      hf p (q-1) (Or.inl hp), mul_zero]
  · simp only [gridLower, spinStep_cutoff m q hq, mul_zero, zero_mul, add_zero,
      hf (p-1) q (Or.inr hq)]

theorem gridRaise_supported {n m : ℕ} {f : GridVector} (hf : GridSupported n m f) :
    GridSupported n m (gridRaise n m f) := by
  intro p q h
  have h1 : n < p+1 ∨ m < q := by omega
  have h2 : n < p ∨ m < q+1 := by omega
  simp [gridRaise, hf (p+1) q h1, hf p (q+1) h2]

theorem gridLower_layer {n m T : ℕ} {f : GridVector} (hf : GridLayer T f) :
    GridLayer (T+1) (gridLower n m f) := by
  intro p q h
  unfold gridLower
  have h1 : spinStep n p * f (p-1) q = 0 := by
    by_cases hp : p = 0
    · simp [hp]
    · rw [hf (p-1) q (by omega), mul_zero]
  have h2 : spinStep m q * f p (q-1) = 0 := by
    by_cases hq : q = 0
    · simp [hq]
    · rw [hf p (q-1) (by omega), mul_zero]
  rw [h1, h2, zero_add]

 

theorem grid_commutator_at (n m : ℕ) (f : GridVector) (p q : ℕ)
    (hp : p ≤ n) (hq : q ≤ m) :
    gridRaise n m (gridLower n m f) p q - gridLower n m (gridRaise n m f) p q =
      ((n : ℝ)+m-2*(p+q)) * f p q := by
  have hdiag : gridRaise n m (gridLower n m f) p q -
      gridLower n m (gridRaise n m f) p q =
      (spinStep n (p+1)^2-spinStep n p^2 +
        (spinStep m (q+1)^2-spinStep m q^2)) * f p q := by
    cases p <;> cases q <;>
      simp only [gridRaise, gridLower, Nat.succ_sub_one,
        spinStep_zero, zero_mul, zero_add, add_zero, zero_pow (by omega : 2 ≠ 0), sub_zero] <;> ring
  rw [hdiag, spinStep_sq_sub hp, spinStep_sq_sub hq]
  ring

 
theorem grid_commutator_layer {n m T : ℕ} {f : GridVector}
    (hf : GridSupported n m f) (hT : GridLayer T f) :
    gridRaise n m (gridLower n m f) = gridLower n m (gridRaise n m f) +
      ((n : ℝ)+m-2*T) • f := by
  funext p q
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : n < p ∨ m < q
  · rw [gridRaise_supported (gridLower_supported hf) p q h,
      gridLower_supported (gridRaise_supported hf) p q h, hf p q h]
    ring
  · have hp : p ≤ n := by omega
    have hq : q ≤ m := by omega
    have he := grid_commutator_at n m f p q hp hq
    by_cases hl : p+q = T
    · have hc : (p : ℝ) + q = T := by exact_mod_cast hl
      rw [hc] at he
      linarith only [he]
    · rw [hT p q hl, mul_zero] at he ⊢
      linarith

 
def gridInner (n m : ℕ) (f g : GridVector) : ℝ :=
  ∑ p ∈ Finset.range (n+1), ∑ q ∈ Finset.range (m+1), f p q * g p q

theorem gridInner_smul_left (n m : ℕ) (c : ℝ) (f g : GridVector) :
    gridInner n m (c • f) g = c * gridInner n m f g := by
  simp only [gridInner, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem gridInner_smul_right (n m : ℕ) (c : ℝ) (f g : GridVector) :
    gridInner n m f (c • g) = c * gridInner n m f g := by
  simp only [gridInner, Pi.smul_apply, smul_eq_mul, ←mul_assoc, mul_comm _ c, Finset.mul_sum]



theorem grid_adjoint (n m : ℕ) (f g : GridVector) :
    gridInner n m (gridLower n m f) g = gridInner n m f (gridRaise n m g) := by
  simp only [gridInner, gridLower, gridRaise, add_mul, mul_add, Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · rw [Finset.sum_comm, Finset.sum_comm (f := fun p q => f p q * _)]
    apply Finset.sum_congr rfl
    intro q _
    exact spinStep_sum_adjoint n (fun p => f p q) (fun p => g p q)
  · apply Finset.sum_congr rfl
    intro p _
    exact spinStep_sum_adjoint m (f p) (g p)

 

def coupledVector (n m z k : ℕ) : GridVector := fun p q =>
  if p+q = z+k then coupledCoefficient n m z k p else 0

theorem coupledVector_layer (n m z k : ℕ) :
    GridLayer (z+k) (coupledVector n m z k) := by
  intro p q h
  exact ite_eq_right h

theorem coupledVector_supported {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m) (k : ℕ) :
    GridSupported n m (coupledVector n m z k) := by
  intro p q h
  unfold coupledVector
  split_ifs with he
  · rcases h with hp | hq
    · exact coupledCoefficient_left_support hn k p hp
    · exact coupledCoefficient_right_support hm k p (by omega)
  · rfl



theorem coupledVector_highest {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m) :
    gridRaise n m (coupledVector n m z 0) = 0 := by
  funext p q
  simp only [gridRaise, coupledVector, Nat.add_zero, Pi.zero_apply]
  by_cases h : p+q+1 = z
  · have h1 : p+1+q = z := by omega
    have h2 : p+(q+1) = z := by omega
    rw [ite_eq_left h1, ite_eq_left h2, spinStep_succ (by omega : p ≤ n),
      spinStep_succ (by omega : q ≤ m)]
    have hq1 : q+1 = z-p := by omega
    have hmq : m-q = m-z+p+1 := by omega
    rw [hq1, hmq]
    simp only [coupledCoefficient]
    simpa only [mul_comm] using highestCoefficient_raising (m := m) hn (by omega : p < z)
  · rw [ite_eq_right (by omega : p+1+q ≠ z), ite_eq_right (by omega : p+(q+1) ≠ z)]
    ring

 

theorem coupledVector_succ_apply (n m z k p q : ℕ) :
    coupledVector n m z (k+1) p q = gridLower n m (coupledVector n m z k) p q /
      Real.sqrt (((k+1 : ℕ) : ℝ)*((n : ℝ)+m-2*z-k)) := by
  by_cases ht : p+q = z+k+1
  · have ht' : (p : ℝ)+q = (z : ℝ)+k+1 := by exact_mod_cast ht
    have hr1 : (((z+k+1 : ℕ) : ℝ)-p) = q := by push_cast; linarith
    have hr2 : (m : ℝ)+p-z-k = (m : ℝ)+1-q := by linarith
    simp only [coupledVector, show z+(k+1) = z+k+1 by omega, ht, ite_true, if_true,
      coupledCoefficient_lower, hr1, hr2, gridLower, spinStep,
      Real.sqrt_mul (Nat.cast_nonneg p), Real.sqrt_mul (Nat.cast_nonneg q)]
    by_cases hp : p = 0
    · subst p
      have hq : 0+(q-1) = z+k := by omega
      simp [hq]
    · by_cases hq : q = 0
      · subst q
        have hp' : p-1+0 = z+k := by omega
        simp [hp']
      · rw [ite_eq_left (by omega : p-1+q = z+k), ite_eq_left (by omega : p+(q-1) = z+k)]
  · have hzero := gridLower_layer (n := n) (m := m) (coupledVector_layer n m z k) p q ht
    rw [hzero, zero_div]
    exact ite_eq_right (by omega)

theorem coupledVector_succ {n m z : ℕ} (hz : 2*z ≤ n+m) (k : ℕ) :
    coupledVector n m z (k+1) = (spinStep (n+m-2*z) (k+1))⁻¹ •
      gridLower n m (coupledVector n m z k) := by
  funext p q
  simp only [Pi.smul_apply, smul_eq_mul, coupledVector_succ_apply]
  have hden : Real.sqrt (((k+1 : ℕ) : ℝ)*((n : ℝ)+m-2*z-k)) =
      spinStep (n+m-2*z) (k+1) := by
    unfold spinStep
    rw [Nat.cast_sub hz]
    push_cast
    congr 2
    ring
  rw [hden, div_eq_mul_inv, mul_comm]

 

theorem coupledVector_lower {n m z k : ℕ} (hz : 2*z ≤ n+m)
    (hk : k < n+m-2*z) :
    gridLower n m (coupledVector n m z k) =
      spinStep (n+m-2*z) (k+1) • coupledVector n m z (k+1) := by
  have hpos := spinStep_pos (by omega : 0 < k+1) (by omega : k+1 ≤ n+m-2*z)
  rw [coupledVector_succ hz, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

 
theorem coupledVector_top_norm {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m) :
    gridInner n m (coupledVector n m z 0) (coupledVector n m z 0) = 1 := by
  have hq : ∀ p, (∑ q ∈ Finset.range (m+1),
      coupledVector n m z 0 p q * coupledVector n m z 0 p q) =
      if p ≤ z then highestCoefficient n m z p ^ 2 else 0 := by
    intro p
    by_cases hp : p ≤ z
    · rw [ite_eq_left hp]
      calc
        _ = coupledVector n m z 0 p (z-p) * coupledVector n m z 0 p (z-p) := by
          apply Finset.sum_eq_single (z-p)
          · intro q _ hne
            simp only [coupledVector, Nat.add_zero, ite_eq_right (by omega : p+q ≠ z), mul_zero]
          · intro hnot
            exact (hnot (Finset.mem_range.mpr (by omega : z-p < m+1))).elim
        _ = _ := by simp [coupledVector, coupledCoefficient, show p+(z-p) = z by omega, pow_two]
    · rw [ite_eq_right hp]
      apply Finset.sum_eq_zero
      intro q _
      simp only [coupledVector, Nat.add_zero, ite_eq_right (by omega : p+q ≠ z), mul_zero]
  simp only [gridInner, hq]
  calc
    _ = ∑ p ∈ Finset.range (z+1), if p ≤ z then highestCoefficient n m z p ^ 2 else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega : z+1 ≤ n+1))
      intro p _ hout
      rw [Finset.mem_range] at hout
      exact ite_eq_right (by omega)
    _ = ∑ p ∈ Finset.range (z+1), highestCoefficient n m z p ^ 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [ite_eq_left (by have := Finset.mem_range.mp hp; omega)]
    _ = 1 := highestCoefficient_norm hn

 
theorem coupledVector_commutator {n m z : ℕ} (hn : z ≤ n) (hm : z ≤ m) (k : ℕ) :
    gridRaise n m (gridLower n m (coupledVector n m z k)) =
      gridLower n m (gridRaise n m (coupledVector n m z k)) +
        (((n+m-2*z : ℕ) : ℝ)-2*k) • coupledVector n m z k := by
  have h := grid_commutator_layer (coupledVector_supported hn hm k) (coupledVector_layer n m z k)
  convert h using 2
  all_goals try with_reducible_and_instances rfl
  rw [Nat.cast_sub (by omega : 2*z ≤ n+m)]
  push_cast
  ring_nf

 

theorem coupledVector_raise {n m z k : ℕ} (hn : z ≤ n) (hm : z ≤ m)
    (hk : k ≤ n+m-2*z) :
    gridRaise n m (coupledVector n m z k) =
      spinStep (n+m-2*z) k • coupledVector n m z (k-1) := by
  have hz : 2*z ≤ n+m := by omega
  revert hk
  induction k with
  | zero =>
    intro _
    simp only [coupledVector_highest hn hm, spinStep_zero, zero_smul]
  | succ k ih =>
    intro hk
    have hprev := ih (by omega : k ≤ n+m-2*z)
    have hLR : gridLower n m (gridRaise n m (coupledVector n m z k)) =
        spinStep (n+m-2*z) k ^ 2 • coupledVector n m z k := by
      rw [hprev, gridLower_smul]
      by_cases hk0 : k = 0
      · simp [hk0]
      · rw [coupledVector_lower hz (by omega : k-1 < n+m-2*z),
          show k-1+1 = k by omega, smul_smul, ← pow_two]
    have h := coupledVector_commutator hn hm k
    rw [coupledVector_lower hz (by omega : k < n+m-2*z), gridRaise_smul, hLR, ← add_smul] at h
    have hsq : spinStep (n+m-2*z) k ^ 2 + (((n+m-2*z : ℕ) : ℝ)-2*k) =
        spinStep (n+m-2*z) (k+1)^2 := by
      linarith only [spinStep_sq_sub (by omega : k ≤ n+m-2*z)]
    rw [hsq] at h
    have hpos := spinStep_pos (by omega : 0 < k+1) (by omega : k+1 ≤ n+m-2*z)
    funext p q
    have he := congrArg (fun f : GridVector => f p q) h
    simp only [Pi.smul_apply, smul_eq_mul] at he ⊢
    simp only [Nat.succ_sub_one]
    apply mul_left_cancel₀ hpos.ne'
    nlinarith only [he]

 

theorem coupledVector_norm {n m z k : ℕ} (hn : z ≤ n) (hm : z ≤ m)
    (hk : k ≤ n+m-2*z) :
    gridInner n m (coupledVector n m z k) (coupledVector n m z k) = 1 := by
  have hz : 2*z ≤ n+m := by omega
  revert hk
  induction k with
  | zero => exact fun _ => coupledVector_top_norm hn hm
  | succ k ih =>
    intro hk
    have hprev := ih (by omega : k ≤ n+m-2*z)
    have h := grid_adjoint n m (coupledVector n m z k) (coupledVector n m z (k+1))
    rw [coupledVector_lower hz (by omega : k < n+m-2*z),
      coupledVector_raise hn hm (by omega : k+1 ≤ n+m-2*z),
      Nat.add_sub_cancel, gridInner_smul_left, gridInner_smul_right, hprev, mul_one] at h
    have hpos := spinStep_pos (by omega : 0 < k+1) (by omega : k+1 ≤ n+m-2*z)
    apply mul_left_cancel₀ hpos.ne'
    simpa using h

@[simp] theorem gridInner_zero_right (n m : ℕ) (f : GridVector) :
    gridInner n m f 0 = 0 := by simp [gridInner]

@[simp] theorem gridInner_zero_left (n m : ℕ) (g : GridVector) :
    gridInner n m 0 g = 0 := by simp [gridInner]

theorem gridInner_comm (n m : ℕ) (f g : GridVector) :
    gridInner n m f g = gridInner n m g f := by
  simp only [gridInner, mul_comm]

theorem gridInner_of_layers {n m T U : ℕ} {f g : GridVector}
    (hf : GridLayer T f) (hg : GridLayer U g) (hTU : T ≠ U) :
    gridInner n m f g = 0 := by
  apply Finset.sum_eq_zero
  intro p _
  apply Finset.sum_eq_zero
  intro q _
  by_cases h : p+q = T
  · rw [hg p q (by omega), mul_zero]
  · rw [hf p q h, zero_mul]

 

theorem coupledVector_orthogonal {n m z r k l : ℕ}
    (hzn : z ≤ n) (hzm : z ≤ m) (hrn : r ≤ n) (hrm : r ≤ m)
    (hzr : z < r) (hk : k ≤ n+m-2*z) (hl : l ≤ n+m-2*r) :
    gridInner n m (coupledVector n m z k) (coupledVector n m r l) = 0 := by
  have hz : 2*z ≤ n+m := by omega
  induction l generalizing k with
  | zero =>
    by_cases ht : z+k = r
    · have h := grid_adjoint n m (coupledVector n m z (k-1)) (coupledVector n m r 0)
      rw [coupledVector_lower hz (by omega : k-1 < n+m-2*z),
        show k-1+1 = k by omega, coupledVector_highest hrn hrm,
        gridInner_smul_left, gridInner_zero_right] at h
      exact (mul_eq_zero.mp h).resolve_left (spinStep_pos (by omega : 0 < k) hk).ne'
    · exact gridInner_of_layers (coupledVector_layer _ _ _ _) (coupledVector_layer _ _ _ _) (by omega)
  | succ l ih =>
    by_cases ht : z+k = r+(l+1)
    · have h := grid_adjoint n m (coupledVector n m z (k-1)) (coupledVector n m r (l+1))
      rw [coupledVector_lower hz (by omega : k-1 < n+m-2*z),
        show k-1+1 = k by omega,
        coupledVector_raise hrn hrm (by omega : l+1 ≤ n+m-2*r),
        Nat.add_sub_cancel, gridInner_smul_left, gridInner_smul_right,
        ih (by omega : k-1 ≤ n+m-2*z) (by omega : l ≤ n+m-2*r), mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_left (spinStep_pos (by omega : 0 < k) hk).ne'
    · exact gridInner_of_layers (coupledVector_layer _ _ _ _) (coupledVector_layer _ _ _ _) (by omega)

 

theorem coupledVector_gram {n m z r k l : ℕ}
    (hzn : z ≤ n) (hzm : z ≤ m) (hrn : r ≤ n) (hrm : r ≤ m)
    (hk : k ≤ n+m-2*z) (hl : l ≤ n+m-2*r) :
    gridInner n m (coupledVector n m z k) (coupledVector n m r l) =
      if z = r ∧ k = l then 1 else 0 := by
  rcases lt_trichotomy z r with hzr | rfl | hrz
  · rw [ite_eq_right (by omega)]
    exact coupledVector_orthogonal hzn hzm hrn hrm hzr hk hl
  · by_cases hkl : k = l
    · subst l
      rw [ite_eq_left ⟨rfl, rfl⟩]
      exact coupledVector_norm hzn hzm hk
    · rw [ite_eq_right (by tauto)]
      exact gridInner_of_layers (coupledVector_layer _ _ _ _) (coupledVector_layer _ _ _ _) (by omega)
  · rw [ite_eq_right (by omega), gridInner_comm]
    exact coupledVector_orthogonal hrn hrm hzn hzm hrz hl hk

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_TensorBasis
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor Basis. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators


def gridEuclidean (n m : ℕ) (f : GridVector) : EuclideanSpace ℝ (Fin (n+1) × Fin (m+1)) :=
  WithLp.toLp 2 (fun pq => f pq.1 pq.2)

theorem gridEuclidean_inner (n m : ℕ) (f g : GridVector) :
    inner ℝ (gridEuclidean n m f) (gridEuclidean n m g) = gridInner n m f g := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp only [gridEuclidean, WithLp.ofLp_toLp, RCLike.inner_apply, conj_trivial]
  calc
    _ = ∑ p : Fin (n+1), ∑ q ∈ Finset.range (m+1), g p.val q * f p.val q := by
      apply Finset.sum_congr rfl
      intro p _
      exact Fin.sum_univ_eq_sum_range (fun q => g p.val q * f p.val q) (m+1)
    _ = ∑ p ∈ Finset.range (n+1), ∑ q ∈ Finset.range (m+1), g p q * f p q :=
      Fin.sum_univ_eq_sum_range (fun p => ∑ q ∈ Finset.range (m+1), g p q * f p q) (n+1)
    _ = _ := by simp only [gridInner, mul_comm]

 

def coupledEuclidean (n m : ℕ) (i : CoupledIndex n m) :
    EuclideanSpace ℝ (Fin (n+1) × Fin (m+1)) :=
  gridEuclidean n m (coupledVector n m i.1.val i.2.val)



theorem coupledEuclidean_orthonormal (n m : ℕ) : Orthonormal ℝ (coupledEuclidean n m) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  have hi := coupledIndex_bounds i
  have hj := coupledIndex_bounds j
  rw [coupledEuclidean, coupledEuclidean, gridEuclidean_inner,
    coupledVector_gram hi.1 hi.2.1 hj.1 hj.2.1 hi.2.2 hj.2.2]
  have he : (i.1.val = j.1.val ∧ i.2.val = j.2.val) ↔ i = j := by
    constructor
    · intro ⟨hz, hk⟩
      rcases i with ⟨z, k⟩
      rcases j with ⟨r, l⟩
      have hr : z = r := Fin.ext hz
      subst r
      have hl : k = l := Fin.ext hk
      subst l
      rfl
    · rintro rfl
      exact ⟨rfl, rfl⟩
  simp only [he]

 

def coupledBasis (n m : ℕ) :
    OrthonormalBasis (CoupledIndex n m) ℝ (EuclideanSpace ℝ (Fin (n+1) × Fin (m+1))) :=
  OrthonormalBasis.mk (coupledEuclidean_orthonormal n m)
    (((coupledEuclidean_orthonormal n m).linearIndependent.span_eq_top_of_card_eq_finrank'
      (by rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; exact coupledIndex_card n m)).ge)

@[simp] theorem coupledBasis_apply (n m : ℕ) (i : CoupledIndex n m) :
    coupledBasis n m i = coupledEuclidean n m i := by
  simp only [coupledBasis, OrthonormalBasis.coe_mk]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_CopyNormalization
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Copy Normalization. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators



def wedgeCoupledCoefficient (Q r k : ℕ) (ij : IncreasingPair Q) : ℝ :=
  Real.sqrt 2 * coupledVector Q Q r k ij.val.1.val ij.val.2.val



def composedCoupledVector (Q r z k : ℕ)
    (b : Fin (2*Q-2+1) × IncreasingPair Q) : ℝ :=
  ∑ a : Fin (2*Q-2*r+1),
    coupledVector (2*Q-2) (2*Q-2*r) z k b.1.val a.val *
      wedgeCoupledCoefficient Q r a.val b.2



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_ThreeSpectrum
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Spectrum. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder



def threeCoupledColumn (Q z k : ℕ) : PairLabel Q × Orbital Q → ℂ :=
  fun pj => coupledVector (2*Q-2) Q z k pj.1.val pj.2.val



def threeCouplingMatrix (Q : ℕ) :
    Matrix (PairLabel Q × Orbital Q) (CoupledIndex (2*Q-2) Q) ℂ :=
  fun pj c => threeCoupledColumn Q c.1.val c.2.val pj



def threeSpinProjection (Q z : ℕ) : Matrix (PairLabel Q × Orbital Q) (PairLabel Q × Orbital Q) ℂ :=
  threeCouplingMatrix Q * Matrix.diagonal
    (fun c : CoupledIndex (2*Q-2) Q => if c.1.val=z then (1:ℂ) else 0) * (threeCouplingMatrix Q)ᴴ


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FiniteComparison
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Comparison. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology


def finiteThreeTarget (Q : ℕ) : FockMatrix Q :=
  exteriorLift Q 3 (threeWedgeMatrix Q *
    (∑ z ∈ Finset.range 16, (gramShift Q z : ℂ) • threeSpinProjection Q z) *
      (threeWedgeMatrix Q)ᴴ)

 
def fullThreeTarget (Q : ℕ) : FockMatrix Q :=
  exteriorLift Q 3 (threeWedgeMatrix Q *
    (∑ z ∈ Finset.range (Q+1), (gramShift Q z : ℂ) • threeSpinProjection Q z) *
      (threeWedgeMatrix Q)ᴴ)



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate07. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_7 : List (Occupation 24 × List ℚ) := fourHighestCache_7_0

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_SparseTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder


def collectedFourTrace (D r s : ℕ) (ls : List CollectedFourTerm) : ℤ :=
  -(directIntegerSum (collectedTermValue D r s) ls)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0903
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0903. -/
namespace LaughlinFock

def collectedFourData_9_0 : List (List CollectedFourTerm) := [
  collectedFourData_9_0_0,
  collectedFourData_9_0_1,
  collectedFourData_9_0_2,
  collectedFourData_9_0_3,
  collectedFourData_9_0_4,
  collectedFourData_9_0_5,
  collectedFourData_9_0_6,
  collectedFourData_9_0_7,
  collectedFourData_9_0_8,
  collectedFourData_9_0_9,
  collectedFourData_9_0_10,
  collectedFourData_9_0_11,
  collectedFourData_9_0_12,
  collectedFourData_9_0_13,
  collectedFourData_9_0_14,
  collectedFourData_9_0_15,
  collectedFourData_9_0_16,
  collectedFourData_9_0_17,
  collectedFourData_9_0_18,
  collectedFourData_9_0_19,
  collectedFourData_9_0_20,
  collectedFourData_9_0_21,
  collectedFourData_9_0_22,
  collectedFourData_9_0_23,
  collectedFourData_9_0_24,
  collectedFourData_9_0_25,
  collectedFourData_9_0_26,
  collectedFourData_9_0_27,
  collectedFourData_9_0_28,
  collectedFourData_9_0_29,
  collectedFourData_9_0_30,
  collectedFourData_9_0_31,
  collectedFourData_9_0_32,
  collectedFourData_9_0_33,
  collectedFourData_9_0_34,
  collectedFourData_9_0_35,
  collectedFourData_9_0_36,
  collectedFourData_9_0_37,
  collectedFourData_9_0_38,
  collectedFourData_9_0_39,
  collectedFourData_9_0_40,
  collectedFourData_9_0_41,
  collectedFourData_9_0_42,
  collectedFourData_9_0_43
]

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0915
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0915. -/
namespace LaughlinFock

def collectedFourData_9_3 : List (List CollectedFourTerm) := [
  collectedFourData_9_3_0,
  collectedFourData_9_3_1,
  collectedFourData_9_3_2,
  collectedFourData_9_3_3,
  collectedFourData_9_3_4,
  collectedFourData_9_3_5,
  collectedFourData_9_3_6,
  collectedFourData_9_3_7,
  collectedFourData_9_3_8,
  collectedFourData_9_3_9,
  collectedFourData_9_3_10,
  collectedFourData_9_3_11,
  collectedFourData_9_3_12,
  collectedFourData_9_3_13,
  collectedFourData_9_3_14,
  collectedFourData_9_3_15,
  collectedFourData_9_3_16,
  collectedFourData_9_3_17,
  collectedFourData_9_3_18,
  collectedFourData_9_3_19,
  collectedFourData_9_3_20,
  collectedFourData_9_3_21,
  collectedFourData_9_3_22,
  collectedFourData_9_3_23,
  collectedFourData_9_3_24,
  collectedFourData_9_3_25,
  collectedFourData_9_3_26,
  collectedFourData_9_3_27,
  collectedFourData_9_3_28,
  collectedFourData_9_3_29,
  collectedFourData_9_3_30,
  collectedFourData_9_3_31,
  collectedFourData_9_3_32,
  collectedFourData_9_3_33,
  collectedFourData_9_3_34,
  collectedFourData_9_3_35,
  collectedFourData_9_3_36,
  collectedFourData_9_3_37,
  collectedFourData_9_3_38,
  collectedFourData_9_3_39,
  collectedFourData_9_3_40,
  collectedFourData_9_3_41,
  collectedFourData_9_3_42,
  collectedFourData_9_3_43,
  collectedFourData_9_3_44,
  collectedFourData_9_3_45,
  collectedFourData_9_3_46,
  collectedFourData_9_3_47,
  collectedFourData_9_3_48,
  collectedFourData_9_3_49,
  collectedFourData_9_3_50,
  collectedFourData_9_3_51,
  collectedFourData_9_3_52,
  collectedFourData_9_3_53,
  collectedFourData_9_3_54,
  collectedFourData_9_3_55
]

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0930
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0930. -/
namespace LaughlinFock

def collectedFourData_9_7 : List (List CollectedFourTerm) := [
  collectedFourData_9_7_0,
  collectedFourData_9_7_1,
  collectedFourData_9_7_2,
  collectedFourData_9_7_3,
  collectedFourData_9_7_4,
  collectedFourData_9_7_5,
  collectedFourData_9_7_6,
  collectedFourData_9_7_7,
  collectedFourData_9_7_8,
  collectedFourData_9_7_9,
  collectedFourData_9_7_10,
  collectedFourData_9_7_11,
  collectedFourData_9_7_12,
  collectedFourData_9_7_13,
  collectedFourData_9_7_14,
  collectedFourData_9_7_15,
  collectedFourData_9_7_16,
  collectedFourData_9_7_17,
  collectedFourData_9_7_18,
  collectedFourData_9_7_19,
  collectedFourData_9_7_20,
  collectedFourData_9_7_21,
  collectedFourData_9_7_22,
  collectedFourData_9_7_23,
  collectedFourData_9_7_24,
  collectedFourData_9_7_25,
  collectedFourData_9_7_26,
  collectedFourData_9_7_27,
  collectedFourData_9_7_28,
  collectedFourData_9_7_29,
  collectedFourData_9_7_30,
  collectedFourData_9_7_31,
  collectedFourData_9_7_32,
  collectedFourData_9_7_33,
  collectedFourData_9_7_34,
  collectedFourData_9_7_35,
  collectedFourData_9_7_36,
  collectedFourData_9_7_37,
  collectedFourData_9_7_38,
  collectedFourData_9_7_39,
  collectedFourData_9_7_40,
  collectedFourData_9_7_41,
  collectedFourData_9_7_42,
  collectedFourData_9_7_43
]

def collectedFourData_9 : Fin 8 → List (List CollectedFourTerm) :=
  ![collectedFourData_9_0, collectedFourData_9_1, collectedFourData_9_2, collectedFourData_9_3, collectedFourData_9_4, collectedFourData_9_5, collectedFourData_9_6, collectedFourData_9_7]

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate09
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate09. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_9 : List (Occupation 24 × List ℚ) := fourHighestCache_9_0 ++ fourHighestCache_9_1

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate10Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate10 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourLData_10 : Matrix (CopyLabel 10) (CopyLabel 10) ℚ :=
  copyMatrixData 10 [
    [1, 0, 0, 0, 0],
    [0, 1, 0, 0, 0],
    [0, 0, 1, 0, 0],
    [0, (-3/16), 0, 1, 0],
    [0, (3/8), 0, 0, 1]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1605
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1605. -/
namespace LaughlinFock

def collectedFourData_16 : List CollectedFourTerm := ((((((collectedFourData_16_0 ++ (collectedFourData_16_1 ++ collectedFourData_16_2)) ++ (collectedFourData_16_3 ++ (collectedFourData_16_4 ++ collectedFourData_16_5))) ++ ((collectedFourData_16_6 ++ (collectedFourData_16_7 ++ collectedFourData_16_8)) ++ (collectedFourData_16_9 ++ (collectedFourData_16_10 ++ collectedFourData_16_11)))) ++ (((collectedFourData_16_12 ++ (collectedFourData_16_13 ++ collectedFourData_16_14)) ++ (collectedFourData_16_15 ++ (collectedFourData_16_16 ++ collectedFourData_16_17))) ++ ((collectedFourData_16_18 ++ (collectedFourData_16_19 ++ collectedFourData_16_20)) ++ ((collectedFourData_16_21 ++ collectedFourData_16_22) ++ (collectedFourData_16_23 ++ collectedFourData_16_24))))) ++ ((((collectedFourData_16_25 ++ (collectedFourData_16_26 ++ collectedFourData_16_27)) ++ (collectedFourData_16_28 ++ (collectedFourData_16_29 ++ collectedFourData_16_30))) ++ ((collectedFourData_16_31 ++ (collectedFourData_16_32 ++ collectedFourData_16_33)) ++ ((collectedFourData_16_34 ++ collectedFourData_16_35) ++ (collectedFourData_16_36 ++ collectedFourData_16_37)))) ++ (((collectedFourData_16_38 ++ (collectedFourData_16_39 ++ collectedFourData_16_40)) ++ (collectedFourData_16_41 ++ (collectedFourData_16_42 ++ collectedFourData_16_43))) ++ ((collectedFourData_16_44 ++ (collectedFourData_16_45 ++ collectedFourData_16_46)) ++ ((collectedFourData_16_47 ++ collectedFourData_16_48) ++ (collectedFourData_16_49 ++ collectedFourData_16_50)))))) ++ (((((collectedFourData_16_51 ++ (collectedFourData_16_52 ++ collectedFourData_16_53)) ++ (collectedFourData_16_54 ++ (collectedFourData_16_55 ++ collectedFourData_16_56))) ++ ((collectedFourData_16_57 ++ (collectedFourData_16_58 ++ collectedFourData_16_59)) ++ (collectedFourData_16_60 ++ (collectedFourData_16_61 ++ collectedFourData_16_62)))) ++ (((collectedFourData_16_63 ++ (collectedFourData_16_64 ++ collectedFourData_16_65)) ++ (collectedFourData_16_66 ++ (collectedFourData_16_67 ++ collectedFourData_16_68))) ++ ((collectedFourData_16_69 ++ (collectedFourData_16_70 ++ collectedFourData_16_71)) ++ ((collectedFourData_16_72 ++ collectedFourData_16_73) ++ (collectedFourData_16_74 ++ collectedFourData_16_75))))) ++ ((((collectedFourData_16_76 ++ (collectedFourData_16_77 ++ collectedFourData_16_78)) ++ (collectedFourData_16_79 ++ (collectedFourData_16_80 ++ collectedFourData_16_81))) ++ ((collectedFourData_16_82 ++ (collectedFourData_16_83 ++ collectedFourData_16_84)) ++ ((collectedFourData_16_85 ++ collectedFourData_16_86) ++ (collectedFourData_16_87 ++ collectedFourData_16_88)))) ++ (((collectedFourData_16_89 ++ (collectedFourData_16_90 ++ collectedFourData_16_91)) ++ (collectedFourData_16_92 ++ (collectedFourData_16_93 ++ collectedFourData_16_94))) ++ ((collectedFourData_16_95 ++ (collectedFourData_16_96 ++ collectedFourData_16_97)) ++ ((collectedFourData_16_98 ++ collectedFourData_16_99) ++ (collectedFourData_16_100 ++ collectedFourData_16_101)))))))

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate16Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate16 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourLData_16 : Matrix (CopyLabel 16) (CopyLabel 16) ℚ :=
  copyMatrixData 16 [
    [1, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0],
    [0, (2662114609823252321446554735/31846883619456444318310735886), 1, 0, 0, 0, 0, 0],
    [0, (-17360028699934957438187203593/254775068955651554546485887088), (8465590199751968259176205997398130465255792473891241/1203382170043606369261657898744251670892140198195617080), 1, 0, 0, 0, 0],
    [0, (640570914407014793429222681/127387534477825777273242943544), (436797514031755906616504442343241048612038835260569/80225478002907091284110526582950111392809346546374472), (-1275194507514036637278365937230604879105104344465161974052430467237510230580/11008773474816855464614116596323385562037106374777989640768967739311575751573), 1, 0, 0, 0],
    [0, (11611413667826677607464701735/509550137911303109092971774176), (-194613665775878056818579803761786280887342230583992893/3850822944139540381637305275981605346854848634225974656), (-56439349625015857914692290450676628694242661968005386360520314081135354041545/176140375597069687433825865541174168992593701996447834252303483828985212025168), (-165/112), 1, 0, 0],
    [0, (-1840313747998192277792824497/46322739810118464462997434016), (287240814382777194295671681721906343167860587762014927/19254114720697701908186526379908026734274243171129873280), (146742309025041230578199955171759234605030921116814004537352816610951920508017/352280751194139374867651731082348337985187403992895668504606967657970424050336), (429/224), 0, 1, 0],
    [0, (63294652727275802726767645065/1019100275822606218185943548352), (987596636001863499622501810331762538010156135684222467/2567215296093026921091536850654403564569899089483983104), (227941018218134048913507911279970622140037401573147702861871946018704953716175/704561502388278749735303462164696675970374807985791337009213935315940848100672), (-715/256), 0, 0, 1]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate17. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_17 : List (Occupation 24 × List ℚ) := fourHighestCache_17_0 ++ fourHighestCache_17_1 ++ fourHighestCache_17_2 ++ fourHighestCache_17_3 ++ fourHighestCache_17_4 ++ fourHighestCache_17_5 ++ fourHighestCache_17_6 ++ fourHighestCache_17_7 ++ fourHighestCache_17_8

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate19Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate19 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourLData_19 : Matrix (CopyLabel 19) (CopyLabel 19) ℚ :=
  copyMatrixData 19 [
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [(-2020011531631846969177200/1202639047713818742631803172201), 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [(23595088792077008460858915/76968899053684399528435403020864), (-5822692808407349938912024178421113542355995713624115777/31262571384967907735769652165612355825696278835743059616), 1, 0, 0, 0, 0, 0, 0, 0],
    [(-6451764561601397527869641/153937798107368799056870806041728), (2503750154892137909913496822537882251630356635271327065/62525142769935815471539304331224711651392557671486119232), (-92774401214903063949344590108787205519457990348578712381666279529750347731/168418625539847275664136167095522878077741314813553176311666683135166901682), 1, 0, 0, 0, 0, 0, 0],
    [(-3991241748017824922059479/307875596214737598113741612083456), (-424440986191928747792654883979978928826133369553726583/250100571079743261886157217324898846605570230685944476928), (292552408649523873184750356531382741673385640896547717852755738972549700203/3368372510796945513282723341910457561554826296271063526233333662703338033640), (-9686261414621178345199795745128428396957249184590196228783883175168413330877698894846027553/13809778020376421591169151541712996318383052045070770607444688987375008635459809794761716924), 1, 0, 0, 0, 0, 0],
    [(772800113721185652704523/615751192429475196227483224166912), (1385142357177886757041123943329631902700428160389838855/500201142159486523772314434649797693211140461371888953856), (-32581241124941751750352214972586545115893793027678406661240754676955279473/336837251079694551328272334191045756155482629627106352623333366270333803364), (3251016691257014358611121593521969021370373108242937325123146042503015433752498856034179231/13809778020376421591169151541712996318383052045070770607444688987375008635459809794761716924), (-2122231202756391713145325083545292842288303167896135143392823227018143507956047460325521849288415365/15870638051051129919271535319839481602043326225695621661360980618060215480300545072063250228599005104), 1, 0, 0, 0, 0],
    [(2811778187557848892254875/307875596214737598113741612083456), (-1509785959510237917930593179397250973442741161169160203/250100571079743261886157217324898846605570230685944476928), (6401774252120685662357585571886157870975114629754590565441298796897955427111/47157215151157237185958126786746405861767568147794889367266671277846732470960), (18729047246966666079667574135347429918773885130339118875816720849736745793810665416263379983/3093390276564318436421889945343711175317803658095852616067610333172001934342997394026624590976), (-128094774302086004238884690032304206718133114297639347331085824516047259085717351746740342242370764701/296251910286287758493068659303670323238142089546318271012071638203790688965610174678514004267181428608), (-6702785262915535022085814294995920066692670055957138446674674798735073316329511157131562446168655168296380347/4264045600302034874792061579880963129330136297602065715110861053443518810565784897268444808748010548014575944), 1, 0, 0, 0],
    [(-13993580349908417522901555/1231502384858950392454966448333824), (6272560116072020767460314837271369997611582439691541385/1000402284318973047544628869299595386422280922743777907712), (-53994202807818727880203037240236812292585294681520751894397546531524863076/421046563849618189160340417738807195194353287033882940779166707837917254205), (-40098902593236325891789226096139882314755846076938467183475906989123414139838158185502713333/441912896652045490917412849334815882188257665442264659438230047596000276334713913432374941568), (32770074676248522710006638816111908772902096028501605030943516753614473499893798307524222067677526869/63482552204204519677086141279357926408173304902782486645443922472240861921202180288253000914396020416), (563607842048940847817534681407895588619244881444636054709299988710470948500694807584354119739423491219929061/304574685735859633913718684277211652095009735543004693936490075245965629326127492662031772053429324858183996), (-9/2), 1, 0, 0],
    [(-18350121065500000000000000/1202639047713818742631803172201), (-313600733812462986419512299537214253490000000000000/976955355780247116742801630175386119553008713616970613), (441570846180885198909046659227810858111826365890906336956256556000000000/84209312769923637832068083547761439038870657406776588155833341567583450841), (131645772084642511409985537258103541019401171342814414409646572578055364474948577099609375/6904889010188210795584575770856498159191526022535385303722344493687504317729904897380858462), (11312548259316076855245775593721245396374151409654469795096913062573833380412020467169874330265475505/72551488233376593916669875747837630180769491317465699023364482825418127909945348900860572473595451904), (-4464100423831520588262797324649000680699963188046352726804700693944857034202148761387233561981806136560432081/2436597485886877071309749474217693216760077884344037551491920601967725034609019941296254176427434598865471968), (85/4), 0, 1, 0],
    [(697304609035580000000000000/1202639047713818742631803172201), (13978478272021385777459991602037106843824375000000000/976955355780247116742801630175386119553008713616970613), (6717416019148967780259088242587558144193978697225759002148282681500000000/84209312769923637832068083547761439038870657406776588155833341567583450841), (7705138308084153675883035243414537786376683952106186448166916362765958097789103370666015625/110478224163011372729353212333703970547064416360566164859557511899000069083678478358093735392), (578594629283587183301293481989396418779507290411938707222981396191981046305649679474498620292164629795/677147223511514876555585506979817881687181918963013190884735173037235860492823256408032009753557551104), (11726613515986148404227844711992671967876439443152177866396077750214029128556582266077138798517899565228513013/9746389943547508285238997896870772867040311537376150205967682407870900138436079765185016705709738395461887872), (-969/4), 0, 0, 1]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate19. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_19 : List (Occupation 24 × List ℚ) := fourHighestCache_19_0 ++ fourHighestCache_19_1 ++ fourHighestCache_19_2 ++ fourHighestCache_19_3 ++ fourHighestCache_19_4 ++ fourHighestCache_19_5 ++ fourHighestCache_19_6 ++ fourHighestCache_19_7 ++ fourHighestCache_19_8 ++ fourHighestCache_19_9 ++ fourHighestCache_19_10 ++ fourHighestCache_19_11

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate20Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate20 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourLData_20 : Matrix (CopyLabel 20) (CopyLabel 20) ℚ :=
  copyMatrixData 20 [
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, (-8126138115145743032553165/62284328069371912383859672), 1, 0, 0, 0, 0, 0, 0, 0],
    [0, (1626803167008096359790661/45297693141361390824625216), (-17449910457629697811253768910994745334764785247/36126952092093301262412516311431044434338593352), 1, 0, 0, 0, 0, 0, 0],
    [0, (-2741391634246070130778671/249137312277487649535438688), (1710747011218568525172761259487667720823745509/9031738023023325315603129077857761108584648338), (-1409880132621320206328277901568423102070009205103214981952464878/3672486685330114611812244238666481186928923369975629714230340569), 1, 0, 0, 0, 0, 0],
    [0, (-3468403531570060272169437/996549249109950598141754752), (-54206663627697249243209181831639780932965256217/1445078083683732050496500652457241777373543734080), (-2682669873345268677667448439108508517833436035126757303806715923/48966489137734861490829923182219749159052311599675062856404540920), (390940692538680577286483357680346542717307071740235885579397866444341/1011471242142306678707331123629264075534347116402293932285940459557840), 1, 0, 0, 0, 0],
    [0, (6404262476599127023962681/996549249109950598141754752), (-12271060906794183557615921331520007198784539277/1445078083683732050496500652457241777373543734080), (280398844021620654558483485855868622071510682688491918102282355137/1762793608958455013669877234559910969725883217588302262830563473120), (-1788682496537489510987861678551568040817933777893676875060518069228257241/2497322496849355189728400544240653002494303030397263718813986994648306960), (-205442230950505060736566456171910121044619455031873133064218660750573987/187661331655209709927001310658363823865769463148584900488167563297275181), 1, 0, 0, 0],
    [0, (-8779322327759465983491715/1993098498219901196283509504), (6687041020002338097601109864075674474307238385/578031233473492820198600260982896710949417493632), (-42814016882767727606104144332365856781212582674220992676967182959/352558721791691002733975446911982193945176643517660452566112694624), (1378947132065935572460680545276594936012831841923306016261338517800366171/3995715994958968303565440870785044803990884848635621950102379191437291136), (802545190924812102496849755024902631767861005683116612021376985492540565/1125967989931258259562007863950182943194616778891509402929005379783651086), (-25/8), 1, 0, 0],
    [0, (-5821120000000000000/158888592013703858122091), (-3768460864257326460101079607735000000000000/4515869011511662657801564538928880554292324169), (10368215532090329941304000763197677462009911340790522500000000/1224162228443371537270748079555493728976307789991876571410113523), (13657845482385131284239371109165770160170064532345695293305985047596369/39173686225087924544759224223382792195989067143486489706886070504287168), (-437060818101686496392267403571259618767317470664856137215575304419278347/4503871959725033038248031455800731772778467115566037611716021519134604344), (17/2), 0, 1, 0],
    [0, (74810790000000000000/158888592013703858122091), (237273681736773465102203726552459568750000000/4515869011511662657801564538928880554292324169), (473756356311740932404506082590313071478423778982982285390625000/3672486685330114611812244238666481186928923369975629714230340569), (1013166684682223083025523920336107583474332845429774647175845986566229847/1253557959202813585432295175148249350271650148591567670620354256137189376), (8304155543932043431453080667853932756579031942632266607095930783966288593/24020650451866842870656167764270569454818491283018867262485448102051223168), (-969/32), 0, 0, 1]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate20. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_20 : List (Occupation 24 × List ℚ) := fourHighestCache_20_0 ++ fourHighestCache_20_1 ++ fourHighestCache_20_2 ++ fourHighestCache_20_3 ++ fourHighestCache_20_4 ++ fourHighestCache_20_5 ++ fourHighestCache_20_6 ++ fourHighestCache_20_7 ++ fourHighestCache_20_8 ++ fourHighestCache_20_9 ++ fourHighestCache_20_10 ++ fourHighestCache_20_11 ++ fourHighestCache_20_12 ++ fourHighestCache_20_13

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate21Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate21 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourLData_21 : Matrix (CopyLabel 21) (CopyLabel 21) ℚ :=
  copyMatrixData 21 [
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [(-8548810830947288451141/274878635986343591102561497660), 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [(-124033985403178175655/219902908789074872882049198128), (-14757153203417715518299991021934558935177667165/664024150087302063112879796744004241924426401196), 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [(2502160081413933716363/4398058175781497457640983962560), (3717840143772810771232079066398195689997611923/758884742956916643557576910564576276485058744224), (-272120122881938716411038525475117483470012132201638363/1944332809753462405897919792357279092639701896778055352), 1, 0, 0, 0, 0, 0, 0, 0],
    [(-4780377743058242070237/3518446540625197966112787170048), (148130422718292903990730772372544184241501467375/21248772802793666019612153495808135741581644838272), (1060352093934662093745636740340484304893072449165496869/7777331239013849623591679169429116370558807587112221408), (-8696142136303731809503584984093518274929264230276958063583717/20356877660929408298126406948592442600862047332351177536071132), 1, 0, 0, 0, 0, 0, 0],
    [(10830972661073344317609/7036893081250395932225574340096), (-57677155233072884366416276570083396963443536985/6071077943655333148460615284516610211880469953792), (-1970344530863121207550101349261994845945854550790137131/15554662478027699247183358338858232741117615174224442816), (38207069769285224485772860920057454973853491492633905148388075/81427510643717633192505627794369770403448189329404710144284528), (-138329320388805368201372891238915548986397179867976432281875152058115/155701753873727721118627377208199250545659698359367240448402652202952), 1, 0, 0, 0, 0, 0],
    [(-17311727787538344820711/17592232703125989830563935850240), (132254071891215471295105810273731761612249021753/21248772802793666019612153495808135741581644838272), (4821425922303353707480669215275945173579945024230113285/62218649912110796988733433355432930964470460696897771264), (-97709222793993804444913676366268135892960181911157904449585659/325710042574870532770022511177479081613792757317618840577138112), (341084326270111014094851110796381720994679419404112880192884076287269/622807015494910884474509508832797002182638793437468961793610608811808), (-30113940812185690096786889911085352658321628449549602053881427639667038989/42502993933828826340640487872958883980979259340828174783761707040935098636), 1, 0, 0, 0, 0],
    [(5740134976371624297975/14073786162500791864451148680192), (-20095565573109783113174308549806538916670646795/7726826473743151279858964907566594815120598123008), (-996785994407829034966439075010854702175460163381861913/31109324956055398494366716677716465482235230348448885632), (139261359168545739689039703818210473377229189472973893422828635/1302840170299482131080090044709916326455171029270475362308552448), (-674790097504517865140318623403218646850793520710174505343090952175795/2491228061979643537898038035331188008730555173749875847174442435247232), (22283909766527630160101788746935083691737896861232873693998231553010260385/170011975735315305362561951491835535923917037363312699135046828163740394544), (-45590055979219358411386711012075048322811174736837613418901268346051295341915/20405411281542024974131140470047325652742245613561572522118498602025493474776), 1, 0, 0, 0],
    [(459900000000000/13743931799317179555128074883), (-1449802258970314775428257010308392187500000/23715148217403645111174278455143008640158085757), (-2395255250761331989568356939773718639755575142402034395/995498398593772751819734933686926895431527371150364340224), (-13418176075736194356537502364762088341877229146860666334375015/5211360681197928524320360178839665305820684117081901449234209792), (487865575284756334992773906895746705106398651519135056854571107548959/9964912247918574151592152141324752034922220694999503388697769740988928), (489775601242945684391979977752120194834021229547456876965929983663917306267/2040143708823783664350743417902026431087004448359752389620561937964884734528), (43505192969491182132926799872582277695073580574000721485545373586935100532485/11660235018024014270932080268598471801566997493463755726924856344014567699872), (-119/20), 1, 0, 0],
    [(-3084053983975000000000/808466576430422326772239699), (-6630744430914671133930860629859883984375000/166006037521825515778219949186001060481106600299), (997633968783156110923401994511741399639161255134118197/62218649912110796988733433355432930964470460696897771264), (3971793243161119563670601187158757516771615055247800795636706895/20845442724791714097281440715358661223282736468327605796936839168), (8039897538616978997115340898140436139443964333369611655401031990883023/39859648991674296606368608565299008139688882779998013554791078963955712), (906375549329927009412754792175289405907055876156100252396610809398220865557/2720191611765044885800991223869368574782672597813003186160749250619846312704), (-1790004131550357230463889888075609897998371992570933724333165984690844140466951/326486580504672399586098247520757210443875929816985160353895977632407895596416), (2907/80), 0, 1, 0],
    [(2477266373939568750000000/13743931799317179555128074883), (517910555825304382493487680612287469628906250/23715148217403645111174278455143008640158085757), (2545009274178797313715242194361019417755624297612648023301/15927974377500364029115758938990830326904437938405829443584), (8605765564944287811353984318618871043684221188569515573437797995/11911681557023836627017966123062092127590135124758631883963908096), (-7011887382412585013867388065737146253750710922098621848169972681187625/22776942280956740917924919180170861794107933017141722031309187979403264), (3359044370757364557384621321141036500278741566062717005569520857539523946491/10880766447060179543203964895477474299130690391252012744642997002479385250816), (-1560668513592208246078480195599799647936263394859855442167637748711884810323695/186563760288384228334913284297575548825071959895420091630797701504233083197952), (-33915/64), 0, 0, 1]
  ]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate21. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_21 : List (Occupation 24 × List ℚ) := fourHighestCache_21_0 ++ fourHighestCache_21_1 ++ fourHighestCache_21_2 ++ fourHighestCache_21_3 ++ fourHighestCache_21_4 ++ fourHighestCache_21_5 ++ fourHighestCache_21_6 ++ fourHighestCache_21_7 ++ fourHighestCache_21_8 ++ fourHighestCache_21_9 ++ fourHighestCache_21_10 ++ fourHighestCache_21_11 ++ fourHighestCache_21_12 ++ fourHighestCache_21_13 ++ fourHighestCache_21_14 ++ fourHighestCache_21_15

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate22Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate22 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourPivotData_22 : CopyLabel 22 → ℚ :=
  copyDiagonalData 22 [0, (252477167008626784680769368338283/131072000000000000000), (5512078762303357411618169673832059/439665310840577577157120), (174310682459542995847618821831459734200779/406749418508285119207187210567680), (62404806161650616515384108365273134448230433/1650762092055920072921522129458624000), (1853038138367273847451704609262271325740924925561/359435203904749656793865793338669033062400), (93365306868407495301616487806062763484680988634866769/867182089706185958462280668530801767094845440000), (248386774123325334530722962536243545224925735855560001827/50477692865647294731437465522510224253388848145367040), 0, 0, 0]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate22. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_22 : List (Occupation 24 × List ℚ) := fourHighestCache_22_0 ++ fourHighestCache_22_1 ++ fourHighestCache_22_2 ++ fourHighestCache_22_3 ++ fourHighestCache_22_4 ++ fourHighestCache_22_5 ++ fourHighestCache_22_6 ++ fourHighestCache_22_7 ++ fourHighestCache_22_8 ++ fourHighestCache_22_9 ++ fourHighestCache_22_10 ++ fourHighestCache_22_11 ++ fourHighestCache_22_12 ++ fourHighestCache_22_13 ++ fourHighestCache_22_14 ++ fourHighestCache_22_15 ++ fourHighestCache_22_16 ++ fourHighestCache_22_17

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate23. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_23 : List (Occupation 24 × List ℚ) := fourHighestCache_23_0 ++ fourHighestCache_23_1 ++ fourHighestCache_23_2 ++ fourHighestCache_23_3 ++ fourHighestCache_23_4 ++ fourHighestCache_23_5 ++ fourHighestCache_23_6 ++ fourHighestCache_23_7 ++ fourHighestCache_23_8 ++ fourHighestCache_23_9 ++ fourHighestCache_23_10 ++ fourHighestCache_23_11 ++ fourHighestCache_23_12 ++ fourHighestCache_23_13 ++ fourHighestCache_23_14 ++ fourHighestCache_23_15 ++ fourHighestCache_23_16 ++ fourHighestCache_23_17 ++ fourHighestCache_23_18 ++ fourHighestCache_23_19 ++ fourHighestCache_23_20

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_PairDecomposition
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Decomposition. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

 

def fourCouplingMatrix (Q : ℕ) :
    Matrix (PairLabel Q × PairLabel Q) (CoupledIndex (2*Q-2) (2*Q-2)) ℂ :=
  fun pq c => coupledVector (2*Q-2) (2*Q-2) c.1.val c.2.val pq.1.val pq.2.val



def fourCoupledWedgeMatrix (Q : ℕ) :
    Matrix (SectorOccupation Q 4) (CoupledIndex (2*Q-2) (2*Q-2)) ℂ :=
  fourWedgeMatrix Q * fourCouplingMatrix Q


def fourCoupledAnnihilator (Q z k : ℕ) : FockMatrix Q :=
  ∑ p : PairLabel Q, ∑ q : PairLabel Q,
    (coupledVector (2*Q-2) (2*Q-2) z k p.val q.val : ℂ) •
      (pairAnnihilator Q q.val * pairAnnihilator Q p.val)



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_CopyVectors
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Copy Vectors. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder



def composedFourWedgeColumn (Q r z k : ℕ) : SectorOccupation Q 4 → ℂ :=
  wideFourWedgeMatrix Q *ᵥ fun b => (composedCoupledVector Q r z k b : ℂ)

 
def composedFourAnnihilator (Q r z k : ℕ) : FockMatrix Q :=
  ∑ b : FourUncoupled Q, (composedCoupledVector Q r z k b : ℂ) •
    (annihilator Q b.2.val.2 * annihilator Q b.2.val.1 * pairAnnihilator Q b.1.val)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_CoupledLie
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coupled Lie. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def coupledSpinMatrix (n m z : ℕ) :
    Matrix (Fin (n+1) × Fin (m+1)) (Fin (n+m-2*z+1)) ℂ := fun ij k =>
  (coupledVector n m z k.val ij.1.val ij.2.val : ℂ)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourBasis
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Basis. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def oddPairColumns (Q r : ℕ) :
    Matrix (IncreasingPair Q) (Fin (2*Q-2*r+1)) ℂ :=
  fun b k => wedgeCoupledCoefficient Q r k.val b


def fourFactorEmbedding (Q r : ℕ) :
    Matrix (FourUncoupled Q) (Fin (2*Q-2+1) × Fin (2*Q-2*r+1)) ℂ :=
  Matrix.kronecker 1 (oddPairColumns Q r)

 
def composedCouplingMatrix (Q r : ℕ) :
    Matrix (FourUncoupled Q) (CoupledIndex (2*Q-2) (2*Q-2*r)) ℂ :=
  fun b c => composedCoupledVector Q r c.1.val c.2.val b

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourCopies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Copies. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourCopyColumns (Q D : ℕ) (r : CopyLabel D) :
    Matrix (FourUncoupled Q) (Fin (fourSpinDegree Q D+1)) ℂ :=
  if D+r.val.val ≤ 2*Q then
    fun b k => (composedCoupledVector Q r.val.val (D-r.val.val) k.val b : ℂ)
  else 0


def fourCopyWedge (Q D : ℕ) (r : CopyLabel D) :
    Matrix (SectorOccupation Q 4) (Fin (fourSpinDegree Q D+1)) ℂ :=
  wideFourWedgeMatrix Q * fourCopyColumns Q D r



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourCopyLift (Q D : ℕ) (r s : CopyLabel D) : FockMatrix Q :=
  exteriorLift Q 4 (fourCopyWedge Q D r*(fourCopyWedge Q D s)ᴴ)



end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0807
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0807. -/
namespace LaughlinFock

def collectedFourData_8_1 : List (List CollectedFourTerm) := [
  collectedFourData_8_1_0,
  collectedFourData_8_1_1,
  collectedFourData_8_1_2,
  collectedFourData_8_1_3,
  collectedFourData_8_1_4,
  collectedFourData_8_1_5,
  collectedFourData_8_1_6,
  collectedFourData_8_1_7,
  collectedFourData_8_1_8,
  collectedFourData_8_1_9,
  collectedFourData_8_1_10,
  collectedFourData_8_1_11,
  collectedFourData_8_1_12,
  collectedFourData_8_1_13,
  collectedFourData_8_1_14,
  collectedFourData_8_1_15,
  collectedFourData_8_1_16,
  collectedFourData_8_1_17,
  collectedFourData_8_1_18,
  collectedFourData_8_1_19,
  collectedFourData_8_1_20,
  collectedFourData_8_1_21,
  collectedFourData_8_1_22,
  collectedFourData_8_1_23,
  collectedFourData_8_1_24,
  collectedFourData_8_1_25,
  collectedFourData_8_1_26,
  collectedFourData_8_1_27,
  collectedFourData_8_1_28,
  collectedFourData_8_1_29,
  collectedFourData_8_1_30,
  collectedFourData_8_1_31,
  collectedFourData_8_1_32,
  collectedFourData_8_1_33,
  collectedFourData_8_1_34,
  collectedFourData_8_1_35,
  collectedFourData_8_1_36,
  collectedFourData_8_1_37,
  collectedFourData_8_1_38,
  collectedFourData_8_1_39,
  collectedFourData_8_1_40,
  collectedFourData_8_1_41,
  collectedFourData_8_1_42,
  collectedFourData_8_1_43,
  collectedFourData_8_1_44,
  collectedFourData_8_1_45,
  collectedFourData_8_1_46,
  collectedFourData_8_1_47,
  collectedFourData_8_1_48,
  collectedFourData_8_1_49
]

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0821
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0821. -/
namespace LaughlinFock

def collectedFourData_8_4 : List (List CollectedFourTerm) := [
  collectedFourData_8_4_0,
  collectedFourData_8_4_1,
  collectedFourData_8_4_2,
  collectedFourData_8_4_3,
  collectedFourData_8_4_4,
  collectedFourData_8_4_5,
  collectedFourData_8_4_6,
  collectedFourData_8_4_7,
  collectedFourData_8_4_8,
  collectedFourData_8_4_9,
  collectedFourData_8_4_10,
  collectedFourData_8_4_11,
  collectedFourData_8_4_12,
  collectedFourData_8_4_13,
  collectedFourData_8_4_14,
  collectedFourData_8_4_15,
  collectedFourData_8_4_16,
  collectedFourData_8_4_17,
  collectedFourData_8_4_18,
  collectedFourData_8_4_19,
  collectedFourData_8_4_20,
  collectedFourData_8_4_21,
  collectedFourData_8_4_22,
  collectedFourData_8_4_23,
  collectedFourData_8_4_24,
  collectedFourData_8_4_25,
  collectedFourData_8_4_26,
  collectedFourData_8_4_27,
  collectedFourData_8_4_28,
  collectedFourData_8_4_29,
  collectedFourData_8_4_30,
  collectedFourData_8_4_31,
  collectedFourData_8_4_32,
  collectedFourData_8_4_33,
  collectedFourData_8_4_34,
  collectedFourData_8_4_35,
  collectedFourData_8_4_36,
  collectedFourData_8_4_37,
  collectedFourData_8_4_38,
  collectedFourData_8_4_39,
  collectedFourData_8_4_40,
  collectedFourData_8_4_41,
  collectedFourData_8_4_42,
  collectedFourData_8_4_43,
  collectedFourData_8_4_44,
  collectedFourData_8_4_45,
  collectedFourData_8_4_46,
  collectedFourData_8_4_47,
  collectedFourData_8_4_48,
  collectedFourData_8_4_49,
  collectedFourData_8_4_50,
  collectedFourData_8_4_51,
  collectedFourData_8_4_52,
  collectedFourData_8_4_53,
  collectedFourData_8_4_54,
  collectedFourData_8_4_55
]

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0833
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0833. -/
namespace LaughlinFock

def collectedFourData_8 : Fin 8 → List (List CollectedFourTerm) :=
  ![collectedFourData_8_0, collectedFourData_8_1, collectedFourData_8_2, collectedFourData_8_3, collectedFourData_8_4, collectedFourData_8_5, collectedFourData_8_6, collectedFourData_8_7]

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1102. -/
namespace LaughlinFock

def collectedFourData_11_0 : List (List CollectedFourTerm) := [
  collectedFourData_11_0_0,
  collectedFourData_11_0_1,
  collectedFourData_11_0_2,
  collectedFourData_11_0_3,
  collectedFourData_11_0_4,
  collectedFourData_11_0_5,
  collectedFourData_11_0_6,
  collectedFourData_11_0_7,
  collectedFourData_11_0_8,
  collectedFourData_11_0_9,
  collectedFourData_11_0_10,
  collectedFourData_11_0_11,
  collectedFourData_11_0_12,
  collectedFourData_11_0_13,
  collectedFourData_11_0_14,
  collectedFourData_11_0_15,
  collectedFourData_11_0_16,
  collectedFourData_11_0_17,
  collectedFourData_11_0_18,
  collectedFourData_11_0_19,
  collectedFourData_11_0_20,
  collectedFourData_11_0_21,
  collectedFourData_11_0_22,
  collectedFourData_11_0_23,
  collectedFourData_11_0_24,
  collectedFourData_11_0_25,
  collectedFourData_11_0_26,
  collectedFourData_11_0_27,
  collectedFourData_11_0_28,
  collectedFourData_11_0_29,
  collectedFourData_11_0_30,
  collectedFourData_11_0_31,
  collectedFourData_11_0_32,
  collectedFourData_11_0_33,
  collectedFourData_11_0_34,
  collectedFourData_11_0_35,
  collectedFourData_11_0_36,
  collectedFourData_11_0_37,
  collectedFourData_11_0_38,
  collectedFourData_11_0_39,
  collectedFourData_11_0_40,
  collectedFourData_11_0_41,
  collectedFourData_11_0_42,
  collectedFourData_11_0_43
]

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1108
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1108. -/
namespace LaughlinFock

def collectedFourData_11_2 : List (List CollectedFourTerm) := [
  collectedFourData_11_2_0,
  collectedFourData_11_2_1,
  collectedFourData_11_2_2,
  collectedFourData_11_2_3,
  collectedFourData_11_2_4,
  collectedFourData_11_2_5,
  collectedFourData_11_2_6,
  collectedFourData_11_2_7,
  collectedFourData_11_2_8,
  collectedFourData_11_2_9,
  collectedFourData_11_2_10,
  collectedFourData_11_2_11,
  collectedFourData_11_2_12,
  collectedFourData_11_2_13,
  collectedFourData_11_2_14,
  collectedFourData_11_2_15,
  collectedFourData_11_2_16,
  collectedFourData_11_2_17,
  collectedFourData_11_2_18,
  collectedFourData_11_2_19,
  collectedFourData_11_2_20,
  collectedFourData_11_2_21,
  collectedFourData_11_2_22,
  collectedFourData_11_2_23,
  collectedFourData_11_2_24,
  collectedFourData_11_2_25,
  collectedFourData_11_2_26,
  collectedFourData_11_2_27,
  collectedFourData_11_2_28,
  collectedFourData_11_2_29,
  collectedFourData_11_2_30,
  collectedFourData_11_2_31,
  collectedFourData_11_2_32,
  collectedFourData_11_2_33,
  collectedFourData_11_2_34,
  collectedFourData_11_2_35,
  collectedFourData_11_2_36,
  collectedFourData_11_2_37,
  collectedFourData_11_2_38,
  collectedFourData_11_2_39,
  collectedFourData_11_2_40,
  collectedFourData_11_2_41,
  collectedFourData_11_2_42,
  collectedFourData_11_2_43,
  collectedFourData_11_2_44,
  collectedFourData_11_2_45,
  collectedFourData_11_2_46,
  collectedFourData_11_2_47,
  collectedFourData_11_2_48,
  collectedFourData_11_2_49,
  collectedFourData_11_2_50,
  collectedFourData_11_2_51,
  collectedFourData_11_2_52,
  collectedFourData_11_2_53
]

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1111. -/
namespace LaughlinFock

def collectedFourData_11_3 : List (List CollectedFourTerm) := [
  collectedFourData_11_3_0,
  collectedFourData_11_3_1,
  collectedFourData_11_3_2,
  collectedFourData_11_3_3,
  collectedFourData_11_3_4,
  collectedFourData_11_3_5,
  collectedFourData_11_3_6,
  collectedFourData_11_3_7,
  collectedFourData_11_3_8,
  collectedFourData_11_3_9,
  collectedFourData_11_3_10,
  collectedFourData_11_3_11,
  collectedFourData_11_3_12,
  collectedFourData_11_3_13,
  collectedFourData_11_3_14,
  collectedFourData_11_3_15,
  collectedFourData_11_3_16,
  collectedFourData_11_3_17,
  collectedFourData_11_3_18,
  collectedFourData_11_3_19,
  collectedFourData_11_3_20,
  collectedFourData_11_3_21,
  collectedFourData_11_3_22,
  collectedFourData_11_3_23,
  collectedFourData_11_3_24,
  collectedFourData_11_3_25,
  collectedFourData_11_3_26,
  collectedFourData_11_3_27,
  collectedFourData_11_3_28,
  collectedFourData_11_3_29,
  collectedFourData_11_3_30,
  collectedFourData_11_3_31,
  collectedFourData_11_3_32,
  collectedFourData_11_3_33,
  collectedFourData_11_3_34,
  collectedFourData_11_3_35,
  collectedFourData_11_3_36,
  collectedFourData_11_3_37,
  collectedFourData_11_3_38,
  collectedFourData_11_3_39,
  collectedFourData_11_3_40,
  collectedFourData_11_3_41,
  collectedFourData_11_3_42,
  collectedFourData_11_3_43,
  collectedFourData_11_3_44,
  collectedFourData_11_3_45,
  collectedFourData_11_3_46,
  collectedFourData_11_3_47,
  collectedFourData_11_3_48,
  collectedFourData_11_3_49,
  collectedFourData_11_3_50,
  collectedFourData_11_3_51,
  collectedFourData_11_3_52,
  collectedFourData_11_3_53,
  collectedFourData_11_3_54,
  collectedFourData_11_3_55
]

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1115. -/
namespace LaughlinFock

def collectedFourData_11_4 : List (List CollectedFourTerm) := [
  collectedFourData_11_4_0,
  collectedFourData_11_4_1,
  collectedFourData_11_4_2,
  collectedFourData_11_4_3,
  collectedFourData_11_4_4,
  collectedFourData_11_4_5,
  collectedFourData_11_4_6,
  collectedFourData_11_4_7,
  collectedFourData_11_4_8,
  collectedFourData_11_4_9,
  collectedFourData_11_4_10,
  collectedFourData_11_4_11,
  collectedFourData_11_4_12,
  collectedFourData_11_4_13,
  collectedFourData_11_4_14,
  collectedFourData_11_4_15,
  collectedFourData_11_4_16,
  collectedFourData_11_4_17,
  collectedFourData_11_4_18,
  collectedFourData_11_4_19,
  collectedFourData_11_4_20,
  collectedFourData_11_4_21,
  collectedFourData_11_4_22,
  collectedFourData_11_4_23,
  collectedFourData_11_4_24,
  collectedFourData_11_4_25,
  collectedFourData_11_4_26,
  collectedFourData_11_4_27,
  collectedFourData_11_4_28,
  collectedFourData_11_4_29,
  collectedFourData_11_4_30,
  collectedFourData_11_4_31,
  collectedFourData_11_4_32,
  collectedFourData_11_4_33,
  collectedFourData_11_4_34,
  collectedFourData_11_4_35,
  collectedFourData_11_4_36,
  collectedFourData_11_4_37,
  collectedFourData_11_4_38,
  collectedFourData_11_4_39,
  collectedFourData_11_4_40,
  collectedFourData_11_4_41,
  collectedFourData_11_4_42,
  collectedFourData_11_4_43,
  collectedFourData_11_4_44,
  collectedFourData_11_4_45,
  collectedFourData_11_4_46,
  collectedFourData_11_4_47,
  collectedFourData_11_4_48,
  collectedFourData_11_4_49,
  collectedFourData_11_4_50,
  collectedFourData_11_4_51,
  collectedFourData_11_4_52,
  collectedFourData_11_4_53,
  collectedFourData_11_4_54,
  collectedFourData_11_4_55
]

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1124
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1124. -/
namespace LaughlinFock

def collectedFourData_11 : Fin 8 → List (List CollectedFourTerm) :=
  ![collectedFourData_11_0, collectedFourData_11_1, collectedFourData_11_2, collectedFourData_11_3, collectedFourData_11_4, collectedFourData_11_5, collectedFourData_11_6, collectedFourData_11_7]

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1302
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1302. -/
namespace LaughlinFock

def collectedFourData_13_0 : List (List CollectedFourTerm) := [
  collectedFourData_13_0_0,
  collectedFourData_13_0_1,
  collectedFourData_13_0_2,
  collectedFourData_13_0_3,
  collectedFourData_13_0_4,
  collectedFourData_13_0_5,
  collectedFourData_13_0_6,
  collectedFourData_13_0_7,
  collectedFourData_13_0_8,
  collectedFourData_13_0_9,
  collectedFourData_13_0_10,
  collectedFourData_13_0_11,
  collectedFourData_13_0_12,
  collectedFourData_13_0_13,
  collectedFourData_13_0_14,
  collectedFourData_13_0_15,
  collectedFourData_13_0_16,
  collectedFourData_13_0_17,
  collectedFourData_13_0_18,
  collectedFourData_13_0_19,
  collectedFourData_13_0_20,
  collectedFourData_13_0_21,
  collectedFourData_13_0_22,
  collectedFourData_13_0_23,
  collectedFourData_13_0_24,
  collectedFourData_13_0_25,
  collectedFourData_13_0_26,
  collectedFourData_13_0_27,
  collectedFourData_13_0_28,
  collectedFourData_13_0_29,
  collectedFourData_13_0_30,
  collectedFourData_13_0_31,
  collectedFourData_13_0_32,
  collectedFourData_13_0_33,
  collectedFourData_13_0_34,
  collectedFourData_13_0_35,
  collectedFourData_13_0_36,
  collectedFourData_13_0_37,
  collectedFourData_13_0_38,
  collectedFourData_13_0_39,
  collectedFourData_13_0_40,
  collectedFourData_13_0_41,
  collectedFourData_13_0_42,
  collectedFourData_13_0_43
]

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1308
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1308. -/
namespace LaughlinFock

def collectedFourData_13_3 : List (List CollectedFourTerm) := [
  collectedFourData_13_3_0,
  collectedFourData_13_3_1,
  collectedFourData_13_3_2,
  collectedFourData_13_3_3,
  collectedFourData_13_3_4,
  collectedFourData_13_3_5,
  collectedFourData_13_3_6,
  collectedFourData_13_3_7,
  collectedFourData_13_3_8,
  collectedFourData_13_3_9,
  collectedFourData_13_3_10,
  collectedFourData_13_3_11,
  collectedFourData_13_3_12,
  collectedFourData_13_3_13,
  collectedFourData_13_3_14,
  collectedFourData_13_3_15,
  collectedFourData_13_3_16,
  collectedFourData_13_3_17,
  collectedFourData_13_3_18,
  collectedFourData_13_3_19,
  collectedFourData_13_3_20,
  collectedFourData_13_3_21,
  collectedFourData_13_3_22,
  collectedFourData_13_3_23,
  collectedFourData_13_3_24,
  collectedFourData_13_3_25,
  collectedFourData_13_3_26,
  collectedFourData_13_3_27,
  collectedFourData_13_3_28,
  collectedFourData_13_3_29,
  collectedFourData_13_3_30,
  collectedFourData_13_3_31,
  collectedFourData_13_3_32,
  collectedFourData_13_3_33,
  collectedFourData_13_3_34,
  collectedFourData_13_3_35,
  collectedFourData_13_3_36,
  collectedFourData_13_3_37,
  collectedFourData_13_3_38,
  collectedFourData_13_3_39,
  collectedFourData_13_3_40,
  collectedFourData_13_3_41,
  collectedFourData_13_3_42,
  collectedFourData_13_3_43,
  collectedFourData_13_3_44,
  collectedFourData_13_3_45,
  collectedFourData_13_3_46,
  collectedFourData_13_3_47,
  collectedFourData_13_3_48,
  collectedFourData_13_3_49,
  collectedFourData_13_3_50,
  collectedFourData_13_3_51,
  collectedFourData_13_3_52,
  collectedFourData_13_3_53,
  collectedFourData_13_3_54,
  collectedFourData_13_3_55
]

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1317
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1317. -/
namespace LaughlinFock

def collectedFourData_13 : Fin 8 → List (List CollectedFourTerm) :=
  ![collectedFourData_13_0, collectedFourData_13_1, collectedFourData_13_2, collectedFourData_13_3, collectedFourData_13_4, collectedFourData_13_5, collectedFourData_13_6, collectedFourData_13_7]

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1406
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1406. -/
namespace LaughlinFock

def collectedFourData_14_3 : List (List CollectedFourTerm) := [
  collectedFourData_14_3_0,
  collectedFourData_14_3_1,
  collectedFourData_14_3_2,
  collectedFourData_14_3_3,
  collectedFourData_14_3_4,
  collectedFourData_14_3_5,
  collectedFourData_14_3_6,
  collectedFourData_14_3_7,
  collectedFourData_14_3_8,
  collectedFourData_14_3_9,
  collectedFourData_14_3_10,
  collectedFourData_14_3_11,
  collectedFourData_14_3_12,
  collectedFourData_14_3_13,
  collectedFourData_14_3_14,
  collectedFourData_14_3_15,
  collectedFourData_14_3_16,
  collectedFourData_14_3_17,
  collectedFourData_14_3_18,
  collectedFourData_14_3_19,
  collectedFourData_14_3_20,
  collectedFourData_14_3_21,
  collectedFourData_14_3_22,
  collectedFourData_14_3_23,
  collectedFourData_14_3_24,
  collectedFourData_14_3_25,
  collectedFourData_14_3_26,
  collectedFourData_14_3_27,
  collectedFourData_14_3_28,
  collectedFourData_14_3_29,
  collectedFourData_14_3_30,
  collectedFourData_14_3_31,
  collectedFourData_14_3_32,
  collectedFourData_14_3_33,
  collectedFourData_14_3_34,
  collectedFourData_14_3_35,
  collectedFourData_14_3_36,
  collectedFourData_14_3_37,
  collectedFourData_14_3_38,
  collectedFourData_14_3_39,
  collectedFourData_14_3_40,
  collectedFourData_14_3_41,
  collectedFourData_14_3_42,
  collectedFourData_14_3_43,
  collectedFourData_14_3_44,
  collectedFourData_14_3_45,
  collectedFourData_14_3_46,
  collectedFourData_14_3_47,
  collectedFourData_14_3_48,
  collectedFourData_14_3_49,
  collectedFourData_14_3_50,
  collectedFourData_14_3_51,
  collectedFourData_14_3_52,
  collectedFourData_14_3_53,
  collectedFourData_14_3_54,
  collectedFourData_14_3_55
]

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1413
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1413. -/
namespace LaughlinFock

def collectedFourData_14 : Fin 8 → List (List CollectedFourTerm) :=
  ![collectedFourData_14_0, collectedFourData_14_1, collectedFourData_14_2, collectedFourData_14_3, collectedFourData_14_4, collectedFourData_14_5, collectedFourData_14_6, collectedFourData_14_7]

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1508
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1508. -/
namespace LaughlinFock

def collectedFourData_15 : List CollectedFourTerm := (((((((collectedFourData_15_0 ++ collectedFourData_15_1) ++ (collectedFourData_15_2 ++ (collectedFourData_15_3 ++ collectedFourData_15_4))) ++ ((collectedFourData_15_5 ++ collectedFourData_15_6) ++ (collectedFourData_15_7 ++ (collectedFourData_15_8 ++ collectedFourData_15_9)))) ++ (((collectedFourData_15_10 ++ collectedFourData_15_11) ++ (collectedFourData_15_12 ++ (collectedFourData_15_13 ++ collectedFourData_15_14))) ++ ((collectedFourData_15_15 ++ collectedFourData_15_16) ++ (collectedFourData_15_17 ++ (collectedFourData_15_18 ++ collectedFourData_15_19))))) ++ ((((collectedFourData_15_20 ++ collectedFourData_15_21) ++ (collectedFourData_15_22 ++ (collectedFourData_15_23 ++ collectedFourData_15_24))) ++ ((collectedFourData_15_25 ++ collectedFourData_15_26) ++ (collectedFourData_15_27 ++ (collectedFourData_15_28 ++ collectedFourData_15_29)))) ++ (((collectedFourData_15_30 ++ collectedFourData_15_31) ++ (collectedFourData_15_32 ++ (collectedFourData_15_33 ++ collectedFourData_15_34))) ++ ((collectedFourData_15_35 ++ (collectedFourData_15_36 ++ collectedFourData_15_37)) ++ (collectedFourData_15_38 ++ (collectedFourData_15_39 ++ collectedFourData_15_40)))))) ++ (((((collectedFourData_15_41 ++ collectedFourData_15_42) ++ (collectedFourData_15_43 ++ (collectedFourData_15_44 ++ collectedFourData_15_45))) ++ ((collectedFourData_15_46 ++ collectedFourData_15_47) ++ (collectedFourData_15_48 ++ (collectedFourData_15_49 ++ collectedFourData_15_50)))) ++ (((collectedFourData_15_51 ++ collectedFourData_15_52) ++ (collectedFourData_15_53 ++ (collectedFourData_15_54 ++ collectedFourData_15_55))) ++ ((collectedFourData_15_56 ++ (collectedFourData_15_57 ++ collectedFourData_15_58)) ++ (collectedFourData_15_59 ++ (collectedFourData_15_60 ++ collectedFourData_15_61))))) ++ ((((collectedFourData_15_62 ++ collectedFourData_15_63) ++ (collectedFourData_15_64 ++ (collectedFourData_15_65 ++ collectedFourData_15_66))) ++ ((collectedFourData_15_67 ++ collectedFourData_15_68) ++ (collectedFourData_15_69 ++ (collectedFourData_15_70 ++ collectedFourData_15_71)))) ++ (((collectedFourData_15_72 ++ collectedFourData_15_73) ++ (collectedFourData_15_74 ++ (collectedFourData_15_75 ++ collectedFourData_15_76))) ++ ((collectedFourData_15_77 ++ (collectedFourData_15_78 ++ collectedFourData_15_79)) ++ (collectedFourData_15_80 ++ (collectedFourData_15_81 ++ collectedFourData_15_82))))))) ++ ((((((collectedFourData_15_83 ++ collectedFourData_15_84) ++ (collectedFourData_15_85 ++ (collectedFourData_15_86 ++ collectedFourData_15_87))) ++ ((collectedFourData_15_88 ++ collectedFourData_15_89) ++ (collectedFourData_15_90 ++ (collectedFourData_15_91 ++ collectedFourData_15_92)))) ++ (((collectedFourData_15_93 ++ collectedFourData_15_94) ++ (collectedFourData_15_95 ++ (collectedFourData_15_96 ++ collectedFourData_15_97))) ++ ((collectedFourData_15_98 ++ collectedFourData_15_99) ++ (collectedFourData_15_100 ++ (collectedFourData_15_101 ++ collectedFourData_15_102))))) ++ ((((collectedFourData_15_103 ++ collectedFourData_15_104) ++ (collectedFourData_15_105 ++ (collectedFourData_15_106 ++ collectedFourData_15_107))) ++ ((collectedFourData_15_108 ++ collectedFourData_15_109) ++ (collectedFourData_15_110 ++ (collectedFourData_15_111 ++ collectedFourData_15_112)))) ++ (((collectedFourData_15_113 ++ collectedFourData_15_114) ++ (collectedFourData_15_115 ++ (collectedFourData_15_116 ++ collectedFourData_15_117))) ++ ((collectedFourData_15_118 ++ (collectedFourData_15_119 ++ collectedFourData_15_120)) ++ (collectedFourData_15_121 ++ (collectedFourData_15_122 ++ collectedFourData_15_123)))))) ++ (((((collectedFourData_15_124 ++ collectedFourData_15_125) ++ (collectedFourData_15_126 ++ (collectedFourData_15_127 ++ collectedFourData_15_128))) ++ ((collectedFourData_15_129 ++ collectedFourData_15_130) ++ (collectedFourData_15_131 ++ (collectedFourData_15_132 ++ collectedFourData_15_133)))) ++ (((collectedFourData_15_134 ++ collectedFourData_15_135) ++ (collectedFourData_15_136 ++ (collectedFourData_15_137 ++ collectedFourData_15_138))) ++ ((collectedFourData_15_139 ++ (collectedFourData_15_140 ++ collectedFourData_15_141)) ++ (collectedFourData_15_142 ++ (collectedFourData_15_143 ++ collectedFourData_15_144))))) ++ ((((collectedFourData_15_145 ++ collectedFourData_15_146) ++ (collectedFourData_15_147 ++ (collectedFourData_15_148 ++ collectedFourData_15_149))) ++ ((collectedFourData_15_150 ++ collectedFourData_15_151) ++ (collectedFourData_15_152 ++ (collectedFourData_15_153 ++ collectedFourData_15_154)))) ++ (((collectedFourData_15_155 ++ collectedFourData_15_156) ++ (collectedFourData_15_157 ++ (collectedFourData_15_158 ++ collectedFourData_15_159))) ++ ((collectedFourData_15_160 ++ (collectedFourData_15_161 ++ collectedFourData_15_162)) ++ (collectedFourData_15_163 ++ (collectedFourData_15_164 ++ collectedFourData_15_165))))))))

end LaughlinFock

end OAI
end


