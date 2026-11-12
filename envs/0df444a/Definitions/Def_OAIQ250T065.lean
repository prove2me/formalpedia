-- Prove2me | Definitions.Def_OAIQ250T065
-- name    : OAIQ250T065
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:20:49.698537+00:00
-- url     : https://prove2.me/theorems/7eb2c8a5-3421-49f8-8cfe-484b8abb3c80
-- title:
--   Definitions bundle OAIQ250T065 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 4 definitions and 7 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.tw0_0_2`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_5`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_3`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_6`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_RemainderSums0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums0.lean), [`Triangular_Signs_SineBarrierBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineBarrierBase.lean), [`Triangular_Signs_SineGrid2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid2.lean), [`Triangular_Taylor_TaylorWave002`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave002.lean), [`Triangular_Taylor_TaylorWave005`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave005.lean), [`Triangular_Taylor_TaylorWave013`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave013.lean), [`Triangular_Taylor_TaylorWave016`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave016.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T003`, `OAIQ250T011`, `OAIQ250T012`, `OAIQ250T015`, `OAIQ250T016`, `OAIQ250T017`, `OAIQ250T018`, `OAIQ250T019` and `OAIQ250T020` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T086` and `OAIQ250T087`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T003
import Definitions.Def_OAIQ250T011
import Definitions.Def_OAIQ250T012
import Definitions.Def_OAIQ250T015
import Definitions.Def_OAIQ250T016
import Definitions.Def_OAIQ250T017
import Definitions.Def_OAIQ250T018
import Definitions.Def_OAIQ250T019
import Definitions.Def_OAIQ250T020

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave002
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw0_0_2 : Fin 21 → Fin 31 → CI := ![tw0_0_2_0,tw0_0_2_1,tw0_0_2_2,tw0_0_2_3,tw0_0_2_4,tw0_0_2_5,tw0_0_2_6,tw0_0_2_7,tw0_0_2_8,tw0_0_2_9,tw0_0_2_10,tw0_0_2_11,tw0_0_2_12,tw0_0_2_13,tw0_0_2_14,tw0_0_2_15,tw0_0_2_16,tw0_0_2_17,tw0_0_2_18,tw0_0_2_19,tw0_0_2_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave005
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw0_0_5 : Fin 21 → Fin 31 → CI := ![tw0_0_5_0,tw0_0_5_1,tw0_0_5_2,tw0_0_5_3,tw0_0_5_4,tw0_0_5_5,tw0_0_5_6,tw0_0_5_7,tw0_0_5_8,tw0_0_5_9,tw0_0_5_10,tw0_0_5_11,tw0_0_5_12,tw0_0_5_13,tw0_0_5_14,tw0_0_5_15,tw0_0_5_16,tw0_0_5_17,tw0_0_5_18,tw0_0_5_19,tw0_0_5_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave013
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw0_1_3 : Fin 21 → Fin 31 → CI := ![tw0_1_3_0,tw0_1_3_1,tw0_1_3_2,tw0_1_3_3,tw0_1_3_4,tw0_1_3_5,tw0_1_3_6,tw0_1_3_7,tw0_1_3_8,tw0_1_3_9,tw0_1_3_10,tw0_1_3_11,tw0_1_3_12,tw0_1_3_13,tw0_1_3_14,tw0_1_3_15,tw0_1_3_16,tw0_1_3_17,tw0_1_3_18,tw0_1_3_19,tw0_1_3_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave016
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw0_1_6 : Fin 21 → Fin 31 → CI := ![tw0_1_6_0,tw0_1_6_1,tw0_1_6_2,tw0_1_6_3,tw0_1_6_4,tw0_1_6_5,tw0_1_6_6,tw0_1_6_7,tw0_1_6_8,tw0_1_6_9,tw0_1_6_10,tw0_1_6_11,tw0_1_6_12,tw0_1_6_13,tw0_1_6_14,tw0_1_6_15,tw0_1_6_16,tw0_1_6_17,tw0_1_6_18,tw0_1_6_19,tw0_1_6_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderSums0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderColumns0_0_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData0_10 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns0_0 c := by
  revert c
  decide +kernel
lemma remainderColumns0_1_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData0_11 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns0_1 c := by
  revert c
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineBarrierBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset Set Filter
namespace AtomicTriangular.Construction

lemma sine_vanishing_lower {v : ℚ} {u : ℝ} (hv : 0≤v) (hv3 : v≤3) (hu : |u|≤v) :
    (vanishingLower v:ℝ)*|u|≤2*|Real.sin (Real.pi*u/36)| := by
  have hv0 : (0:ℝ)≤v := by exact_mod_cast hv
  have hv3' : (v:ℝ)≤3 := by exact_mod_cast hv3
  have hp0 : (0:ℝ)≤piHigh := by norm_num [piHigh]
  have hx : 0≤Real.pi*|u|/36 := by positivity
  have hl : (piLow:ℝ)/36*|u|≤Real.pi*|u|/36 := by nlinarith [sine_pi_bounds.1,abs_nonneg u]
  have hq : (Real.pi/36)^3≤((piHigh:ℝ)/36)^3 := pow_le_pow_left₀ (by positivity) (by linarith [sine_pi_bounds.2]) 3
  have hu2 : |u|^2≤(v:ℝ)^2 := (sq_le_sq₀ (abs_nonneg u) hv0).mpr hu
  have hc : (Real.pi*|u|/36)^3≤((piHigh:ℝ)/36)^3*(v:ℝ)^2*|u| := by
    have h1 := mul_le_mul_of_nonneg_right hq (pow_nonneg (abs_nonneg u) 3)
    have h2 := mul_le_mul_of_nonneg_left hu2 (mul_nonneg (pow_nonneg (by positivity : 0≤(piHigh:ℝ)/36) 3) (abs_nonneg u))
    nlinarith
  have hs := Real.sin_ge_sub_cube hx
  have he : |Real.sin (Real.pi*u/36)|=Real.sin (Real.pi*|u|/36) := by
    have hb : |Real.pi*u/36|≤Real.pi := by
      rw [abs_div,abs_mul,abs_of_pos Real.pi_pos,abs_of_pos (by norm_num : (0:ℝ)<36)]
      nlinarith [Real.pi_pos]
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hb,abs_div,abs_mul,abs_of_pos Real.pi_pos,abs_of_pos (by norm_num : (0:ℝ)<36)]
  rw [he]
  unfold vanishingLower
  push_cast
  linarith
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGrid2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors26 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 26 k j) ∧ cellBarrier 26 < ∏ j : Fin 15,(cellFactor 26 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 26 k j) ∧ cellBarrier 26 < ∏ j : Fin 15,(cellFactor 26 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors27 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 27 k j) ∧ cellBarrier 27 < ∏ j : Fin 15,(cellFactor 27 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 27 k j) ∧ cellBarrier 27 < ∏ j : Fin 15,(cellFactor 27 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors28 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 28 k j) ∧ cellBarrier 28 < ∏ j : Fin 15,(cellFactor 28 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 28 k j) ∧ cellBarrier 28 < ∏ j : Fin 15,(cellFactor 28 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors29 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 29 k j) ∧ cellBarrier 29 < ∏ j : Fin 15,(cellFactor 29 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 29 k j) ∧ cellBarrier 29 < ∏ j : Fin 15,(cellFactor 29 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


