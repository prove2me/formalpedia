-- Prove2me | Definitions.Def_OAIQ250T076
-- name    : OAIQ250T076
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:20:17.477324+00:00
-- url     : https://prove2.me/theorems/1156fdf8-c12f-4308-a838-e4a871d1bf71
-- title:
--   Definitions bundle OAIQ250T076 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 6 definitions and 24 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.exceptionalOffsetBox`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_1`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_4`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_0`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_2`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalInterval.lean), [`Triangular_Signs_ExceptionalSign0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign0.lean), [`Triangular_Signs_SineGrid1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid1.lean), [`Triangular_Taylor_TaylorRowsBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRowsBase.lean), [`Triangular_Taylor_TaylorWave10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave10.lean), [`Triangular_Taylor_TaylorWave101`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave101.lean), [`Triangular_Taylor_TaylorWave104`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave104.lean), [`Triangular_Taylor_TaylorWave110`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave110.lean), [`Triangular_Taylor_TaylorWave112`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave112.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T007`, `OAIQ250T011`, `OAIQ250T012`, `OAIQ250T013`, `OAIQ250T020`, `OAIQ250T021`, `OAIQ250T022`, `OAIQ250T023` and `OAIQ250T024` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T086` and `OAIQ250T087`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T007
import Definitions.Def_OAIQ250T011
import Definitions.Def_OAIQ250T012
import Definitions.Def_OAIQ250T013
import Definitions.Def_OAIQ250T020
import Definitions.Def_OAIQ250T021
import Definitions.Def_OAIQ250T022
import Definitions.Def_OAIQ250T023
import Definitions.Def_OAIQ250T024

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw1_0_1 : Fin 21 → Fin 31 → CI := ![tw1_0_1_0,tw1_0_1_1,tw1_0_1_2,tw1_0_1_3,tw1_0_1_4,tw1_0_1_5,tw1_0_1_6,tw1_0_1_7,tw1_0_1_8,tw1_0_1_9,tw1_0_1_10,tw1_0_1_11,tw1_0_1_12,tw1_0_1_13,tw1_0_1_14,tw1_0_1_15,tw1_0_1_16,tw1_0_1_17,tw1_0_1_18,tw1_0_1_19,tw1_0_1_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw1_0_4 : Fin 21 → Fin 31 → CI := ![tw1_0_4_0,tw1_0_4_1,tw1_0_4_2,tw1_0_4_3,tw1_0_4_4,tw1_0_4_5,tw1_0_4_6,tw1_0_4_7,tw1_0_4_8,tw1_0_4_9,tw1_0_4_10,tw1_0_4_11,tw1_0_4_12,tw1_0_4_13,tw1_0_4_14,tw1_0_4_15,tw1_0_4_16,tw1_0_4_17,tw1_0_4_18,tw1_0_4_19,tw1_0_4_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw1_0 : Fin 7 → Fin 21 → Fin 31 → CI := ![tw1_0_0,tw1_0_1,tw1_0_2,tw1_0_3,tw1_0_4,tw1_0_5,tw1_0_6]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw1_1_0 : Fin 21 → Fin 31 → CI := ![tw1_1_0_0,tw1_1_0_1,tw1_1_0_2,tw1_1_0_3,tw1_1_0_4,tw1_1_0_5,tw1_1_0_6,tw1_1_0_7,tw1_1_0_8,tw1_1_0_9,tw1_1_0_10,tw1_1_0_11,tw1_1_0_12,tw1_1_0_13,tw1_1_0_14,tw1_1_0_15,tw1_1_0_16,tw1_1_0_17,tw1_1_0_18,tw1_1_0_19,tw1_1_0_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def tw1_1_2 : Fin 21 → Fin 31 → CI := ![tw1_1_2_0,tw1_1_2_1,tw1_1_2_2,tw1_1_2_3,tw1_1_2_4,tw1_1_2_5,tw1_1_2_6,tw1_1_2_7,tw1_1_2_8,tw1_1_2_9,tw1_1_2_10,tw1_1_2_11,tw1_1_2_12,tw1_1_2_13,tw1_1_2_14,tw1_1_2_15,tw1_1_2_16,tw1_1_2_17,tw1_1_2_18,tw1_1_2_19,tw1_1_2_20]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRowsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma nearDisplacementBox_mem (n : Fin 7) (y : Fin 2) :
    (nearDisplacementBox n y).Mem (nearDisplacement n y) := by
  exact RI.mem_divNat (RI.mem_point _) (by norm_num)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_ExceptionalInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def exceptionalOffsetBox (test : Fin 4) (l : ℕ) (r : Fin 8) : RI :=
  if r.val=1 then (if l=0 then QBox1.mul (if test.val=0 then RI.point 1 else (RI.point test.val).mul ZBox)
    else if l=1 ∧ test.val≠0 then QBox1 else RI.point 0) else RI.point 0
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_ExceptionalSign0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex0b1_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 1 r = ex0b1 r := by
  revert r
  decide +kernel
lemma ex0b2_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 2 r = ex0b2 r := by
  revert r
  decide +kernel
lemma ex0b3_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 3 r = ex0b3 r := by
  revert r
  decide +kernel
lemma ex0b4_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 4 r = ex0b4 r := by
  revert r
  decide +kernel
lemma ex0b5_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 5 r = ex0b5 r := by
  revert r
  decide +kernel
lemma ex0b6_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 6 r = ex0b6 r := by
  revert r
  decide +kernel
lemma ex0b7_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 7 r = ex0b7 r := by
  revert r
  decide +kernel
lemma ex0b8_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 8 r = ex0b8 r := by
  revert r
  decide +kernel
lemma ex0b9_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 9 r = ex0b9 r := by
  revert r
  decide +kernel
lemma ex0b12_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 12 r = ex0b12 r := by
  revert r
  decide +kernel
lemma ex0b13_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 13 r = ex0b13 r := by
  revert r
  decide +kernel
lemma ex0b14_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 14 r = ex0b14 r := by
  revert r
  decide +kernel
lemma ex0b15_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 15 r = ex0b15 r := by
  revert r
  decide +kernel
lemma ex0b16_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 16 r = ex0b16 r := by
  revert r
  decide +kernel
lemma ex0b17_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 17 r = ex0b17 r := by
  revert r
  decide +kernel
lemma ex0b18_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 18 r = ex0b18 r := by
  revert r
  decide +kernel
lemma ex0b19_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 19 r = ex0b19 r := by
  revert r
  decide +kernel
lemma ex0b20_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 20 r = ex0b20 r := by
  revert r
  decide +kernel
lemma ex0b21_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 21 r = ex0b21 r := by
  revert r
  decide +kernel
lemma ex0b22_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 22 r = ex0b22 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGrid1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry10 (k : Fin 100) :
    0 ≤ cellMagnitude 10 k ∧ cellMagnitude 10 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 10 → 0 ≤ cellSeparation 10 k j ∧ cellSeparation 10 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 10 k ∧ cellMagnitude 10 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 10 → 0 ≤ cellSeparation 10 k j ∧ cellSeparation 10 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry11 (k : Fin 100) :
    0 ≤ cellMagnitude 11 k ∧ cellMagnitude 11 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 11 → 0 ≤ cellSeparation 11 k j ∧ cellSeparation 11 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 11 k ∧ cellMagnitude 11 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 11 → 0 ≤ cellSeparation 11 k j ∧ cellSeparation 11 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry12 (k : Fin 100) :
    0 ≤ cellMagnitude 12 k ∧ cellMagnitude 12 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 12 → 0 ≤ cellSeparation 12 k j ∧ cellSeparation 12 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 12 k ∧ cellMagnitude 12 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 12 → 0 ≤ cellSeparation 12 k j ∧ cellSeparation 12 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


