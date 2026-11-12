-- Prove2me | Definitions.Def_OAIQ250T077
-- name    : OAIQ250T077
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T13:57:01.593987+00:00
-- url     : https://prove2.me/theorems/471e7efa-a64b-4572-a6dc-7055067cf3ea
-- title:
--   Definitions bundle OAIQ250T077 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 7 definitions and 6 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.bs0_1_1`, `OAI.AtomicTriangular.FiniteCertificate.exceptionalWeightBox`, `OAI.AtomicTriangular.FiniteCertificate.frozenTaylorRowBox`, `OAI.AtomicTriangular.FiniteCertificate.taylorAmplitudeBox`, `OAI.AtomicTriangular.FiniteCertificate.taylorExpTable`, `OAI.AtomicTriangular.FiniteCertificate.taylorWaveBox`, `OAI.AtomicTriangular.FiniteCertificate.tr0_0_1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalInterval.lean), [`Triangular_Signs_ExceptionalSign2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign2.lean), [`Triangular_Signs_Signs01`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs01.lean), [`Triangular_Signs_SineGrid1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid1.lean), [`Triangular_Taylor_TaylorExp`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorExp.lean), [`Triangular_Taylor_TaylorRows00`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows00.lean), [`Triangular_Taylor_TaylorWave`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave.lean), [`Triangular_Taylor_TaylorWave000`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave000.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T004`, `OAIQ250T007`, `OAIQ250T010`, `OAIQ250T011`, `OAIQ250T012`, `OAIQ250T013`, `OAIQ250T014`, `OAIQ250T015`, `OAIQ250T025`, `OAIQ250T026`, `OAIQ250T027` and `OAIQ250T028` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T086`, `OAIQ250T087`, `OAIQ250T088`, `OAIQ250T089`, `OAIQ250T090`, `OAIQ250T091`, `OAIQ250T092`, `OAIQ250T093`, `OAIQ250T094`, `OAIQ250T095`, `OAIQ250T096`, `OAIQ250T097`, `OAIQ250T098`, `OAIQ250T152`, `OAIQ250T153`, `OAIQ250T154`, `OAIQ250T155`, `OAIQ250T156`, `OAIQ250T157`, `OAIQ250T158`, `OAIQ250T159`, `OAIQ250T160` and `OAIQ250T179`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T004
import Definitions.Def_OAIQ250T007
import Definitions.Def_OAIQ250T010
import Definitions.Def_OAIQ250T011
import Definitions.Def_OAIQ250T012
import Definitions.Def_OAIQ250T013
import Definitions.Def_OAIQ250T014
import Definitions.Def_OAIQ250T015
import Definitions.Def_OAIQ250T025
import Definitions.Def_OAIQ250T026
import Definitions.Def_OAIQ250T027
import Definitions.Def_OAIQ250T028

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorExp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def taylorExpTable : Fin 2 → Fin 2 → Fin 7 → Fin 31 → CI := ![![![taylorExp0_0_1,taylorExp0_0_3,taylorExp0_0_4,taylorExp0_0_7,taylorExp0_0_9,taylorExp0_0_12,taylorExp0_0_13],![taylorExp0_1_1,taylorExp0_1_3,taylorExp0_1_4,taylorExp0_1_7,taylorExp0_1_9,taylorExp0_1_12,taylorExp0_1_13]],![![taylorExp1_0_1,taylorExp1_0_3,taylorExp1_0_4,taylorExp1_0_7,taylorExp1_0_9,taylorExp1_0_12,taylorExp1_0_13],![taylorExp1_1_1,taylorExp1_1_3,taylorExp1_1_4,taylorExp1_1_7,taylorExp1_1_9,taylorExp1_1_12,taylorExp1_1_13]]]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def taylorAmplitudeBox (q br : Fin 2) (j : Fin 31) : CI :=
  if br.val=0 then CI.point 1 else lambdaTable q j

def taylorWaveBox (q br : Fin 2) (n : Fin 7) (l : Fin 21) (j : Fin 31) : CI :=
  (((taylorAmplitudeBox q br j).mul (taylorExpTable q br n j)).mul
    ((taylorPhaseTable q br j).pow (l.val+2))).divNat (l.val+2).factorial

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_0_0_calc (j : Fin 31) : taylorWaveBox 0 0 0 0 j = tw0_0_0_0 j := by
  revert j
  decide +kernel
lemma tw0_0_0_10_calc (j : Fin 31) : taylorWaveBox 0 0 0 10 j = tw0_0_0_10 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr0_0_1 : Fin 21 → Fin 8 → RI := ![tr0_0_1_0,tr0_0_1_1,tr0_0_1_2,tr0_0_1_3,tr0_0_1_4,tr0_0_1_5,tr0_0_1_6,tr0_0_1_7,tr0_0_1_8,tr0_0_1_9,tr0_0_1_10,tr0_0_1_11,tr0_0_1_12,tr0_0_1_13,tr0_0_1_14,tr0_0_1_15,tr0_0_1_16,tr0_0_1_17,tr0_0_1_18,tr0_0_1_19,tr0_0_1_20]
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

def frozenTaylorRowBox (z : RI) (l : Fin 21) (r : Fin 8) : RI :=
  (if r.val=0 then RI.point 0 else (tr0_0_1 l r).neg).sub
    (if r.val=1 then z.mul (tr0_0_1 l 0) else RI.point 0)

def exceptionalWeightBox (test : Fin 4) (endpt : Fin 2) (j : Fin 3) : RI :=
  if test.val=0 then (if endpt.val=0 ∧ j.val=1 then RI.point 1 else RI.point 0)
  else if test.val=1 then (if endpt.val=0 then
    (if j.val=1 then ((RI.point 4).mul ZBox).divNat 3 else if j.val=2 then (RI.point 2).divNat 3 else RI.point 0)
    else if j.val=2 then (RI.point 1).divNat 3 else RI.point 0)
  else if test.val=2 then (if endpt.val=0 then
    (if j.val=0 then (RI.point 2).mul (ZBox.pow 2) else if j.val=1 then ((RI.point 4).mul ZBox).divNat 3 else (RI.point 1).divNat 3)
    else (if j.val=1 then ((RI.point 4).mul ZBox).divNat 3 else if j.val=2 then (RI.point 2).divNat 3 else RI.point 0))
  else (if endpt.val=1 then (if j.val=0 then (RI.point 6).mul (ZBox.pow 2) else if j.val=1 then (RI.point 4).mul ZBox else RI.point 1) else RI.point 0)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_ExceptionalSign2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex2b0_calc (r : Fin 8) : bernsteinRowsBox 22 ex2r 0 r = ex2b0 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_Signs01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def bs0_1_1 : Fin 21 → Fin 8 → RI := ![bs0_1_1_0,bs0_1_1_1,bs0_1_1_2,bs0_1_1_3,bs0_1_1_4,bs0_1_1_5,bs0_1_1_6,bs0_1_1_7,bs0_1_1_8,bs0_1_1_9,bs0_1_1_10,bs0_1_1_11,bs0_1_1_12,bs0_1_1_13,bs0_1_1_14,bs0_1_1_15,bs0_1_1_16,bs0_1_1_17,bs0_1_1_18,bs0_1_1_19,bs0_1_1_20]
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
lemma cellGeometry13 (k : Fin 100) :
    0 ≤ cellMagnitude 13 k ∧ cellMagnitude 13 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 13 → 0 ≤ cellSeparation 13 k j ∧ cellSeparation 13 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 13 k ∧ cellMagnitude 13 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 13 → 0 ≤ cellSeparation 13 k j ∧ cellSeparation 13 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry14 (k : Fin 100) :
    0 ≤ cellMagnitude 14 k ∧ cellMagnitude 14 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 14 → 0 ≤ cellSeparation 14 k j ∧ cellSeparation 14 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 14 k ∧ cellMagnitude 14 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 14 → 0 ≤ cellSeparation 14 k j ∧ cellSeparation 14 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry15 (k : Fin 100) :
    0 ≤ cellMagnitude 15 k ∧ cellMagnitude 15 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 15 → 0 ≤ cellSeparation 15 k j ∧ cellSeparation 15 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 15 k ∧ cellMagnitude 15 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 15 → 0 ≤ cellSeparation 15 k j ∧ cellSeparation 15 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


