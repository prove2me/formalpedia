-- Prove2me | Definitions.Def_OAIQ262T100
-- name    : OAIQ262T100
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:53:43.427666+00:00
-- url     : https://prove2.me/theorems/ea97ec33-6512-4805-9945-a9a99aae6f50
-- title:
--   Definitions bundle OAIQ262T100 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 15 declarations of OpenAI's Lean: 6 definitions and 9 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.exceptionalOffsetBox`, `OAI.AtomicTriangular.FiniteCertificate.exceptionalRowBox`, `OAI.AtomicTriangular.FiniteCertificate.exceptionalWeightBox`, `OAI.AtomicTriangular.FiniteCertificate.frozenTaylorRowBox`, `OAI.AtomicTriangular.FiniteCertificate.spectrum0_0`, `OAI.AtomicTriangular.FiniteCertificate.tr0_0_1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalInterval.lean), [`Triangular_Signs_ExceptionalSign0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign0.lean), [`Triangular_Signs_SineGrid0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid0.lean), [`Triangular_Taylor_TaylorRows00`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows00.lean), [`Triangular_Taylor_TaylorSpectrum`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorSpectrum.lean).
--
--   **Imports.** It imports the bundles `OAIQ262T005`, `OAIQ262T012`, `OAIQ262T015`, `OAIQ262T017`, `OAIQ262T020` and `OAIQ262T021` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T143`, `OAIQ262T146`, `OAIQ262T147`, `OAIQ262T148` and `OAIQ262T149`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T012
import Definitions.Def_OAIQ262T015
import Definitions.Def_OAIQ262T017
import Definitions.Def_OAIQ262T020
import Definitions.Def_OAIQ262T021

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def spectrum0_0 : Fin 31 → Fin 8 → CI := ![spectrum0_0_0,spectrum0_0_1,spectrum0_0_2,spectrum0_0_3,spectrum0_0_4,spectrum0_0_5,spectrum0_0_6,spectrum0_0_7,spectrum0_0_8,spectrum0_0_9,spectrum0_0_10,spectrum0_0_11,spectrum0_0_12,spectrum0_0_13,spectrum0_0_14,spectrum0_0_15,spectrum0_0_16,spectrum0_0_17,spectrum0_0_18,spectrum0_0_19,spectrum0_0_20,spectrum0_0_21,spectrum0_0_22,spectrum0_0_23,spectrum0_0_24,spectrum0_0_25,spectrum0_0_26,spectrum0_0_27,spectrum0_0_28,spectrum0_0_29,spectrum0_0_30]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorRows00
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
-- module Solutions.OAIQ262_TG.Triangular_Signs_ExceptionalInterval
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

def exceptionalOffsetBox (test : Fin 4) (l : ℕ) (r : Fin 8) : RI :=
  if r.val=1 then (if l=0 then QBox1.mul (if test.val=0 then RI.point 1 else (RI.point test.val).mul ZBox)
    else if l=1 ∧ test.val≠0 then QBox1 else RI.point 0) else RI.point 0

def exceptionalRowBox (test : Fin 4) (l : Fin 23) (r : Fin 8) : RI :=
  (exceptionalOffsetBox test l.val r).add (RI.sum (fun ep : Fin 2 => RI.sum (fun j : Fin 3 =>
    if h : j.val≤l.val ∧ l.val-j.val<21 then
      (exceptionalWeightBox test ep j).mul (frozenTaylorRowBox (if ep.val=0 then RI.point 0 else ZBox) ⟨l.val-j.val,h.2⟩ r) else RI.point 0)))
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_ExceptionalSign0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex0r0_calc (r : Fin 8) : exceptionalRowBox 0 0 r = ex0r0 r := by
  revert r
  decide +kernel
lemma ex0r10_calc (r : Fin 8) : exceptionalRowBox 0 10 r = ex0r10 r := by
  revert r
  decide +kernel
lemma ex0r11_calc (r : Fin 8) : exceptionalRowBox 0 11 r = ex0r11 r := by
  revert r
  decide +kernel
lemma ex0r12_calc (r : Fin 8) : exceptionalRowBox 0 12 r = ex0r12 r := by
  revert r
  decide +kernel
lemma ex0r13_calc (r : Fin 8) : exceptionalRowBox 0 13 r = ex0r13 r := by
  revert r
  decide +kernel
lemma ex0r14_calc (r : Fin 8) : exceptionalRowBox 0 14 r = ex0r14 r := by
  revert r
  decide +kernel
lemma ex0r15_calc (r : Fin 8) : exceptionalRowBox 0 15 r = ex0r15 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_SineGrid0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors06 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 6 k j) ∧ cellBarrier 6 < ∏ j : Fin 15,(cellFactor 6 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 6 k j) ∧ cellBarrier 6 < ∏ j : Fin 15,(cellFactor 6 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors07 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 7 k j) ∧ cellBarrier 7 < ∏ j : Fin 15,(cellFactor 7 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 7 k j) ∧ cellBarrier 7 < ∏ j : Fin 15,(cellFactor 7 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


