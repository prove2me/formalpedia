-- Prove2me | Definitions.Def_OAIQ334E022
-- name    : OAIQ334E022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T13:00:09.108493+00:00
-- url     : https://prove2.me/theorems/a11d53d2-963e-414f-aae5-94eaeef69347
-- title:
--   Definitions bundle OAIQ334E022 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 8 definitions. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.exceptionalOffsetBox`, `OAI.AtomicTriangular.FiniteCertificate.exceptionalWeightBox`, `OAI.AtomicTriangular.FiniteCertificate.nearDisplacementBox`, `OAI.AtomicTriangular.FiniteCertificate.ordinaryOffsetBox`, `OAI.AtomicTriangular.FiniteCertificate.ordinarySignRowBox`, `OAI.AtomicTriangular.FiniteCertificate.rhsMinusBox`, `OAI.AtomicTriangular.FiniteCertificate.rhsPlusBox`, `OAI.AtomicTriangular.FiniteCertificate.spectrumBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_ParamInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamInterval.lean), [`Triangular_Signs_ExceptionalInterval`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalInterval.lean), [`Triangular_Signs_SignBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SignBase.lean), [`Triangular_Taylor_TaylorRowsBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRowsBase.lean), [`Triangular_Taylor_TaylorSpectrum`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorSpectrum.lean).
--
--   **Imports.** It imports the bundle `OAIQ334E011` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ334E023`; the statement `OAI.AtomicTriangular.FiniteCertificate.spectrumBox_mem_eu`; the proofs of `OAI.AtomicTriangular.Construction.finiteApprox_norm_eu`, `OAI.AtomicTriangular.Construction.near_negative_polynomial_eu`, `OAI.AtomicTriangular.Construction.near_positive_polynomial_eu`, `OAI.AtomicTriangular.FiniteCertificate.UplusTable_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_0_2_0_eu`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_0_2_1_eu`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_0_4_0_eu`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_0_4_1_eu`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_0_5_0_eu`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_0_5_1_eu`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_0_6_0_eu`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_0_6_1_eu`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_1_0_eu`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_1_1_eu`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_2_0_eu`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_4_0_eu`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_4_1_eu`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_5_0_eu`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_5_1_eu`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_6_0_eu`, `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_6_1_eu`, `OAI.AtomicTriangular.FiniteCertificate.spectrumBox_mem_eu` and `OAI.AtomicTriangular.FiniteCertificate.spectrumTable_mem_eu`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ334E011

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_ParamInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix

def rhsPlusBox (i : Fin 20) (j : Fin 8) : RI :=
  (YfBox i j).add (matrixMul R0Box (fun k j => (gammaBox 1 k j).add (gammaBox 0 k j)) i j)
def rhsMinusBox (i : Fin 20) (j : Fin 8) : RI :=
  (YfBox i j).add (matrixMul R0Box (fun k j => (gammaBox 1 k j).sub (gammaBox 0 k j)) i j)

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex

def spectrumBox (side q : Fin 2) (j : Fin 31) (r : Fin 8) : CI :=
  if q.val=0 then (coeffBox15 j).mul (CI.ofReal (ATable side 22 r))
  else CI.sum (fun col : Fin 22 => (columnTable ⟨col.val,by omega⟩ j).mul (CI.ofReal (ATable side ⟨col.val,by omega⟩ r)))
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorRowsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def nearDisplacementBox (n : Fin 7) (y : Fin 2) : RI := (RI.point (nearDisplacementNum n y)).divNat 2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_ExceptionalInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

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
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_SignBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def ordinaryOffsetBox (n : Fin 7) (r : Fin 8) : RI :=
  if n.val=0 ∧ r.val=1 then QBox1.mul ((RI.point 2).mul ZBox).invPos
  else if n.val=1 ∧ r.val=3 then ((RI.point 4).divNat 5).mul QBox1 else RI.point 0

def ordinarySignRowBox (side : Fin 2) (n : Fin 7) (a : Fin 21 → Fin 8 → RI)
    (l : Fin 21) (r : Fin 8) : RI :=
  if side.val=0 then ((if l.val=0 then ordinaryOffsetBox n r else RI.point 0).sub (a l r)) else a l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end


