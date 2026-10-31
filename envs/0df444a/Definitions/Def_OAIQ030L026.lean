-- Prove2me | Definitions.Def_OAIQ030L026
-- name    : OAIQ030L026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T02:34:47.640121+00:00
-- url     : https://prove2.me/theorems/d93104a3-2a32-4aa7-9984-30d7da2e086f
-- title:
--   Definitions bundle OAIQ030L026 of the split of OpenAI, Uniform Laughlin gap and stability under bounded scalar disorder (result family 269)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinGap.thm_main`, carved from OpenAI's openai/math development (OpenAI, *Uniform Laughlin gap and stability under bounded scalar disorder (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 15 declarations of OpenAI's Lean: 13 definitions, 1 inductive type or structure and 1 instance. The definitions and types are `OAI.LaughlinGap.RealOccupation.Certificate11.representatives`, `OAI.LaughlinGap.RealOccupation.Certificate12.fibers`, `OAI.LaughlinGap.RealOccupation.Certificate12.representatives`, `OAI.LaughlinGap.RealOccupation.Certificate13.fibers`, `OAI.LaughlinGap.RealOccupation.Certificate13.representatives`, `OAI.LaughlinGap.RealOccupation.Certificate14.fibers`, `OAI.LaughlinGap.RealOccupation.Certificate14.representatives`, `OAI.LaughlinGap.RealOccupation.Certificate15.fibers`, `OAI.LaughlinGap.RealOccupation.Certificate15.representatives`, `OAI.LaughlinGap.RealOccupation.Certificate16.representatives`, `OAI.LaughlinGap.RealOccupation.Certificate6.fibers`, `OAI.LaughlinGap.RealOccupation.RowData`, `OAI.LaughlinGap.RealOccupation.fourCopyTarget`, `OAI.LaughlinGap.orbitalTripleEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`LaughlinGap_AuxiliaryComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/AuxiliaryComparison.lean), [`LaughlinGap_Basic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Basic.lean), [`LaughlinGap_Certificate11`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Certificate11.lean), [`LaughlinGap_Certificate12`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Certificate12.lean), [`LaughlinGap_Certificate13`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Certificate13.lean), [`LaughlinGap_Certificate14`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Certificate14.lean), [`LaughlinGap_Certificate15`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Certificate15.lean), [`LaughlinGap_Certificate16`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Certificate16.lean), [`LaughlinGap_Certificate6`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Certificate6.lean), [`LaughlinGap_FourComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/FourComparison.lean).
--
--   **Imports.** It imports the bundles `OAIQ030L000`, `OAIQ030L010` and `OAIQ030L011` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ030L035`.
-- source:
--   OpenAI, Uniform Laughlin gap and stability under bounded scalar disorder (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ030L000
import Definitions.Def_OAIQ030L010
import Definitions.Def_OAIQ030L011

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Basic. -/

noncomputable section


namespace LaughlinGap
export _root_.OAI.Laughlin (Configuration State Antisymmetric pairCoefficient pairAmplitude energy SpinorVariables bracket laughlinPolynomial monomialExponent laughlinVector distanceToLaughlinSq )
open scoped BigOperators

def orbitalTripleEquiv (D : ℕ) :
    (Σ n : Fin (D + 1), Fin ((n.val + 1) / 2)) ≃ OrbitalTriple D where
  toFun a := ⟨(D - a.1.val, a.2.val, a.1.val - a.2.val), by
    have hn := a.1.isLt
    have hj := a.2.isLt
    constructor <;> dsimp only <;> omega⟩
  invFun t := ⟨⟨t.val.2.1 + t.val.2.2, by have h := t.property; omega⟩,
    ⟨t.val.2.1, by have h := t.property; dsimp only; omega⟩⟩
  left_inv a := by
    have hn := a.1.isLt
    have hj := a.2.isLt
    have he : a.2.val + (a.1.val - a.2.val) = a.1.val := by omega
    apply Sigma.ext
    · exact Fin.ext he
    · exact (Fin.heq_ext_iff (congrArg (fun n => (n + 1) / 2) he)).mpr rfl
  right_inv t := by
    have h := t.property
    apply Subtype.ext
    apply Prod.ext
    · simp only
      omega
    · apply Prod.ext
      · rfl
      · simp only
        omega

noncomputable instance instFintypeOrbitalTriple (D : ℕ) : Fintype (OrbitalTriple D) :=
  Fintype.ofEquiv _ (orbitalTripleEquiv D)

end LaughlinGap

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_AuxiliaryComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Auxiliary Comparison. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

structure RowData where
  t : Fin 8
  lam : ℝ
  alpha : RowEntry t → ℝ

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Comparison. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology

noncomputable def fourCopyTarget (D : ℕ) : Matrix (FourCopy D) (FourCopy D) ℝ :=
  fun r s => if r.val.val=1 ∧ s.val.val=1 then 1 else 0

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate11. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate11

def representatives : Fin 9 → FourTerm 11 := ![⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩]
end Certificate11
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate12. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate12

def fibers : Fin 11 → Finset (FourTerm 12) := ![{⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}]
def representatives : Fin 11 → FourTerm 12 := ![⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩]
end Certificate12
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate13. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate13

def fibers : Fin 15 → Finset (FourTerm 13) := ![{⟨⟨13,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩}]
def representatives : Fin 15 → FourTerm 13 := ![⟨⟨13,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩]
end Certificate13
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate14. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate14

def fibers : Fin 18 → Finset (FourTerm 14) := ![{⟨⟨14,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩}]
def representatives : Fin 18 → FourTerm 14 := ![⟨⟨14,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩]
end Certificate14
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate15. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate15

def fibers : Fin 23 → Finset (FourTerm 15) := ![{⟨⟨15,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨5,by decide⟩)⟩}]
def representatives : Fin 23 → FourTerm 15 := ![⟨⟨15,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩]
end Certificate15
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate16. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate16

def representatives : Fin 27 → FourTerm 16 := ![⟨⟨16,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩]
end Certificate16
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate6. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate6

def fibers : Fin 1 → Finset (FourTerm 6) := ![{⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}]
end Certificate6
end LaughlinGap.RealOccupation

end

end OAI
end


