-- Prove2me | Definitions.Def_OAIQ030L027
-- name    : OAIQ030L027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T02:35:11.856669+00:00
-- url     : https://prove2.me/theorems/d836556d-c3c2-4636-8cc5-e6f88e65c2a1
-- title:
--   Definitions bundle OAIQ030L027 of the split of OpenAI, Uniform Laughlin gap and stability under bounded scalar disorder (result family 269)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinGap.thm_main`, carved from OpenAI's openai/math development (OpenAI, *Uniform Laughlin gap and stability under bounded scalar disorder (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 16 definitions and 2 theorems. The definitions and types are `OAI.LaughlinGap.RealOccupation.Certificate16.fibers`, `OAI.LaughlinGap.RealOccupation.Certificate17.fibers`, `OAI.LaughlinGap.RealOccupation.Certificate17.representatives`, `OAI.LaughlinGap.RealOccupation.Certificate18.representatives`, `OAI.LaughlinGap.RealOccupation.Certificate8.fibers`, `OAI.LaughlinGap.RealOccupation.RationalRow.fourMatrixEval`, `OAI.LaughlinGap.RealOccupation.RationalRow.fourMatrixFast`, `OAI.LaughlinGap.RealOccupation.RationalRow.fourSumEval`, `OAI.LaughlinGap.RealOccupation.RationalRow.fourSumFast`, `OAI.LaughlinGap.RealOccupation.RationalRow.threeSumFast`, `OAI.LaughlinGap.RealOccupation.localTripleJ`, `OAI.LaughlinGap.RealOccupation.localTripleK`, `OAI.LaughlinGap.RealOccupation.localTripleP`, `OAI.LaughlinGap.RealOccupation.vCoefficient`, `OAI.LaughlinGap.RealOccupation.vFast`, `OAI.LaughlinGap.Spin.uFast`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`LaughlinGap_Certificate16`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Certificate16.lean), [`LaughlinGap_Certificate17`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Certificate17.lean), [`LaughlinGap_Certificate18`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Certificate18.lean), [`LaughlinGap_Certificate8`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Certificate8.lean), [`LaughlinGap_FastCoupling`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/FastCoupling.lean), [`LaughlinGap_FourTransfer`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/FourTransfer.lean), [`LaughlinGap_RationalCoupling`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/RationalCoupling.lean), [`LaughlinGap_RationalFourCoefficients`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/RationalFourCoefficients.lean), [`LaughlinGap_RationalFourComputable`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/RationalFourComputable.lean), [`LaughlinGap_RationalRowComputable`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/RationalRowComputable.lean).
--
--   **Imports.** It imports the bundles `OAIQ030L000`, `OAIQ030L005`, `OAIQ030L007`, `OAIQ030L010` and `OAIQ030L014` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ030L035`.
-- source:
--   OpenAI, Uniform Laughlin gap and stability under bounded scalar disorder (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ030L000
import Definitions.Def_OAIQ030L005
import Definitions.Def_OAIQ030L007
import Definitions.Def_OAIQ030L010
import Definitions.Def_OAIQ030L014

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Coupling. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators Polynomial
open Polynomial

@[simp] lemma rootFactorial_sq (n : ℕ) : rootFactorial n ^ 2 = (n.factorial : ℝ) :=
  Real.sq_sqrt (by positivity)
@[simp] lemma rootFactorial_zero : rootFactorial 0 = 1 := by simp [rootFactorial]

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalRowComputable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Row Computable. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

def RationalRow.threeSumFast (r : RationalRow) (z : ℕ) (i : Fin 9) : ℚ :=
  ∑ p : Fin 8, if h : p.val ≤ r.t.val+i.val ∧ r.t.val+i.val-p.val < 9 then
    r.alpha p ⟨r.t.val+i.val-p.val,h.2⟩ * uCoefficient 2 z (r.t.val+i.val) p.val else 0

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Transfer. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators InnerProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology

variable {ι : Type*} [Fintype ι]

def localTripleP {D : ℕ} (hD : D ≤ 23) (b : OrbitalTriple D) : Fin 24 :=
  ⟨b.val.1,by have := b.property; omega⟩
def localTripleJ {D : ℕ} (hD : D ≤ 23) (b : OrbitalTriple D) : Fin 25 :=
  ⟨b.val.2.1,by have := b.property; omega⟩
def localTripleK {D : ℕ} (hD : D ≤ 23) (b : OrbitalTriple D) : Fin 25 :=
  ⟨b.val.2.2,by have := b.property; omega⟩

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalFourCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Four Coefficients. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

def vCoefficient (D T r p j k : ℕ) : ℚ :=
  if D ≤ T ∧ r ≤ j+k ∧ p+j+k=T then
    uCoefficient 1 r (j+k) j * uCoefficient 1 (D-r) (T-r) p else 0

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalFourComputable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Four Computable. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

def RationalRow.fourSumFast (r : RationalRow) (D s : ℕ) (i k : Fin 9) : ℚ :=
  ∑ p : Fin 8, if h : p.val ≤ r.t.val+i.val ∧ r.t.val+i.val-p.val < 9 then
    r.alpha p ⟨r.t.val+i.val-p.val,h.2⟩ *
      vCoefficient D (r.t.val+i.val+k.val) s p.val (r.t.val+i.val-p.val) k.val *
        (2:ℚ)^((s+1)/2+p.val) else 0

def RationalRow.fourMatrixFast (r : RationalRow) (D u v : ℕ) : ℚ :=
  -(∑ i : Fin 9, ∑ k : Fin 9, fourRowFactor r.t.val D i.val k.val *
    r.fourSumFast D u i k * r.fourSumFast D v k i)

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FastCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fast Coupling. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

def uFast (c z T p : ℕ) : ℚ :=
  if z ≤ T then ∑ h ∈ Finset.range (p+1),
    (-1:ℚ)^(z-h) * (chooseFast z h) * (chooseFast (T-z) (p-h)) * (c:ℚ)^(p-h) else 0

end LaughlinGap.Spin

namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

def vFast (D T r p j k : ℕ) : ℚ :=
  if D ≤ T ∧ r ≤ j+k ∧ p+j+k=T then
    uFast 1 r (j+k) j * uFast 1 (D-r) (T-r) p else 0

def RationalRow.fourSumEval (r : RationalRow) (D s : ℕ) (i k : Fin 9) : ℚ :=
  ∑ p : Fin 8, if h : p.val ≤ r.t.val+i.val ∧ r.t.val+i.val-p.val < 9 then
    r.alpha p ⟨r.t.val+i.val-p.val,h.2⟩ *
      vFast D (r.t.val+i.val+k.val) s p.val (r.t.val+i.val-p.val) k.val *
        (2:ℚ)^((s+1)/2+p.val) else 0

def RationalRow.fourMatrixEval (r : RationalRow) (D u v : ℕ) : ℚ :=
  -(∑ i : Fin 9, ∑ k : Fin 9, fourRowFactor r.t.val D i.val k.val *
    r.fourSumEval D u i k * r.fourSumEval D v k i)

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

def fibers : Fin 27 → Finset (FourTerm 16) := ![{⟨⟨16,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨5,by decide⟩)⟩}]
end Certificate16
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate17. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate17

def fibers : Fin 34 → Finset (FourTerm 17) := ![{⟨⟨17,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨5,by decide⟩)⟩}]
def representatives : Fin 34 → FourTerm 17 := ![⟨⟨17,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨3,by decide⟩)⟩]
end Certificate17
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate18. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate18

def representatives : Fin 39 → FourTerm 18 := ![⟨⟨18,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨3,by decide⟩)⟩]
end Certificate18
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate8. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate8

def fibers : Fin 3 → Finset (FourTerm 8) := ![{⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}, {⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}]
end Certificate8
end LaughlinGap.RealOccupation

end

end OAI
end


