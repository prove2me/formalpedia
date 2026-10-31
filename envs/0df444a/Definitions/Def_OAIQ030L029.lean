-- Prove2me | Definitions.Def_OAIQ030L029
-- name    : OAIQ030L029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T02:35:24.296897+00:00
-- url     : https://prove2.me/theorems/6aea34b1-05c9-4cec-ac8f-863a78682e87
-- title:
--   Definitions bundle OAIQ030L029 of the split of OpenAI, Uniform Laughlin gap and stability under bounded scalar disorder (result family 269)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinGap.thm_main`, carved from OpenAI's openai/math development (OpenAI, *Uniform Laughlin gap and stability under bounded scalar disorder (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 10 definitions and 1 inductive type or structure. The definitions and types are `OAI.LaughlinGap.RealOccupation.Certificate19.fibers`, `OAI.LaughlinGap.RealOccupation.Certificate19.representatives`, `OAI.LaughlinGap.RealOccupation.Certificate21.representatives`, `OAI.LaughlinGap.RealOccupation.Certificate5.fibers`, `OAI.LaughlinGap.RealOccupation.Certificate7.fibers`, `OAI.LaughlinGap.RealOccupation.Certificate7.representatives`, `OAI.LaughlinGap.RealOccupation.Certificate8.representatives`, `OAI.LaughlinGap.RealOccupation.Covariant`, `OAI.LaughlinGap.RealOccupation.fourWeightCoefficientStar`, `OAI.LaughlinGap.Spin.balancedCouplingCoefficient`, `OAI.LaughlinGap.Spin.fourBodyCoefficientStar`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`LaughlinGap_Certificate19`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Certificate19.lean), [`LaughlinGap_Certificate21`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Certificate21.lean), [`LaughlinGap_Certificate5`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Certificate5.lean), [`LaughlinGap_Certificate7`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Certificate7.lean), [`LaughlinGap_Certificate8`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/Certificate8.lean), [`LaughlinGap_CovariantLift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/CovariantLift.lean), [`LaughlinGap_FourComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/FourComparison.lean), [`LaughlinGap_FourSpin`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/FourSpin.lean).
--
--   **Imports.** It imports the bundles `OAIQ030L000`, `OAIQ030L004` and `OAIQ030L009` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ030L035`.
-- source:
--   OpenAI, Uniform Laughlin gap and stability under bounded scalar disorder (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ030L000
import Definitions.Def_OAIQ030L004
import Definitions.Def_OAIQ030L009

section
-- module Solutions.OAIQ030_LG.LaughlinGap_CovariantLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariant Lift. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

structure Covariant (L : Matrix κ κ ℝ) (D : Matrix ι ι ℝ)
    (B : ι → Matrix κ κ ℝ) : Prop where
  lower : ∀ i, commutator L (B i) = -∑ j, D i j • B j
  raise : ∀ i, commutator L.transpose (B i) = -∑ j, D j i • B j

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct
open Occupation Filter Topology

noncomputable def balancedCouplingCoefficient (z T p : ℕ) : ℝ :=
  if z ≤ T then monomialWeight T p *
    (couplingPolynomial (1/Real.sqrt 2) (1/Real.sqrt 2) z (T-z)).coeff p else 0

noncomputable def fourBodyCoefficientStar (D T r p j k : ℕ) : ℝ :=
  if r ≤ j+k ∧ p+j+k=T then
    Real.sqrt 2 * balancedCouplingCoefficient r (j+k) j *
      balancedCouplingCoefficient (D-r) (T-r) p
  else 0

end LaughlinGap.Spin

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

noncomputable def fourWeightCoefficientStar (D T r p j k : ℕ) : ℝ :=
  if D ≤ T then fourBodyCoefficientStar D T r p j k else 0

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate19. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate19

def fibers : Fin 47 → Finset (FourTerm 19) := ![{⟨⟨19,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨18,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨19,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨9,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨6,by decide⟩)⟩}]
def representatives : Fin 47 → FourTerm 19 := ![⟨⟨19,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨3,by decide⟩)⟩]
end Certificate19
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate21. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate21

def representatives : Fin 64 → FourTerm 21 := ![⟨⟨21,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨10,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨9,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨5,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨4,by decide⟩)⟩]
end Certificate21
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate5. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate5

def fibers : Fin 1 → Finset (FourTerm 5) := ![{⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}]
end Certificate5
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate7. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate7

def fibers : Fin 2 → Finset (FourTerm 7) := ![{⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}, {⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}]
def representatives : Fin 2 → FourTerm 7 := ![⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩]
end Certificate7
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

def representatives : Fin 3 → FourTerm 8 := ![⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩]
end Certificate8
end LaughlinGap.RealOccupation

end

end OAI
end


