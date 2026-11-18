-- Prove2me | Definitions.Def_OAIQ368Chrom036
-- name    : OAIQ368Chrom036
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:28:53.380681+00:00
-- url     : https://prove2.me/theorems/39f18cc6-f1ec-40a9-8f1f-12e2d9f50c5d
-- title:
--   Definitions bundle OAIQ368Chrom036 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.fourInputSeries`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Shuffle_CellSeparation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/CellSeparation.lean).
--
--   **Imports.** It imports the bundles `OAIQ368Chrom027` and `OAIQ368Chrom033` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.ElementaryPositivity.RawShuffle.cellTransfer_normalized` and `OAI.ElementaryPositivity.RawShuffle.fourGrid_normalized_algebra`; the proofs of `OAI.ElementaryPositivity.RawShuffle.cellTransfer_normalized`, `OAI.ElementaryPositivity.RawShuffle.clearedSeparationB_cell`, `OAI.ElementaryPositivity.RawShuffle.clipped_grid_constant_head` and `OAI.ElementaryPositivity.RawShuffle.fourGrid_normalized_algebra`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom027
import Definitions.Def_OAIQ368Chrom033

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CellSeparation
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel
open SeparationInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] cancelTensorRing cancelTensorAlg cancelFourRing cancelFourAlg
attribute [local instance] cancelTensorSelf cancelTensorNonUnital cancelFourNonUnital cancelSeriesRing

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cellSepTensorSemiring
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cellSepTensorNonAssoc
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cellSepFourSemiring
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cellSepFourNonAssoc
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cellSepFourModule
noncomputable def fourInputSeries (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :=
  mapRing (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom (tensorSeparationSeries a d₁ d₂ f) *
    mapRing (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom (tensorSeparationSeries a e₁ e₂ g) *
    (mappedInverseKernel a e₁ d₂ (crossingColumnAlg d₁ e₁ d₂ e₂) *
      (mappedInverseKernel (fun i j=>a j i) e₁ d₂ (crossingColumnAlg d₁ e₁ d₂ e₂))⁻¹).val

end ElementaryPositivity.RawShuffle

end OAI
end


