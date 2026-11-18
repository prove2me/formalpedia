-- Prove2me | Definitions.Def_OAIQ368Chrom037
-- name    : OAIQ368Chrom037
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:32:47.6392+00:00
-- url     : https://prove2.me/theorems/79ece468-83cc-4ecd-88d8-378ef47858d6
-- title:
--   Definitions bundle OAIQ368Chrom037 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.fourInputSeriesB`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Shuffle_TensorColumnSeriesFiltration`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/TensorColumnSeriesFiltration.lean).
--
--   **Imports.** It imports the bundles `OAIQ368Chrom027`, `OAIQ368Chrom028` and `OAIQ368Chrom033` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.ElementaryPositivity.RawShuffle.clearedSeparationB_cell`; the proofs of `OAI.ElementaryPositivity.RawShuffle.clearedSeparationB_cell` and `OAI.ElementaryPositivity.RawShuffle.unitalSeparationConstant_shuffle_leading_all`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom027
import Definitions.Def_OAIQ368Chrom028
import Definitions.Def_OAIQ368Chrom033

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorColumnSeriesFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.LinearDetection
open ElementaryPositivity.SlopeArithmetic
open HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] braidFourTensor braidFourTensorAlg braidFourRing braidFourAlg
attribute [local instance] braidFourTensorN braidFourTensorM braidFourN braidFourM

noncomputable def fourInputSeriesB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (hd : d₁=0 ∨ d₂=0 ∨ slope c η d₁=slope c η d₂)
    (he : e₁=0 ∨ e₂=0 ∨ slope c η e₁=slope c η e₂)
    (f : B a (slope c η) (d₁+d₂)) (g : B a (slope c η) (e₁+e₂)) :
    LaurentSeries ((B a (slope c η) d₁⊗[ℚ]B a (slope c η) e₁)⊗[ℚ]
      (B a (slope c η) d₂⊗[ℚ]B a (slope c η) e₂)) :=
  mapRing (crossingColumnBAlg a (slope c η) d₁ e₁ d₂ e₂).toRingHom
    (braidingRatioUnit a (slope c η) e₁ d₂).val *
  ElementaryPositivity.TensorColumns.seriesProduct
    (unitalSeparationSeries a c η hc hd f) (unitalSeparationSeries a c η hc he g)

end ElementaryPositivity.RawShuffle

end

end OAI
end


