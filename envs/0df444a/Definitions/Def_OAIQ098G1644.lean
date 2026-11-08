-- Prove2me | Definitions.Def_OAIQ098G1644
-- name    : OAIQ098G1644
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:36:01.007195+00:00
-- url     : https://prove2.me/theorems/4b9379e4-9243-48b5-8da7-b13dc34f03b3
-- title:
--   Definitions bundle OAIQ098G1644 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.cardinal`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Entire`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Entire.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G001` and `OAIQ098G1643` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1652` and `OAIQ098G1678`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G001
import Definitions.Def_OAIQ098G1643

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Entire
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

/-!
# Gaussian cardinal interpolation

The folded spectral representation gives the cardinal values and derivatives.
Gaussian damping then extends the radial cardinal functions to Schwartz functions.
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory



open MeasureTheory
open scoped ComplexConjugate



open Set Filter MeasureTheory
open scoped Topology FourierTransform ContDiff


open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap


open scoped SchwartzMap

namespace SharpPlanar


noncomputable def cardinal (p : CardinalData) (s : ℝ) : ℝ :=
  ((spectral (Measure.dirac 0) (fun _ => (p.C : ℂ) * Pcoeff 0) s) +
    (∑ j ∈ Finset.Icc (1 : ℕ) 6,
      spectral (Measure.dirac ((j : ℝ)/6)) (fun _ => 2*(p.C : ℂ)*Pcoeff j) s) +
    (∑ j ∈ Finset.range 6,
      spectral (volume.restrict (Set.Icc ((j : ℝ)/6) (((j : ℝ)+1)/6)))
        (density p j) s)).re

end SharpPlanar

end OAI
end


