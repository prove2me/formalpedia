-- Prove2me | Definitions.Def_OAIQ098E012
-- name    : OAIQ098E012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T04:52:44.315913+00:00
-- url     : https://prove2.me/theorems/69b4afd7-1b94-42e3-bd6e-eb904b3f6300
-- title:
--   Definitions bundle OAIQ098E012 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.expCut`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Entire`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Entire.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098E239`; the statements `OAI.SharpPlanar.expCut_decay_e` and `OAI.SharpPlanar.expCut_smooth_e`; the proofs of `OAI.SharpPlanar.expCut_decay_e` and `OAI.SharpPlanar.expCut_smooth_e`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Entire
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

namespace SharpPlanar

noncomputable def expCut (c x : ℝ) : ℝ :=
  Real.smoothTransition (x+1) * Real.exp (-c*x)

end SharpPlanar


open scoped SchwartzMap

end OAI
end


