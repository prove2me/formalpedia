-- Prove2me | Definitions.Def_OAIQ098G1677
-- name    : OAIQ098G1677
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T19:30:17.04337+00:00
-- url     : https://prove2.me/theorems/589769e3-65ab-404b-9388-8dc29173c0da
-- title:
--   Definitions bundle OAIQ098G1677 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.expCutSchwartz`, `OAI.SharpPlanar.gaussianSchwartz`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Entire`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Entire.lean).
--
--   **Imports.** It imports the bundle `OAIQ098G012` of this split; the published statements `OAI.SharpPlanar.expCut_decay_g` and `OAI.SharpPlanar.expCut_smooth_g`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G1678`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G012
import Theorems.Thm_OAI_SharpPlanar_expCut_decay_g
import Theorems.Thm_OAI_SharpPlanar_expCut_smooth_g

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

noncomputable def expCutSchwartz (c : ℝ) (hc : 0 < c) : SchwartzMap ℝ ℝ where
  toFun := expCut c
  smooth' := expCut_smooth_g c
  decay' := expCut_decay_g c hc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


noncomputable def gaussianSchwartz (c : ℝ) (hc : 0 < c) : SchwartzMap E ℝ :=
  SchwartzMap.compCLM ℝ (g := fun x : E => ‖x‖^2) (Function.hasTemperateGrowth_norm_sq E)
    ⟨1, 1, fun x => by
      simp only [pow_one, one_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖)]
      nlinarith [sq_nonneg (‖x‖-1)]⟩ (expCutSchwartz c hc)

end SharpPlanar


open scoped SchwartzMap

end OAI
end


