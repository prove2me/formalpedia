-- Prove2me | Definitions.Def_OAIQ098G1678
-- name    : OAIQ098G1678
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T20:50:25.835838+00:00
-- url     : https://prove2.me/theorems/9ec53ac0-129b-42f2-a5ee-d90e1eb148c4
-- title:
--   Definitions bundle OAIQ098G1678 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 definitions. The definitions and types are `OAI.SharpPlanar.kSchwartz`, `OAI.SharpPlanar.pairLeft`, `OAI.SharpPlanar.pairRight`, `OAI.SharpPlanar.qComplexSchwartz`, `OAI.SharpPlanar.qSchwartz`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Entire`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Entire.lean), [`PlanarPacking_ExactPair`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/ExactPair.lean).
--
--   **Imports.** It imports the published bundle `Def_PlanarPacking`; the bundles `OAIQ098G1644` and `OAIQ098G1677` of this split; the published statements `OAI.SharpPlanar.b_pos_g` and `OAI.SharpPlanar.h_pos_g`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G1679`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_PlanarPacking
import Definitions.Def_OAIQ098G1644
import Definitions.Def_OAIQ098G1677
import Theorems.Thm_OAI_SharpPlanar_b_pos_g
import Theorems.Thm_OAI_SharpPlanar_h_pos_g

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

noncomputable def qSchwartz (p : CardinalData) : SchwartzMap Plane ℝ :=
  SchwartzMap.smulLeftCLM ℝ (fun x : Plane => cardinal p (b*‖x‖^2))
    (gaussianSchwartz (Real.pi*h*b) (mul_pos (mul_pos Real.pi_pos h_pos_g) b_pos_g))

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_ExactPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped FourierTransform
noncomputable def qComplexSchwartz (p : CardinalData) : SchwartzMap Plane ℂ :=
  SchwartzMap.postcompCLM Complex.ofRealCLM (qSchwartz p)
noncomputable def kSchwartz (p : CardinalData) : SchwartzMap Plane ℝ :=
  SchwartzMap.postcompCLM Complex.reCLM (𝓕 (qComplexSchwartz p))
noncomputable def pairLeft (p q : CardinalData) : SchwartzMap Plane ℝ := qSchwartz p+kSchwartz q
noncomputable def pairRight (p q : CardinalData) : SchwartzMap Plane ℝ := qSchwartz q+kSchwartz p
end SharpPlanar

end OAI
end


