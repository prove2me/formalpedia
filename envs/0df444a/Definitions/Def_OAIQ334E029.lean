-- Prove2me | Definitions.Def_OAIQ334E029
-- name    : OAIQ334E029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T12:55:12.666525+00:00
-- url     : https://prove2.me/theorems/7cf52f57-0c53-4ba5-83d2-4ad094e574a1
-- title:
--   Definitions bundle OAIQ334E029 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Schwartz_GaussianPair`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Schwartz/GaussianPair.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularEnergy`; the bundles `OAIQ334E008` and `OAIQ334E028` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ334E032`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularEnergy
import Definitions.Def_OAIQ334E008
import Definitions.Def_OAIQ334E028

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_GaussianPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped FourierTransform SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular
open Construction

lemma gaussianSchwartz_apply (α : ℝ) (hα : 0<α) (x : Plane) :
    gaussianSchwartz α hα x=gaussian α x := by
  simp only [gaussianSchwartz,Analysis.gaussianSchwartz_apply,gaussian,neg_mul]
lemma gaussianSchwartz_coe (α : ℝ) (hα : 0<α) :
    (gaussianSchwartz α hα : Plane → ℝ)=gaussian α := funext (gaussianSchwartz_apply α hα)
end AtomicTriangular
end

end OAI
end


