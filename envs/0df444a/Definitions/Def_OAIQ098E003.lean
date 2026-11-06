-- Prove2me | Definitions.Def_OAIQ098E003
-- name    : OAIQ098E003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-05T20:48:52.108974+00:00
-- url     : https://prove2.me/theorems/4330628d-d19e-4a5e-9652-ce88c947b046
-- title:
--   Definitions bundle OAIQ098E003 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.Slinear`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Cardinal`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean).
--
--   **Imports.** It imports the bundle `OAIQ098E001` of this split; the published statements `OAI.SharpPlanar.Scoords_add_e`, `OAI.SharpPlanar.Scoords_mem_e` and `OAI.SharpPlanar.Scoords_smul_e`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098E004`; the statement `OAI.SharpPlanar.Slinear_bound_e`; the proof of `OAI.SharpPlanar.Slinear_bound_e`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098E001
import Theorems.Thm_OAI_SharpPlanar_Scoords_add_e
import Theorems.Thm_OAI_SharpPlanar_Scoords_mem_e
import Theorems.Thm_OAI_SharpPlanar_Scoords_smul_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar

noncomputable def Slinear : X →ₗ[ℝ] X where
  toFun x := ⟨Scoords x, Scoords_mem_e x⟩
  map_add' x y := lp.ext (funext fun ni => Scoords_add_e x y ni)
  map_smul' r x := lp.ext (funext fun ni => Scoords_smul_e r x ni)

end SharpPlanar

end OAI
end


