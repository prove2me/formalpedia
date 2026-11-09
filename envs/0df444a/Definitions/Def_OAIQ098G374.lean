-- Prove2me | Definitions.Def_OAIQ098G374
-- name    : OAIQ098G374
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-08T08:58:04.004843+00:00
-- url     : https://prove2.me/theorems/2189bac0-34fa-4137-b75e-6fdf3c0def60
-- title:
--   Definitions bundle OAIQ098G374 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.Numerical.U25.umat`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_WUCert25`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert25.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G004` and `OAIQ098G311` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.SharpPlanar.Numerical.U25.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U25.wuplus_column_g`; the proofs of `OAI.SharpPlanar.Numerical.U25.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U25.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U25.wuplus_column_g` and `OAI.SharpPlanar.Numerical.signedVU_norm_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G004
import Definitions.Def_OAIQ098G311

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Numerical.U25
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U25

end OAI
end


