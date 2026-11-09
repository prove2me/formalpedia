-- Prove2me | Definitions.Def_OAIQ098G370
-- name    : OAIQ098G370
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-08T08:56:25.655194+00:00
-- url     : https://prove2.me/theorems/bb63356d-c804-415c-8c1b-6a32fd2ee610
-- title:
--   Definitions bundle OAIQ098G370 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.Numerical.U13.umat`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_WUCert13`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert13.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G004` and `OAIQ098G330` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.SharpPlanar.Numerical.U13.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U13.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U13.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U13.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U13.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U13.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U13.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U13.wuplus_column_g`; the proofs of `OAI.SharpPlanar.Numerical.U13.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U13.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U13.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U13.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U13.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U13.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U13.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U13.wuplus_column_g` and `OAI.SharpPlanar.Numerical.signedVU_norm_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G004
import Definitions.Def_OAIQ098G330

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert13
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

namespace SharpPlanar.Numerical.U13
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U13

end OAI
end


