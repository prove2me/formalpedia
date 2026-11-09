-- Prove2me | Definitions.Def_OAIQ098G373
-- name    : OAIQ098G373
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-08T08:57:55.556024+00:00
-- url     : https://prove2.me/theorems/a48ee00c-1c21-44c1-890b-6a360d0f376e
-- title:
--   Definitions bundle OAIQ098G373 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.Numerical.U24.umat`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_WUCert24`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert24.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G004` and `OAIQ098G314` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.SharpPlanar.Numerical.U24.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry1_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry2_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U24.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U24.wuplus_column_g`; the proofs of `OAI.SharpPlanar.Numerical.U24.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry1_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry2_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U24.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U24.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U24.wuplus_column_g` and `OAI.SharpPlanar.Numerical.signedVU_norm_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G004
import Definitions.Def_OAIQ098G314

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert24
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

namespace SharpPlanar.Numerical.U24
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U24

end OAI
end


