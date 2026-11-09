-- Prove2me | Definitions.Def_OAIQ098G160
-- name    : OAIQ098G160
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-08T09:02:38.029177+00:00
-- url     : https://prove2.me/theorems/d5e512df-be0b-46a4-93c8-561d9f7b377c
-- title:
--   Definitions bundle OAIQ098G160 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.cm3_9_1_0.s3`, `OAI.SharpPlanar.Numerical.U9.umat`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_LMoments9`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/LMoments9.lean), [`PlanarPacking_Certificate_WUCert9`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert9.lean).
--
--   **Imports.** It imports the bundle `OAIQ098G154` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G162`; the statements `OAI.SharpPlanar.Numerical.U9.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U9.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U9.wuplus_column_g`; the proofs of `OAI.SharpPlanar.Numerical.U9.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U9.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U9.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U9.wuplus_column_g` and `OAI.SharpPlanar.Numerical.signedVU_norm_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G154

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LMoments9
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
namespace cm3_9_1_0
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
end cm3_9_1_0
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert9
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

namespace SharpPlanar.Numerical.U9
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U9

end OAI
end


