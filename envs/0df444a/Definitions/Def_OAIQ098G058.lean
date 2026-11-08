-- Prove2me | Definitions.Def_OAIQ098G058
-- name    : OAIQ098G058
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:03:51.890274+00:00
-- url     : https://prove2.me/theorems/e0a397a7-2f98-4fd0-9899-070c17205a5b
-- title:
--   Definitions bundle OAIQ098G058 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.column4_0Expr`, `OAI.SharpPlanar.CachedData.column4_1Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns10.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G021` and `OAIQ098G053` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.SharpPlanar.CachedData.column4_0_eq_g`; the proofs of `OAI.SharpPlanar.CachedData.cm4_16_1_1.contains_g`, `OAI.SharpPlanar.CachedData.cm4_4_0_0.contains_g`, `OAI.SharpPlanar.CachedData.cm4_4_1_1.contains_g`, `OAI.SharpPlanar.CachedData.column4_0_eq_g`, `OAI.SharpPlanar.CachedData.tableTerm4_contains_g`, `OAI.SharpPlanar.Numerical.Lmat_column_g`, `OAI.SharpPlanar.Numerical.defectminus_column_g`, `OAI.SharpPlanar.Numerical.defectplus_column_g`, `OAI.SharpPlanar.Numerical.dentry0_5_contains_g`, `OAI.SharpPlanar.Numerical.dentry1_5_contains_g`, `OAI.SharpPlanar.Numerical.dentry2_2_contains_g`, `OAI.SharpPlanar.Numerical.dentry2_5_contains_g`, `OAI.SharpPlanar.Numerical.dentry3_5_contains_g`, `OAI.SharpPlanar.Numerical.dentry4_5_contains_g`, `OAI.SharpPlanar.Numerical.dentry5_2_contains_g`, `OAI.SharpPlanar.Numerical.dentry5_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry0_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry10_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry10_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry11_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry11_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry1_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry1_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry2_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry2_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry3_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry4_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry4_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry5_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry5_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry6_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry7_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry7_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry8_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry8_5_contains_g` and `OAI.SharpPlanar.Numerical.lentry9_5_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G021
import Definitions.Def_OAIQ098G053

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns10
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
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
noncomputable def column4_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_0 j i k).mul (power4 j i k)
noncomputable def column4_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_1 j i k).mul (power4 j i k)
end SharpPlanar.CachedData

end OAI
end


