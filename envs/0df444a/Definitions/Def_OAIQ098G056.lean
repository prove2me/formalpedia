-- Prove2me | Definitions.Def_OAIQ098G056
-- name    : OAIQ098G056
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:02:10.170737+00:00
-- url     : https://prove2.me/theorems/a48e0e7f-500b-449e-972d-2c298d6f32a9
-- title:
--   Definitions bundle OAIQ098G056 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.CachedData.column3_0Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns10.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G019` and `OAIQ098G053` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.CachedData.cm3_16_0_1.contains_g`, `OAI.SharpPlanar.CachedData.cm3_3_0_1.contains_g`, `OAI.SharpPlanar.CachedData.cm3_4_0_1.contains_g`, `OAI.SharpPlanar.CachedData.tableTerm3_contains_g`, `OAI.SharpPlanar.Numerical.dentry0_1_contains_g`, `OAI.SharpPlanar.Numerical.dentry1_1_contains_g`, `OAI.SharpPlanar.Numerical.dentry2_1_contains_g`, `OAI.SharpPlanar.Numerical.dentry3_1_contains_g`, `OAI.SharpPlanar.Numerical.dentry4_1_contains_g`, `OAI.SharpPlanar.Numerical.dentry5_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry0_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry10_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry11_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry1_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry2_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry3_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry4_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry5_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry6_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry7_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry8_1_contains_g` and `OAI.SharpPlanar.Numerical.lentry9_1_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G019
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
noncomputable def column3_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp3_0 j i k).mul (power3 j i k)
end SharpPlanar.CachedData

end OAI
end


