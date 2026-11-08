-- Prove2me | Definitions.Def_OAIQ098G1607
-- name    : OAIQ098G1607
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:32:34.387224+00:00
-- url     : https://prove2.me/theorems/5e3c015b-50ec-48fd-9184-890a0f506f8a
-- title:
--   Definitions bundle OAIQ098G1607 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.trans32Expr`, `OAI.SharpPlanar.CachedData.trans34Expr`, `OAI.SharpPlanar.CachedData.trans37Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_TransformedPowers40`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers40.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G064` and `OAIQ098G1415` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Bernstein37.N0_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein37.N0_left.t3_contains_g`, `OAI.SharpPlanar.Bernstein37.N0_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein37.N0_right.t3_contains_g`, `OAI.SharpPlanar.Bernstein37.N1_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein37.N1_left.t3_contains_g`, `OAI.SharpPlanar.Bernstein37.N1_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein37.N1_right.t3_contains_g`, `OAI.SharpPlanar.CachedData.hk37_1_3_contains_g`, `OAI.SharpPlanar.CachedData.hm37_0_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm37_1_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.kernel33_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel39_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel40_0_contains_g`, `OAI.SharpPlanar.CachedData.trans36_contains_g`, `OAI.SharpPlanar.CachedData.trans43_contains_g`, `OAI.SharpPlanar.Residual33.bound0_1_g`, `OAI.SharpPlanar.Residual33.bound1_1_g`, `OAI.SharpPlanar.Residual37.bound0_0_g`, `OAI.SharpPlanar.Residual37.bound0_1_g`, `OAI.SharpPlanar.Residual37.bound1_0_g`, `OAI.SharpPlanar.Residual37.bound1_1_g`, `OAI.SharpPlanar.Residual39.bound0_1_g`, `OAI.SharpPlanar.Residual39.bound1_1_g`, `OAI.SharpPlanar.Residual40.bound0_1_g` and `OAI.SharpPlanar.Residual40.bound1_1_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G064
import Definitions.Def_OAIQ098G1415

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers40
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
noncomputable def trans32Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans31 j i k).mul (transStep j i k)
noncomputable def trans34Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans33 j i k).mul (transStep j i k)
noncomputable def trans37Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans36 j i k).mul (transStep j i k)
end SharpPlanar.CachedData

end OAI
end


