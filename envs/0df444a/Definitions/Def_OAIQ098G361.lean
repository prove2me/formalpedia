-- Prove2me | Definitions.Def_OAIQ098G361
-- name    : OAIQ098G361
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-09T03:47:28.987404+00:00
-- url     : https://prove2.me/theorems/fe4f8b2f-ebba-4409-879c-adede111d496
-- title:
--   Definitions bundle OAIQ098G361 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.CachedData.trans16Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_TransformedPowers20`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers20.lean).
--
--   **Imports.** It imports the bundle `OAIQ098G302` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Bernstein16.N0_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_left.t3_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_left.t4_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_left.t7_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_right.t3_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_right.t4_contains_g`, `OAI.SharpPlanar.Bernstein16.N0_right.t7_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_left.t3_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_left.t4_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_left.t7_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_right.t2_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_right.t3_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_right.t4_contains_g`, `OAI.SharpPlanar.Bernstein16.N1_right.t7_contains_g`, `OAI.SharpPlanar.CachedData.cm1_16_1_1.contains_g`, `OAI.SharpPlanar.CachedData.cm3_16_0_1.contains_g`, `OAI.SharpPlanar.CachedData.cm3_16_1_1.contains_g`, `OAI.SharpPlanar.CachedData.cm4_16_1_1.contains_g`, `OAI.SharpPlanar.CachedData.hk16_1_13_contains_g`, `OAI.SharpPlanar.CachedData.hk16_1_3_contains_g`, `OAI.SharpPlanar.CachedData.hk16_1_8_contains_g`, `OAI.SharpPlanar.CachedData.hm16_0_1_10.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_0_1_11.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_0_1_12.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_0_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_0_1_7.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_1_1_10.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_1_1_11.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_1_1_12.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_1_1_2.realContains_g`, `OAI.SharpPlanar.CachedData.hm16_1_1_7.realContains_g`, `OAI.SharpPlanar.CachedData.kernel19_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel21_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel21_1_contains_g`, `OAI.SharpPlanar.CachedData.trans22_contains_g`, `OAI.SharpPlanar.Numerical.lentry11_0_contains_g`, `OAI.SharpPlanar.Numerical.lentry11_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry11_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry11_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry11_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry11_5_contains_g`, `OAI.SharpPlanar.Numerical.lentry5_0_contains_g`, `OAI.SharpPlanar.Numerical.lentry5_1_contains_g`, `OAI.SharpPlanar.Numerical.lentry5_2_contains_g`, `OAI.SharpPlanar.Numerical.lentry5_3_contains_g`, `OAI.SharpPlanar.Numerical.lentry5_4_contains_g`, `OAI.SharpPlanar.Numerical.lentry5_5_contains_g`, `OAI.SharpPlanar.Residual16.bound0_0_g`, `OAI.SharpPlanar.Residual16.bound0_1_g`, `OAI.SharpPlanar.Residual16.bound1_0_g`, `OAI.SharpPlanar.Residual16.bound1_1_g`, `OAI.SharpPlanar.Residual19.bound0_1_g` and `OAI.SharpPlanar.Residual19.bound1_1_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G302

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers20
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
noncomputable def trans16Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans15 j i k).mul (transStep j i k)
end SharpPlanar.CachedData

end OAI
end


