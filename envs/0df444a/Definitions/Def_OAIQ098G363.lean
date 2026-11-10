-- Prove2me | Definitions.Def_OAIQ098G363
-- name    : OAIQ098G363
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-09T19:21:02.001244+00:00
-- url     : https://prove2.me/theorems/0d160083-1911-4a4a-9bfa-665f889d8124
-- title:
--   Definitions bundle OAIQ098G363 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.trans8`, `OAI.SharpPlanar.CachedData.trans8_r3`, `OAI.SharpPlanar.CachedData.trans9Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_TransformedPowers10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers10.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G359` and `OAIQ098G362` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.SharpPlanar.CachedData.trans8_contains_g` and `OAI.SharpPlanar.CachedData.trans9_eq_g`; the proofs of `OAI.SharpPlanar.Bernstein9.N0_left.t12_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_left.t13_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_left.t2_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_right.t3_contains_g`, `OAI.SharpPlanar.Bernstein9.N0_right.t8_contains_g`, `OAI.SharpPlanar.CachedData.hk9_1_5_contains_g`, `OAI.SharpPlanar.CachedData.kernel9_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel9_1_contains_g`, `OAI.SharpPlanar.CachedData.trans10_contains_g`, `OAI.SharpPlanar.CachedData.trans8_contains_g`, `OAI.SharpPlanar.CachedData.trans9_eq_g`, `OAI.SharpPlanar.Numerical.lentry7_0_contains_g` and `OAI.SharpPlanar.Numerical.lentry7_1_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G359
import Definitions.Def_OAIQ098G362

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers10
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
noncomputable def trans8_r3 : Fin 16 → Fin 16 → CBox := ![trans8_r3_0,trans8_r3_1,trans8_r3_2,trans8_r3_3,trans8_r3_4,trans8_r3_5,trans8_r3_6,trans8_r3_7,trans8_r3_8,trans8_r3_9,trans8_r3_10,trans8_r3_11,trans8_r3_12,trans8_r3_13,trans8_r3_14,trans8_r3_15]
noncomputable def trans8 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans8_r0,trans8_r1,trans8_r2,trans8_r3,trans8_r4,trans8_r5]
noncomputable def trans9Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans8 j i k).mul (transStep j i k)
end SharpPlanar.CachedData

end OAI
end


