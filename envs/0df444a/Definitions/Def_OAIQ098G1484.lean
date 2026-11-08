-- Prove2me | Definitions.Def_OAIQ098G1484
-- name    : OAIQ098G1484
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T19:21:43.310239+00:00
-- url     : https://prove2.me/theorems/2fd5b612-9b19-49b5-9535-7b2006982155
-- title:
--   Definitions bundle OAIQ098G1484 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.mpower1_26Expr`, `OAI.SharpPlanar.CachedData.mpower1_27Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_MomentPowers30`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/MomentPowers30.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G020` and `OAIQ098G463` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Bernstein0.N1_right.t26_contains_g`, `OAI.SharpPlanar.Bernstein0.N1_right.t27_contains_g`, `OAI.SharpPlanar.Bernstein0.N1_right.t28_contains_g`, `OAI.SharpPlanar.Bernstein1.N0_right.t25_contains_g`, `OAI.SharpPlanar.Bernstein1.N0_right.t26_contains_g`, `OAI.SharpPlanar.Bernstein1.N0_right.t27_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_left.t24_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_left.t25_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_left.t26_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_right.t24_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_right.t25_contains_g`, `OAI.SharpPlanar.Bernstein1.N1_right.t26_contains_g`, `OAI.SharpPlanar.CachedData.hk1_1_29_contains_g` and `OAI.SharpPlanar.CachedData.mpower1_30_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G020
import Definitions.Def_OAIQ098G463

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MomentPowers30
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
noncomputable def mpower1_26Expr (j : Fin 6) (i k : Fin 16) : CBox := ((mpower1_25 j i k).mul (piI.mul (gridRows j i k).z)).scale 1 26
noncomputable def mpower1_27Expr (j : Fin 6) (i k : Fin 16) : CBox := ((mpower1_26 j i k).mul (piI.mul (gridRows j i k).z)).scale 1 27
end SharpPlanar.CachedData

end OAI
end


