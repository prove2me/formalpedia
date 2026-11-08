-- Prove2me | Definitions.Def_OAIQ098G1628
-- name    : OAIQ098G1628
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T19:28:18.303363+00:00
-- url     : https://prove2.me/theorems/1c347466-b980-4eac-9251-35c4370461f6
-- title:
--   Definitions bundle OAIQ098G1628 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.CachedData.trans70Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_TransformedPowers70`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers70.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G064` and `OAIQ098G1440` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.SharpPlanar.CachedData.trans71_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G064
import Definitions.Def_OAIQ098G1440

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers70
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
noncomputable def trans70Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans69 j i k).mul (transStep j i k)
end SharpPlanar.CachedData

end OAI
end


