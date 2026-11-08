-- Prove2me | Definitions.Def_OAIQ098G084
-- name    : OAIQ098G084
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:06:40.100654+00:00
-- url     : https://prove2.me/theorems/22456d6a-7294-4714-8a79-034aa3204b35
-- title:
--   Definitions bundle OAIQ098G084 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.IntegerCompact.roots5`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Fejer`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Fejer.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G064` and `OAIQ098G083` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G085`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G064
import Definitions.Def_OAIQ098G083

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Fejer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fejér quadrature enclosures

Certified nodes and weights for the 256-node cosine quadrature rule.
-/

namespace SharpPlanar.IntegerCompact
open IntegerIntervals
def roots5 : Fin 32 → CBox := ![IntegerRoots.root160,IntegerRoots.root161,IntegerRoots.root162,IntegerRoots.root163,IntegerRoots.root164,IntegerRoots.root165,IntegerRoots.root166,IntegerRoots.root167,IntegerRoots.root168,IntegerRoots.root169,IntegerRoots.root170,IntegerRoots.root171,IntegerRoots.root172,IntegerRoots.root173,IntegerRoots.root174,IntegerRoots.root175,IntegerRoots.root176,IntegerRoots.root177,IntegerRoots.root178,IntegerRoots.root179,IntegerRoots.root180,IntegerRoots.root181,IntegerRoots.root182,IntegerRoots.root183,IntegerRoots.root184,IntegerRoots.root185,IntegerRoots.root186,IntegerRoots.root187,IntegerRoots.root188,IntegerRoots.root189,IntegerRoots.root190,IntegerRoots.root191]
end SharpPlanar.IntegerCompact


end OAI
end


