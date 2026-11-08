-- Prove2me | Definitions.Def_OAIQ098G082
-- name    : OAIQ098G082
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:06:28.629323+00:00
-- url     : https://prove2.me/theorems/42817b85-af14-4eec-91f0-ceeb25bdb361
-- title:
--   Definitions bundle OAIQ098G082 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.IntegerCompact.roots24`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Fejer`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Fejer.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G053` and `OAIQ098G064` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G085`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G053
import Definitions.Def_OAIQ098G064

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
def roots24 : Fin 32 → CBox := ![IntegerRoots.root768,IntegerRoots.root769,IntegerRoots.root770,IntegerRoots.root771,IntegerRoots.root772,IntegerRoots.root773,IntegerRoots.root774,IntegerRoots.root775,IntegerRoots.root776,IntegerRoots.root777,IntegerRoots.root778,IntegerRoots.root779,IntegerRoots.root780,IntegerRoots.root781,IntegerRoots.root782,IntegerRoots.root783,IntegerRoots.root784,IntegerRoots.root785,IntegerRoots.root786,IntegerRoots.root787,IntegerRoots.root788,IntegerRoots.root789,IntegerRoots.root790,IntegerRoots.root791,IntegerRoots.root792,IntegerRoots.root793,IntegerRoots.root794,IntegerRoots.root795,IntegerRoots.root796,IntegerRoots.root797,IntegerRoots.root798,IntegerRoots.root799]
end SharpPlanar.IntegerCompact


end OAI
end


