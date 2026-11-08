-- Prove2me | Definitions.Def_OAIQ098G081
-- name    : OAIQ098G081
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:05:08.656187+00:00
-- url     : https://prove2.me/theorems/072e5120-7161-46f4-9f52-c0699794f177
-- title:
--   Definitions bundle OAIQ098G081 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.IntegerCompact.roots0`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Fejer`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Fejer.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G053`, `OAIQ098G059` and `OAIQ098G064` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G085`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G053
import Definitions.Def_OAIQ098G059
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
def roots0 : Fin 32 → CBox := ![IntegerRoots.root0,IntegerRoots.root1,IntegerRoots.root2,IntegerRoots.root3,IntegerRoots.root4,IntegerRoots.root5,IntegerRoots.root6,IntegerRoots.root7,IntegerRoots.root8,IntegerRoots.root9,IntegerRoots.root10,IntegerRoots.root11,IntegerRoots.root12,IntegerRoots.root13,IntegerRoots.root14,IntegerRoots.root15,IntegerRoots.root16,IntegerRoots.root17,IntegerRoots.root18,IntegerRoots.root19,IntegerRoots.root20,IntegerRoots.root21,IntegerRoots.root22,IntegerRoots.root23,IntegerRoots.root24,IntegerRoots.root25,IntegerRoots.root26,IntegerRoots.root27,IntegerRoots.root28,IntegerRoots.root29,IntegerRoots.root30,IntegerRoots.root31]
end SharpPlanar.IntegerCompact


end OAI
end


