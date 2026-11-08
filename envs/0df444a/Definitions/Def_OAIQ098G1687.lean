-- Prove2me | Definitions.Def_OAIQ098G1687
-- name    : OAIQ098G1687
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T19:31:39.894227+00:00
-- url     : https://prove2.me/theorems/f05e4a8d-4557-4a1a-addb-c7029746127b
-- title:
--   Definitions bundle OAIQ098G1687 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.hexNode`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_HexLattice`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/HexLattice.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G000` and `OAIQ098G013` of this split; the published statements `OAI.SharpPlanar.hexNat_pos_g` and `OAI.SharpPlanar.hexNat_residue_g`.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.exactLeft_origin_positive_g` and `OAI.sharp_fourier_certificate`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G000
import Definitions.Def_OAIQ098G013
import Theorems.Thm_OAI_SharpPlanar_hexNat_pos_g
import Theorems.Thm_OAI_SharpPlanar_hexNat_residue_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HexLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
noncomputable def hexNode (v : ℤ×ℤ) (hv : v≠0) : Node := ⟨hexNat v,hexNat_pos_g hv,hexNat_residue_g v⟩
end SharpPlanar

end OAI
end


