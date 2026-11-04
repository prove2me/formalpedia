-- Prove2me | Definitions.Def_OAIQ098E013
-- name    : OAIQ098E013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T04:52:44.02963+00:00
-- url     : https://prove2.me/theorems/a4bb701c-4b0b-4684-ab90-aa9b6dc99091
-- title:
--   Definitions bundle OAIQ098E013 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.hexForm`, `OAI.SharpPlanar.hexNat`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_HexLattice`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/HexLattice.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098E239`; the statements `OAI.SharpPlanar.hexNat_pos_e` and `OAI.SharpPlanar.hexNat_residue_e`; the proofs of `OAI.SharpPlanar.hexNat_pos_e` and `OAI.SharpPlanar.hexNat_residue_e`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HexLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
def hexForm (v : ℤ×ℤ) : ℤ := v.1^2+v.1*v.2+v.2^2
def hexNat (v : ℤ×ℤ) : ℕ := (hexForm v).toNat
end SharpPlanar

end OAI
end


