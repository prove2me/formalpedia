-- Prove2me | Definitions.Def_OAIQ098G1673
-- name    : OAIQ098G1673
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T23:16:13.305665+00:00
-- url     : https://prove2.me/theorems/cb118e97-73aa-440a-ad9f-0133b0798b1c
-- title:
--   Definitions bundle OAIQ098G1673 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.tableList`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_TableList`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableList.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G001` and `OAIQ098G015` of this split; the published statement `OAI.SharpPlanar.tableCoords_mem_g`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1674`, `OAIQ098G1691` and `OAIQ098G1696`; the statement `OAI.SharpPlanar.tableList_discard_g`; the proof of `OAI.SharpPlanar.tableList_discard_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G001
import Definitions.Def_OAIQ098G015
import Theorems.Thm_OAI_SharpPlanar_tableCoords_mem_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableList
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

namespace SharpPlanar
open Numerical
noncomputable def tableList (a : Bool) : X := ⟨tableCoords a,tableCoords_mem_g a⟩
end SharpPlanar

end OAI
end


