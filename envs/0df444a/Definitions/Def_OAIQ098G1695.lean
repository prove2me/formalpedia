-- Prove2me | Definitions.Def_OAIQ098G1695
-- name    : OAIQ098G1695
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T23:21:09.19349+00:00
-- url     : https://prove2.me/theorems/98baab14-2d5c-4e56-a5f0-4baf9632cb12
-- title:
--   Definitions bundle OAIQ098G1695 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.tableHJet`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_FullMomentBridge`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/FullMomentBridge.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G1642` and `OAIQ098G1691` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.SharpPlanar.error_large_cap_g`, `OAI.SharpPlanar.error_one_cap_g`, `OAI.SharpPlanar.error_two_cap_g`, `OAI.SharpPlanar.error_zero_cap_g`, `OAI.SharpPlanar.normalizedH_table_g` and `OAI.SharpPlanar.table_jet_sharp_g`; the proofs of `OAI.SharpPlanar.error_large_cap_g`, `OAI.SharpPlanar.error_one_cap_g`, `OAI.SharpPlanar.error_two_cap_g`, `OAI.SharpPlanar.error_zero_cap_g`, `OAI.SharpPlanar.exactLeft_origin_positive_g`, `OAI.SharpPlanar.halfSign_0_N1_right_g`, `OAI.SharpPlanar.normalizedCandidate_fourier_nonneg_g`, `OAI.SharpPlanar.normalizedH_table_g`, `OAI.SharpPlanar.sourcePower_sharp_g`, `OAI.SharpPlanar.table_jet_sharp_g` and `OAI.sharp_fourier_certificate`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G1642
import Definitions.Def_OAIQ098G1691

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FullMomentBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped BigOperators
noncomputable def tableHJet (a : Bool) (ell : ℕ) (s : ℝ) : ℝ :=
  cardinalSeries (tableData a) ell s+K (tableData (!a)) ell s
end SharpPlanar

end OAI
end


