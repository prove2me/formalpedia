-- Prove2me | Definitions.Def_OAIQ098G1675
-- name    : OAIQ098G1675
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T22:09:21.776835+00:00
-- url     : https://prove2.me/theorems/0ebf8e5c-3a55-4663-9336-ca4a1eb70662
-- title:
--   Definitions bundle OAIQ098G1675 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.directEnvelope`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Envelopes`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Envelopes.lean).
--
--   **Imports.** It imports the bundle `OAIQ098G365` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.SharpPlanar.directEnvelope_le_rat_g` and `OAI.SharpPlanar.direct_spectral_bound_g`; the proofs of `OAI.SharpPlanar.directEnvelope_le_rat_g`, `OAI.SharpPlanar.direct_spectral_bound_g`, `OAI.SharpPlanar.error_large_cap_g`, `OAI.SharpPlanar.error_one_cap_g`, `OAI.SharpPlanar.error_two_cap_g`, `OAI.SharpPlanar.error_zero_cap_g`, `OAI.SharpPlanar.halfSign_0_N1_right_g`, `OAI.SharpPlanar.normalizedCandidate_fourier_nonneg_g`, `OAI.SharpPlanar.table_jet_sharp_g`, `OAI.SharpPlanar.tail_second_bound_g` and `OAI.sharp_fourier_certificate`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G365

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Envelopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spectral derivative bounds

Monotone spectral envelopes bound the cardinal functions and their Fourier kernels.
The estimates follow *A sharp Fourier certificate for planar circle packing*
(OpenAI, 2026).
-/

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
noncomputable def directEnvelope (ell : ℕ) : ℝ :=
  ∑ j : Fin 6,densityCap j/6*(Real.pi*((j.val:ℝ)+1)/6)^ell
end SharpPlanar

end OAI
end


