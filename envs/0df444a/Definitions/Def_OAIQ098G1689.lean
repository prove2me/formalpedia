-- Prove2me | Definitions.Def_OAIQ098G1689
-- name    : OAIQ098G1689
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-09T19:22:05.777197+00:00
-- url     : https://prove2.me/theorems/a2142bd8-66f9-45d9-9114-1718b2002a1e
-- title:
--   Definitions bundle OAIQ098G1689 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SharpPlanar.transformRational`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_RationalBounds`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/RationalBounds.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G365`, `OAIQ098G1643` and `OAIQ098G1670` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1690` and `OAIQ098G1697`; the statement `OAI.SharpPlanar.transformEnvelope_le_rat_g`; the proofs of `OAI.SharpPlanar.error_large_cap_g`, `OAI.SharpPlanar.error_zero_cap_g`, `OAI.SharpPlanar.tail_second_bound_g` and `OAI.SharpPlanar.transformEnvelope_le_rat_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G365
import Definitions.Def_OAIQ098G1643
import Definitions.Def_OAIQ098G1670

section
-- module Solutions.OAIQ098_PP.PlanarPacking_RationalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rational Fourier envelopes

Explicit rational majorants control the direct and transformed spectral envelopes
at integral and half-integral radii.
-/

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
noncomputable def transformRational (ell n : ℕ) : ℝ :=
  ∑ j : Fin 6,densityCap j*pieceIntCap j n*(piUpper*zCap ⟨j.val,by omega⟩)^ell
end SharpPlanar

end OAI
end


