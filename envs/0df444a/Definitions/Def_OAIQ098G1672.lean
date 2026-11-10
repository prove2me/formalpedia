-- Prove2me | Definitions.Def_OAIQ098G1672
-- name    : OAIQ098G1672
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-09T19:22:28.983842+00:00
-- url     : https://prove2.me/theorems/e2655f19-8c24-462a-b607-3bad8731248a
-- title:
--   Definitions bundle OAIQ098G1672 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.atomRowRat`, `OAI.SharpPlanar.atomTableRat`, `OAI.SharpPlanar.halfCap`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_AtomTail`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/AtomTail.lean), [`PlanarPacking_RationalBounds`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/RationalBounds.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G1643` and `OAIQ098G1670` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G1683`; the proofs of `OAI.SharpPlanar.error_large_cap_g`, `OAI.SharpPlanar.error_zero_cap_g`, `OAI.SharpPlanar.exact_head_lower_g` and `OAI.SharpPlanar.tail_second_bound_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G1643
import Definitions.Def_OAIQ098G1670

section
-- module Solutions.OAIQ098_PP.PlanarPacking_AtomTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerBasis
noncomputable def atomRowRat (j : Fin 7) (n : ℕ) : ℝ :=
  if n%12∈residues then atomFactorRat j n*(atomMass j*lambdaCap j*atomBase j^n) else 0
noncomputable def atomTableRat (N : ℕ) : ℝ := ∑ j : Fin 7,(∑ a : Fin 12,atomRowRat j (N+1+a.val))/(1-atomBase j^12)
end SharpPlanar

end OAI
end

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
noncomputable def halfCap (j : Fin 6) : ℝ := lambdaCap ⟨j.val,by omega⟩*halfBase j*halfMass j
end SharpPlanar

end OAI
end


