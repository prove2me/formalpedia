-- Prove2me | Definitions.Def_OAIQ098G1670
-- name    : OAIQ098G1670
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-09T19:21:07.400408+00:00
-- url     : https://prove2.me/theorems/924e678f-e939-4a74-a93e-2abbceae4a8b
-- title:
--   Definitions bundle OAIQ098G1670 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7 declarations of OpenAI's Lean: 7 definitions. The definitions and types are `OAI.SharpPlanar.atomFactorRat`, `OAI.SharpPlanar.atomRow`, `OAI.SharpPlanar.atomRowFactor`, `OAI.SharpPlanar.atomRowTable`, `OAI.SharpPlanar.atomicEnvelope`, `OAI.SharpPlanar.halfMass`, `OAI.SharpPlanar.pieceIntCap`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_AtomTail`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/AtomTail.lean), [`PlanarPacking_Envelopes`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Envelopes.lean), [`PlanarPacking_RationalBounds`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/RationalBounds.lean).
--
--   **Imports.** It imports the bundle `OAIQ098G362` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1672` and `OAIQ098G1689`; the statements `OAI.SharpPlanar.atomicEnvelope_le_rat_g`, `OAI.SharpPlanar.atomicEnvelope_nonneg_g` and `OAI.SharpPlanar.pieceL_le_intCap_g`; the proofs of `OAI.SharpPlanar.atomicEnvelope_le_rat_g`, `OAI.SharpPlanar.atomicEnvelope_nonneg_g` and `OAI.SharpPlanar.pieceL_le_intCap_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G362

section
-- module Solutions.OAIQ098_PP.PlanarPacking_AtomTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerBasis
noncomputable def atomRowFactor (j : Fin 7) (n : ℕ) : ℝ := (1+|D n|+Real.pi*zCap j)/Q n
noncomputable def atomRow (j : Fin 7) (n : ℕ) : ℝ :=
  if n%12∈residues then atomRowFactor j n*atomL j n else 0
noncomputable def atomRowTable (N : ℕ) : ℝ :=
  ∑ j : Fin 7, (∑ a : Fin 12, atomRow j (N+1+a.val))/(1-Real.exp (-12*Real.pi*dampingCap j))
noncomputable def atomFactorRat (j : Fin 7) (n : ℕ) : ℝ := (1+rowDUpper n+(31416/10000:ℝ)*zCap j)/rowQLower n
end SharpPlanar

end OAI
end

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
noncomputable def atomicEnvelope (ell : ℕ) (s : ℝ) : ℝ :=
  ∑ j : Fin 7,atomL j s*(Real.pi*zCap j)^ell
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
noncomputable def pieceIntCap (j : Fin 6) (n : ℕ) : ℝ :=
  lambdaCap ⟨j.val,by omega⟩*pieceBase j^n*massRational j n
noncomputable def halfMass (j : Fin 6) : ℝ :=
  if slopeCap j=0 then 1/6 else min (1/6) (2/((314159/100000:ℝ)*slopeCap j))
end SharpPlanar

end OAI
end


