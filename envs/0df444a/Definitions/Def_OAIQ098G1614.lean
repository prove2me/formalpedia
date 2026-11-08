-- Prove2me | Definitions.Def_OAIQ098G1614
-- name    : OAIQ098G1614
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:31:59.215109+00:00
-- url     : https://prove2.me/theorems/6e3eacee-2baa-440a-8539-a7a662473a04
-- title:
--   Definitions bundle OAIQ098G1614 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.trans44Expr`, `OAI.SharpPlanar.CachedData.trans46Expr`, `OAI.SharpPlanar.CachedData.trans49Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_TransformedPowers50`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers50.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G064` and `OAIQ098G1422` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.CachedData.kernel49_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel49_1_contains_g`, `OAI.SharpPlanar.CachedData.tm0_48_1.KContains_g`, `OAI.SharpPlanar.CachedData.tm1_48_1.KContains_g`, `OAI.SharpPlanar.CachedData.trans50_contains_g`, `OAI.SharpPlanar.Residual45.bound0_0_g`, `OAI.SharpPlanar.Residual45.bound0_1_g`, `OAI.SharpPlanar.Residual45.bound1_0_g`, `OAI.SharpPlanar.Residual45.bound1_1_g`, `OAI.SharpPlanar.Residual48.bound0_0_g`, `OAI.SharpPlanar.Residual48.bound0_1_g`, `OAI.SharpPlanar.Residual48.bound1_0_g` and `OAI.SharpPlanar.Residual48.bound1_1_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G064
import Definitions.Def_OAIQ098G1422

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers50
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

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
noncomputable def trans44Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans43 j i k).mul (transStep j i k)
noncomputable def trans46Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans45 j i k).mul (transStep j i k)
noncomputable def trans49Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans48 j i k).mul (transStep j i k)
end SharpPlanar.CachedData

end OAI
end


