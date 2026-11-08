-- Prove2me | Definitions.Def_OAIQ098G1454
-- name    : OAIQ098G1454
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T19:15:54.144885+00:00
-- url     : https://prove2.me/theorems/6be949f7-965f-40ea-8bb0-60dbd395f293
-- title:
--   Definitions bundle OAIQ098G1454 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.kernel93_0Expr`, `OAI.SharpPlanar.CachedData.kernel93_1Expr`, `OAI.SharpPlanar.CachedData.kernel96_0Expr`, `OAI.SharpPlanar.CachedData.kernel96_1Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_KernelValues100`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues100.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G020` and `OAIQ098G1452` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.CachedData.tm0_96_1.KContains_g`, `OAI.SharpPlanar.CachedData.tm1_96_1.KContains_g`, `OAI.SharpPlanar.Residual93.bound0_0_g`, `OAI.SharpPlanar.Residual93.bound0_1_g`, `OAI.SharpPlanar.Residual93.bound1_0_g`, `OAI.SharpPlanar.Residual93.bound1_1_g`, `OAI.SharpPlanar.Residual96.bound0_0_g`, `OAI.SharpPlanar.Residual96.bound0_1_g`, `OAI.SharpPlanar.Residual96.bound1_0_g` and `OAI.SharpPlanar.Residual96.bound1_1_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G020
import Definitions.Def_OAIQ098G1452

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues100
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
noncomputable def kernel93_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (gridRows j i k).lam.mul (trans93 j i k)
noncomputable def kernel93_1Expr (j : Fin 6) (i k : Fin 16) : CBox := ((gridRows j i k).lam.mul (trans93 j i k)).mul (piI.mul (gridRows j i k).z)
noncomputable def kernel96_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (gridRows j i k).lam.mul (trans96 j i k)
noncomputable def kernel96_1Expr (j : Fin 6) (i k : Fin 16) : CBox := ((gridRows j i k).lam.mul (trans96 j i k)).mul (piI.mul (gridRows j i k).z)
end SharpPlanar.CachedData

end OAI
end


