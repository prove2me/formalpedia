-- Prove2me | Definitions.Def_OAIQ098G1620
-- name    : OAIQ098G1620
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T18:33:30.76204+00:00
-- url     : https://prove2.me/theorems/ac373796-921f-4dea-9f3f-1e601fe28aa7
-- title:
--   Definitions bundle OAIQ098G1620 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7 declarations of OpenAI's Lean: 7 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.trans55Expr`, `OAI.SharpPlanar.CachedData.trans57Expr`, `OAI.SharpPlanar.CachedData.trans59Expr`, `OAI.SharpPlanar.CachedData.trans60Expr`, `OAI.SharpPlanar.CachedData.trans63Expr`, `OAI.SharpPlanar.CachedData.trans66Expr`, `OAI.SharpPlanar.CachedData.trans67Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_TransformedPowers60`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers60.lean), [`PlanarPacking_Certificate_TransformedPowers70`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TransformedPowers70.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G064` and `OAIQ098G1616` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.CachedData.kernel63_0_contains_g`, `OAI.SharpPlanar.CachedData.kernel63_1_contains_g`, `OAI.SharpPlanar.CachedData.tm0_55_1.KContains_g`, `OAI.SharpPlanar.CachedData.tm0_61_1.KContains_g`, `OAI.SharpPlanar.CachedData.tm0_67_1.KContains_g`, `OAI.SharpPlanar.CachedData.tm0_69_1.KContains_g`, `OAI.SharpPlanar.CachedData.tm1_55_1.KContains_g`, `OAI.SharpPlanar.CachedData.tm1_61_1.KContains_g`, `OAI.SharpPlanar.CachedData.tm1_67_1.KContains_g`, `OAI.SharpPlanar.CachedData.tm1_69_1.KContains_g`, `OAI.SharpPlanar.CachedData.trans57_contains_g`, `OAI.SharpPlanar.CachedData.trans64_contains_g`, `OAI.SharpPlanar.CachedData.trans71_contains_g`, `OAI.SharpPlanar.Residual55.bound0_0_g`, `OAI.SharpPlanar.Residual55.bound0_1_g`, `OAI.SharpPlanar.Residual55.bound1_0_g`, `OAI.SharpPlanar.Residual55.bound1_1_g`, `OAI.SharpPlanar.Residual60.bound0_0_g`, `OAI.SharpPlanar.Residual60.bound0_1_g`, `OAI.SharpPlanar.Residual60.bound1_0_g`, `OAI.SharpPlanar.Residual60.bound1_1_g`, `OAI.SharpPlanar.Residual61.bound0_0_g`, `OAI.SharpPlanar.Residual61.bound0_1_g`, `OAI.SharpPlanar.Residual61.bound1_0_g`, `OAI.SharpPlanar.Residual61.bound1_1_g`, `OAI.SharpPlanar.Residual67.bound0_0_g`, `OAI.SharpPlanar.Residual67.bound0_1_g`, `OAI.SharpPlanar.Residual67.bound1_0_g`, `OAI.SharpPlanar.Residual67.bound1_1_g`, `OAI.SharpPlanar.Residual69.bound0_0_g`, `OAI.SharpPlanar.Residual69.bound0_1_g`, `OAI.SharpPlanar.Residual69.bound1_0_g` and `OAI.SharpPlanar.Residual69.bound1_1_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G064
import Definitions.Def_OAIQ098G1616

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers60
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
noncomputable def trans55Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans54 j i k).mul (transStep j i k)
noncomputable def trans57Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans56 j i k).mul (transStep j i k)
noncomputable def trans59Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans58 j i k).mul (transStep j i k)
noncomputable def trans60Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans59 j i k).mul (transStep j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers70
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
noncomputable def trans63Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans62 j i k).mul (transStep j i k)
noncomputable def trans66Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans65 j i k).mul (transStep j i k)
noncomputable def trans67Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans66 j i k).mul (transStep j i k)
end SharpPlanar.CachedData

end OAI
end


