-- Prove2me | Definitions.Def_OAIQ098G259
-- name    : OAIQ098G259
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:02:19.652219+00:00
-- url     : https://prove2.me/theorems/ade4d725-a5f0-4b8a-b615-a00d5538762a
-- title:
--   Definitions bundle OAIQ098G259 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.column40_0Expr`, `OAI.SharpPlanar.CachedData.column40_1Expr`, `OAI.SharpPlanar.CachedData.power40`, `OAI.SharpPlanar.CachedData.power40_r5`, `OAI.SharpPlanar.CachedData.power41Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Columns40`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Columns40.lean), [`PlanarPacking_Certificate_Powers40`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers40.lean), [`PlanarPacking_Certificate_Powers50`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers50.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G256` and `OAIQ098G258` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G680`, `OAIQ098G681`, `OAIQ098G682`, `OAIQ098G683`, `OAIQ098G684`, `OAIQ098G685`, `OAIQ098G686` and `OAIQ098G687`; the proofs of `OAI.SharpPlanar.CachedData.column43_0_contains_g`, `OAI.SharpPlanar.CachedData.column43_1_contains_g`, `OAI.SharpPlanar.CachedData.power45_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm40_contains_g`, `OAI.SharpPlanar.Numerical.U40.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U40.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U40.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U40.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U40.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U40.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U40.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U40.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U40.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U40.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G256
import Definitions.Def_OAIQ098G258

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers40
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
noncomputable def power40_r5 : Fin 16 → Fin 16 → CBox := ![power40_r5_0,power40_r5_1,power40_r5_2,power40_r5_3,power40_r5_4,power40_r5_5,power40_r5_6,power40_r5_7,power40_r5_8,power40_r5_9,power40_r5_10,power40_r5_11,power40_r5_12,power40_r5_13,power40_r5_14,power40_r5_15]
noncomputable def power40 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power40_r0,power40_r1,power40_r2,power40_r3,power40_r4,power40_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns40
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
noncomputable def column40_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_0 j i k).mul (power40 j i k)
noncomputable def column40_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_1 j i k).mul (power40 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers50
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
noncomputable def power41Expr (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end


