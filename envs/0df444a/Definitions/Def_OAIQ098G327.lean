-- Prove2me | Definitions.Def_OAIQ098G327
-- name    : OAIQ098G327
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T21:10:38.495767+00:00
-- url     : https://prove2.me/theorems/62f4dd82-ed3e-49a4-b8ff-25b8cfa1a06e
-- title:
--   Definitions bundle OAIQ098G327 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.power46`, `OAI.SharpPlanar.CachedData.power47Expr`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Powers50`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers50.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G324` and `OAIQ098G326` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.SharpPlanar.CachedData.power46_contains_g`; the proofs of `OAI.SharpPlanar.CachedData.column51_0_contains_g`, `OAI.SharpPlanar.CachedData.column51_1_contains_g`, `OAI.SharpPlanar.CachedData.column52_0_contains_g`, `OAI.SharpPlanar.CachedData.column52_1_contains_g`, `OAI.SharpPlanar.CachedData.power46_contains_g`, `OAI.SharpPlanar.CachedData.power54_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm48_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm49_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry1_0_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry2_0_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U48.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U48.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U48.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U49.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U49.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U49.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U49.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G324
import Definitions.Def_OAIQ098G326

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
noncomputable def power46 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power46_r0,power46_r1,power46_r2,power46_r3,power46_r4,power46_r5]
noncomputable def power47Expr (j : Fin 6) (i k : Fin 16) : CBox := (power46 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end


