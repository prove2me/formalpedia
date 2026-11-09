-- Prove2me | Definitions.Def_OAIQ098G332
-- name    : OAIQ098G332
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-08T08:57:30.56267+00:00
-- url     : https://prove2.me/theorems/c5030619-3c16-443d-9a20-e2bf91727ebf
-- title:
--   Definitions bundle OAIQ098G332 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.power56Expr`, `OAI.SharpPlanar.CachedData.power58Expr`, `OAI.SharpPlanar.Numerical.U12.umat`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_Powers60`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/Powers60.lean), [`PlanarPacking_Certificate_WUCert12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert12.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G004`, `OAIQ098G020` and `OAIQ098G266` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.SharpPlanar.Numerical.U12.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U12.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U12.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U12.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U12.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U12.wuplus_column_g`; the proofs of `OAI.SharpPlanar.CachedData.column60_0_contains_g`, `OAI.SharpPlanar.CachedData.column60_1_contains_g`, `OAI.SharpPlanar.CachedData.power61_contains_g`, `OAI.SharpPlanar.CachedData.tableTerm57_contains_g`, `OAI.SharpPlanar.Numerical.U12.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U12.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U12.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U12.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U12.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U12.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U57.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry4_0_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U57.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U57.wuminus_contains_g`, `OAI.SharpPlanar.Numerical.U57.wuplus_contains_g` and `OAI.SharpPlanar.Numerical.signedVU_norm_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G004
import Definitions.Def_OAIQ098G020
import Definitions.Def_OAIQ098G266

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers60
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
noncomputable def power56Expr (j : Fin 6) (i k : Fin 16) : CBox := (power55 j i k).mul (gridRows j i k).direct
noncomputable def power58Expr (j : Fin 6) (i k : Fin 16) : CBox := (power57 j i k).mul (gridRows j i k).direct
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert12
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

namespace SharpPlanar.Numerical.U12
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U12

end OAI
end


