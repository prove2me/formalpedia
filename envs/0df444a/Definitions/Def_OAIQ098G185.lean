-- Prove2me | Definitions.Def_OAIQ098G185
-- name    : OAIQ098G185
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-08T08:59:22.278292+00:00
-- url     : https://prove2.me/theorems/0a6dbb83-eeed-41af-99f3-ac8ad722e85e
-- title:
--   Definitions bundle OAIQ098G185 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 6 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.cm52_1_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm52_3_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm52_3_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm52_4_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm52_4_0_1.chunk`, `OAI.SharpPlanar.Numerical.U100.umat`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_UMoments52`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments52.lean), [`PlanarPacking_Certificate_WUCert100`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WUCert100.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G004` and `OAIQ098G180` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.SharpPlanar.Numerical.U100.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U100.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U100.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U100.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U100.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U100.wuplus_column_g`; the proofs of `OAI.SharpPlanar.Numerical.U100.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U100.entry0_1_contains_g`, `OAI.SharpPlanar.Numerical.U100.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U100.entry3_1_contains_g`, `OAI.SharpPlanar.Numerical.U100.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U100.wuplus_column_g`, `OAI.SharpPlanar.Numerical.U52.entry0_0_contains_g`, `OAI.SharpPlanar.Numerical.U52.entry3_0_contains_g`, `OAI.SharpPlanar.Numerical.U52.wuminus_column_g`, `OAI.SharpPlanar.Numerical.U52.wuplus_column_g` and `OAI.SharpPlanar.Numerical.signedVU_norm_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G004
import Definitions.Def_OAIQ098G180

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments52
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
open IntegerIntervals IntegerBasis IntegerGrid
namespace cm52_1_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column52_0 j i k).mul (kernel1_1 j i k))
end cm52_1_0_1
namespace cm52_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column52_0 j i k).mul (kernel3_0 j i k))
end cm52_3_0_0
namespace cm52_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column52_0 j i k).mul (kernel3_1 j i k))
end cm52_3_0_1
namespace cm52_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column52_0 j i k).mul (kernel4_0 j i k))
end cm52_4_0_0
namespace cm52_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column52_0 j i k).mul (kernel4_1 j i k))
end cm52_4_0_1
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert100
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

namespace SharpPlanar.Numerical.U100
open IntegerIntervals IntegerBasis IntegerGrid CachedData
noncomputable def umat : Matrix (Fin 6) (Fin 2) ℝ := fun i j => S (columnVector node (decide (j.val=1))) (jNode i,jDeriv i)
end SharpPlanar.Numerical.U100

end OAI
end


