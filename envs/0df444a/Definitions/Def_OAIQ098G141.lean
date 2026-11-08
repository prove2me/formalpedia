-- Prove2me | Definitions.Def_OAIQ098G141
-- name    : OAIQ098G141
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T19:10:14.477+00:00
-- url     : https://prove2.me/theorems/78d87edc-2a42-490e-821b-c0791392ebfd
-- title:
--   Definitions bundle OAIQ098G141 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 6 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.cm28_3_1_0.chunk`, `OAI.SharpPlanar.CachedData.cm28_3_1_1.chunk`, `OAI.SharpPlanar.CachedData.cm28_4_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm28_4_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm28_4_1_0.chunk`, `OAI.SharpPlanar.CachedData.cm28_4_1_1.chunk`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_UMoments28`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments28.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G032` and `OAIQ098G136` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Numerical.U28.entry2_0_contains_g`, `OAI.SharpPlanar.Numerical.U28.entry5_0_contains_g`, `OAI.SharpPlanar.Numerical.U28.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U28.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G032
import Definitions.Def_OAIQ098G136

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments28
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
namespace cm28_3_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column28_1 j i k).mul (kernel3_0 j i k))
end cm28_3_1_0
namespace cm28_3_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column28_1 j i k).mul (kernel3_1 j i k))
end cm28_3_1_1
namespace cm28_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column28_0 j i k).mul (kernel4_0 j i k))
end cm28_4_0_0
namespace cm28_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column28_0 j i k).mul (kernel4_1 j i k))
end cm28_4_0_1
namespace cm28_4_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column28_1 j i k).mul (kernel4_0 j i k))
end cm28_4_1_0
namespace cm28_4_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column28_1 j i k).mul (kernel4_1 j i k))
end cm28_4_1_1
end SharpPlanar.CachedData

end OAI
end


