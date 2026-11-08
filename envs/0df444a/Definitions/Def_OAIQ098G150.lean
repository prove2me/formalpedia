-- Prove2me | Definitions.Def_OAIQ098G150
-- name    : OAIQ098G150
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T19:23:45.264389+00:00
-- url     : https://prove2.me/theorems/65efc7c4-a75b-43d8-9927-a10e70463f6d
-- title:
--   Definitions bundle OAIQ098G150 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 8 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.cm36_3_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm36_3_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm36_3_1_0.chunk`, `OAI.SharpPlanar.CachedData.cm36_3_1_1.chunk`, `OAI.SharpPlanar.CachedData.cm36_4_0_0.chunk`, `OAI.SharpPlanar.CachedData.cm36_4_0_1.chunk`, `OAI.SharpPlanar.CachedData.cm36_4_1_0.chunk`, `OAI.SharpPlanar.CachedData.cm36_4_1_1.chunk`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_UMoments36`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/UMoments36.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G032` and `OAIQ098G145` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.SharpPlanar.Numerical.U36.entry1_1_contains_g`, `OAI.SharpPlanar.Numerical.U36.entry2_1_contains_g`, `OAI.SharpPlanar.Numerical.U36.entry4_1_contains_g`, `OAI.SharpPlanar.Numerical.U36.entry5_1_contains_g`, `OAI.SharpPlanar.Numerical.U36.wuminus_column_g` and `OAI.SharpPlanar.Numerical.U36.wuplus_column_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G032
import Definitions.Def_OAIQ098G145

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments36
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
namespace cm36_3_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column36_0 j i k).mul (kernel3_0 j i k))
end cm36_3_0_0
namespace cm36_3_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column36_0 j i k).mul (kernel3_1 j i k))
end cm36_3_0_1
namespace cm36_3_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column36_1 j i k).mul (kernel3_0 j i k))
end cm36_3_1_0
namespace cm36_3_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column36_1 j i k).mul (kernel3_1 j i k))
end cm36_3_1_1
namespace cm36_4_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column36_0 j i k).mul (kernel4_0 j i k))
end cm36_4_0_0
namespace cm36_4_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column36_0 j i k).mul (kernel4_1 j i k))
end cm36_4_0_1
namespace cm36_4_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column36_1 j i k).mul (kernel4_0 j i k))
end cm36_4_1_0
namespace cm36_4_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column36_1 j i k).mul (kernel4_1 j i k))
end cm36_4_1_1
end SharpPlanar.CachedData

end OAI
end


