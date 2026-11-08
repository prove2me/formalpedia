-- Prove2me | Definitions.Def_OAIQ098G032
-- name    : OAIQ098G032
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T17:59:25.953757+00:00
-- url     : https://prove2.me/theorems/2733cff5-29f8-49dc-ac8f-c0911a4b8d6f
-- title:
--   Definitions bundle OAIQ098G032 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.cm1_4_0_0.s0`, `OAI.SharpPlanar.CachedData.cm1_4_0_0.sums`, `OAI.SharpPlanar.CachedData.kernel4_0`, `OAI.SharpPlanar.CachedData.kernel4_0_r1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Certificate_DMoments1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/DMoments1.lean), [`PlanarPacking_Certificate_KernelValues10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/KernelValues10.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G027` and `OAIQ098G031` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G033`, `OAIQ098G035`, `OAIQ098G043`, `OAIQ098G045`, `OAIQ098G051`, `OAIQ098G106`, `OAIQ098G108`, `OAIQ098G110`, `OAIQ098G112`, `OAIQ098G114`, `OAIQ098G116`, `OAIQ098G128`, `OAIQ098G131`, `OAIQ098G135`, `OAIQ098G138`, `OAIQ098G141`, `OAIQ098G144`, `OAIQ098G147`, `OAIQ098G150`, `OAIQ098G1524`, `OAIQ098G153`, `OAIQ098G156`, `OAIQ098G1573`, `OAIQ098G161`, `OAIQ098G164`, `OAIQ098G167`, `OAIQ098G170`, `OAIQ098G173`, `OAIQ098G180`, `OAIQ098G182`, `OAIQ098G183`, `OAIQ098G187`, `OAIQ098G188`, `OAIQ098G190`, `OAIQ098G192`, `OAIQ098G194`, `OAIQ098G196`, `OAIQ098G198`, `OAIQ098G200`, `OAIQ098G202`, `OAIQ098G204`, `OAIQ098G206`, `OAIQ098G208`, `OAIQ098G210`, `OAIQ098G212`, `OAIQ098G214`, `OAIQ098G216`, `OAIQ098G219`, `OAIQ098G221`, `OAIQ098G223`, `OAIQ098G225`, `OAIQ098G227`, `OAIQ098G229`, `OAIQ098G231`, `OAIQ098G233`, `OAIQ098G235`, `OAIQ098G689`, `OAIQ098G690`, `OAIQ098G691`, `OAIQ098G692`, `OAIQ098G693`, `OAIQ098G694`, `OAIQ098G695`, `OAIQ098G696`, `OAIQ098G697`, `OAIQ098G698`, `OAIQ098G699`, `OAIQ098G700`, `OAIQ098G701` and `OAIQ098G702`; the statement `OAI.SharpPlanar.CachedData.kernel4_0_contains_g`; the proof of `OAI.SharpPlanar.CachedData.kernel4_0_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G027
import Definitions.Def_OAIQ098G031

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues10
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
noncomputable def kernel4_0_r1 : Fin 16 → Fin 16 → CBox := ![kernel4_0_r1_0,kernel4_0_r1_1,kernel4_0_r1_2,kernel4_0_r1_3,kernel4_0_r1_4,kernel4_0_r1_5,kernel4_0_r1_6,kernel4_0_r1_7,kernel4_0_r1_8,kernel4_0_r1_9,kernel4_0_r1_10,kernel4_0_r1_11,kernel4_0_r1_12,kernel4_0_r1_13,kernel4_0_r1_14,kernel4_0_r1_15]
noncomputable def kernel4_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel4_0_r0,kernel4_0_r1,kernel4_0_r2,kernel4_0_r3,kernel4_0_r4,kernel4_0_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_DMoments1
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
namespace cm1_4_0_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm1_4_0_0
end SharpPlanar.CachedData

end OAI
end


