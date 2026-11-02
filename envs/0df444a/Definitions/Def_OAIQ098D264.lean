-- Prove2me | Definitions.Def_OAIQ098D264
-- name    : OAIQ098D264
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T16:29:13.786058+00:00
-- url     : https://prove2.me/theorems/315fa14f-5370-4fc2-9359-7f0980e377c8
-- title:
--   Definitions bundle OAIQ098D264 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 578 declarations of OpenAI's Lean: 109 definitions and 469 theorems. The definitions and types are `OAI.SharpPlanar.CachedData.cm100_1_0_1.s0`, `OAI.SharpPlanar.CachedData.cm100_1_0_1.s1`, `OAI.SharpPlanar.CachedData.cm100_1_0_1.s2`, `OAI.SharpPlanar.CachedData.cm100_1_0_1.s3`, `OAI.SharpPlanar.CachedData.cm100_1_0_1.s4`, `OAI.SharpPlanar.CachedData.cm100_1_0_1.s5`, `OAI.SharpPlanar.CachedData.cm100_1_0_1.sums`, `OAI.SharpPlanar.CachedData.cm100_1_1_0.s0`, `OAI.SharpPlanar.CachedData.cm100_1_1_0.s1`, `OAI.SharpPlanar.CachedData.cm100_1_1_0.s2`, `OAI.SharpPlanar.CachedData.cm100_1_1_0.s3`, `OAI.SharpPlanar.CachedData.cm100_1_1_0.s4`, `OAI.SharpPlanar.CachedData.cm100_1_1_0.s5`, `OAI.SharpPlanar.CachedData.cm100_1_1_0.sums`, `OAI.SharpPlanar.CachedData.cm100_1_1_1.s0`, `OAI.SharpPlanar.CachedData.cm100_1_1_1.s1`, `OAI.SharpPlanar.CachedData.cm100_1_1_1.s2`, `OAI.SharpPlanar.CachedData.cm100_1_1_1.s3`, `OAI.SharpPlanar.CachedData.cm100_1_1_1.sums`, `OAI.SharpPlanar.CachedData.cm100_3_0_0.s0`, `OAI.SharpPlanar.CachedData.cm100_3_0_0.sums`, `OAI.SharpPlanar.CachedData.cm100_3_0_1.s0`, `OAI.SharpPlanar.CachedData.cm100_3_0_1.sums`, `OAI.SharpPlanar.CachedData.cm100_4_0_0.s0`, `OAI.SharpPlanar.CachedData.cm100_4_0_0.s1`, `OAI.SharpPlanar.CachedData.cm100_4_0_0.sums`, `OAI.SharpPlanar.CachedData.cm12_3_0_1.s0`, `OAI.SharpPlanar.CachedData.cm12_3_0_1.s1`, `OAI.SharpPlanar.CachedData.column100_1Expr`, `OAI.SharpPlanar.CachedData.column12_0Expr`, `OAI.SharpPlanar.CachedData.column12_1Expr`, `OAI.SharpPlanar.CachedData.column13_0Expr`, `OAI.SharpPlanar.CachedData.kernel4_0`, `OAI.SharpPlanar.CachedData.kernel4_0_r3`, `OAI.SharpPlanar.CachedData.power0`, `OAI.SharpPlanar.CachedData.power10`, `OAI.SharpPlanar.CachedData.power10_r3`, `OAI.SharpPlanar.CachedData.power13`, `OAI.SharpPlanar.CachedData.power13_r4`, `OAI.SharpPlanar.CachedData.power15` and 69 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_Certificate_Columns100`, `PlanarPacking_Certificate_Columns20`, `PlanarPacking_Certificate_KernelValues10`, `PlanarPacking_Certificate_Powers10`, `PlanarPacking_Certificate_Powers20`, `PlanarPacking_Certificate_Powers30`, `PlanarPacking_Certificate_Powers40`, `PlanarPacking_Certificate_Powers50`, `PlanarPacking_Certificate_Powers60`, `PlanarPacking_Certificate_Powers70`, `PlanarPacking_Certificate_Powers80`, `PlanarPacking_Certificate_Powers90`, `PlanarPacking_Certificate_TransformedPowers10`, `PlanarPacking_Certificate_UMoments100`, `PlanarPacking_Certificate_UMoments12`.
--
--   **Imports.** It imports the bundles `OAIQ098D006`, `OAIQ098D033`, `OAIQ098D041`, `OAIQ098D042`, `OAIQ098D044`, `OAIQ098D045`, `OAIQ098D046`, `OAIQ098D047`, `OAIQ098D049`, `OAIQ098D050`, `OAIQ098D051`, `OAIQ098D052`, `OAIQ098D053`, `OAIQ098D054`, `OAIQ098D055`, `OAIQ098D056`, `OAIQ098D057`, `OAIQ098D058`, `OAIQ098D059`, `OAIQ098D060`, `OAIQ098D061`, `OAIQ098D062`, `OAIQ098D063`, `OAIQ098D064`, `OAIQ098D065`, `OAIQ098D066`, `OAIQ098D067`, `OAIQ098D068`, `OAIQ098D069`, `OAIQ098D070`, `OAIQ098D071`, `OAIQ098D072`, `OAIQ098D073`, `OAIQ098D074`, `OAIQ098D075`, `OAIQ098D076`, `OAIQ098D077`, `OAIQ098D078`, `OAIQ098D079`, `OAIQ098D080`, `OAIQ098D081`, `OAIQ098D082`, `OAIQ098D083`, `OAIQ098D084` and `OAIQ098D085` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098D277`, `OAIQ098D278`, `OAIQ098D279`, `OAIQ098D280`, `OAIQ098D281`, `OAIQ098D282`, `OAIQ098D283`, `OAIQ098D284`, `OAIQ098D285`, `OAIQ098D286`, `OAIQ098D287`, `OAIQ098D288`, `OAIQ098D289`, `OAIQ098D290`, `OAIQ098D291`, `OAIQ098D292`, `OAIQ098D293`, `OAIQ098D294`, `OAIQ098D295`, `OAIQ098D296`, `OAIQ098D297`, `OAIQ098D298`, `OAIQ098D299`, `OAIQ098D301`, `OAIQ098D302`, `OAIQ098D303`, `OAIQ098D306`, `OAIQ098D308`, `OAIQ098D309`, `OAIQ098D310`, `OAIQ098D311`, `OAIQ098D312`, `OAIQ098D313`, `OAIQ098D314`, `OAIQ098D317`, `OAIQ098D318`, `OAIQ098D319`, `OAIQ098D320`, `OAIQ098D321`, `OAIQ098D322`, `OAIQ098D323`, `OAIQ098D324`, `OAIQ098D325`, `OAIQ098D326`, `OAIQ098D327`, `OAIQ098D328`, `OAIQ098D329`, `OAIQ098D330`, `OAIQ098D331`, `OAIQ098D332`, `OAIQ098D333`, `OAIQ098D334`, `OAIQ098D335`, `OAIQ098D336`, `OAIQ098D337`, `OAIQ098D338`, `OAIQ098D339`, `OAIQ098D340`, `OAIQ098D341`, `OAIQ098D342`, `OAIQ098D343`, `OAIQ098D344`, `OAIQ098D345`, `OAIQ098D346`, `OAIQ098D347`, `OAIQ098D348`, `OAIQ098D349`, `OAIQ098D350`, `OAIQ098D351`, `OAIQ098D352`, `OAIQ098D353`, `OAIQ098D354`, `OAIQ098D355`, `OAIQ098D356`, `OAIQ098D357`, `OAIQ098D359`, `OAIQ098D360`, `OAIQ098D363`, `OAIQ098D373`, `OAIQ098D378`, `OAIQ098D379`, `OAIQ098D382`, `OAIQ098D391`, `OAIQ098D396`, `OAIQ098D397`, `OAIQ098D399`, `OAIQ098D409`, `OAIQ098D416`, `OAIQ098D418`, `OAIQ098D419`, `OAIQ098D422`, `OAIQ098D426`, `OAIQ098D428`, `OAIQ098D429`, `OAIQ098D430`, `OAIQ098D431`, `OAIQ098D432`, `OAIQ098D435`, `OAIQ098D438`, `OAIQ098D439`, `OAIQ098D441`, `OAIQ098D443`, `OAIQ098D444`, `OAIQ098D445`, `OAIQ098D447`, `OAIQ098D448`, `OAIQ098D450`, `OAIQ098D452`, `OAIQ098D453`, `OAIQ098D455`, `OAIQ098D457`, `OAIQ098D458`, `OAIQ098D459`, `OAIQ098D460`, `OAIQ098D462`, `OAIQ098D463`, `OAIQ098D464`, `OAIQ098D465`, `OAIQ098D466`, `OAIQ098D469`, `OAIQ098D470`, `OAIQ098D471`, `OAIQ098D472` and `OAIQ098D473`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098D006
import Definitions.Def_OAIQ098D033
import Definitions.Def_OAIQ098D041
import Definitions.Def_OAIQ098D042
import Definitions.Def_OAIQ098D044
import Definitions.Def_OAIQ098D045
import Definitions.Def_OAIQ098D046
import Definitions.Def_OAIQ098D047
import Definitions.Def_OAIQ098D049
import Definitions.Def_OAIQ098D050
import Definitions.Def_OAIQ098D051
import Definitions.Def_OAIQ098D052
import Definitions.Def_OAIQ098D053
import Definitions.Def_OAIQ098D054
import Definitions.Def_OAIQ098D055
import Definitions.Def_OAIQ098D056
import Definitions.Def_OAIQ098D057
import Definitions.Def_OAIQ098D058
import Definitions.Def_OAIQ098D059
import Definitions.Def_OAIQ098D060
import Definitions.Def_OAIQ098D061
import Definitions.Def_OAIQ098D062
import Definitions.Def_OAIQ098D063
import Definitions.Def_OAIQ098D064
import Definitions.Def_OAIQ098D065
import Definitions.Def_OAIQ098D066
import Definitions.Def_OAIQ098D067
import Definitions.Def_OAIQ098D068
import Definitions.Def_OAIQ098D069
import Definitions.Def_OAIQ098D070
import Definitions.Def_OAIQ098D071
import Definitions.Def_OAIQ098D072
import Definitions.Def_OAIQ098D073
import Definitions.Def_OAIQ098D074
import Definitions.Def_OAIQ098D075
import Definitions.Def_OAIQ098D076
import Definitions.Def_OAIQ098D077
import Definitions.Def_OAIQ098D078
import Definitions.Def_OAIQ098D079
import Definitions.Def_OAIQ098D080
import Definitions.Def_OAIQ098D081
import Definitions.Def_OAIQ098D082
import Definitions.Def_OAIQ098D083
import Definitions.Def_OAIQ098D084
import Definitions.Def_OAIQ098D085

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers10
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
noncomputable def power0 (_j : Fin 6) (_i _k : Fin 16) : CBox := CBox.rat 1 1 0 1
noncomputable def power2_r5 : Fin 16 → Fin 16 → CBox := ![power2_r5_0,power2_r5_1,power2_r5_2,power2_r5_3,power2_r5_4,power2_r5_5,power2_r5_6,power2_r5_7,power2_r5_8,power2_r5_9,power2_r5_10,power2_r5_11,power2_r5_12,power2_r5_13,power2_r5_14,power2_r5_15]
noncomputable def power2 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power2_r0,power2_r1,power2_r2,power2_r3,power2_r4,power2_r5]
noncomputable def power4 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power4_r0,power4_r1,power4_r2,power4_r3,power4_r4,power4_r5]
noncomputable def power7_r2 : Fin 16 → Fin 16 → CBox := ![power7_r2_0,power7_r2_1,power7_r2_2,power7_r2_3,power7_r2_4,power7_r2_5,power7_r2_6,power7_r2_7,power7_r2_8,power7_r2_9,power7_r2_10,power7_r2_11,power7_r2_12,power7_r2_13,power7_r2_14,power7_r2_15]
noncomputable def power7 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power7_r0,power7_r1,power7_r2,power7_r3,power7_r4,power7_r5]
noncomputable def power9_r1 : Fin 16 → Fin 16 → CBox := ![power9_r1_0,power9_r1_1,power9_r1_2,power9_r1_3,power9_r1_4,power9_r1_5,power9_r1_6,power9_r1_7,power9_r1_8,power9_r1_9,power9_r1_10,power9_r1_11,power9_r1_12,power9_r1_13,power9_r1_14,power9_r1_15]
noncomputable def power9 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power9_r0,power9_r1,power9_r2,power9_r3,power9_r4,power9_r5]
noncomputable def power10_r3 : Fin 16 → Fin 16 → CBox := ![power10_r3_0,power10_r3_1,power10_r3_2,power10_r3_3,power10_r3_4,power10_r3_5,power10_r3_6,power10_r3_7,power10_r3_8,power10_r3_9,power10_r3_10,power10_r3_11,power10_r3_12,power10_r3_13,power10_r3_14,power10_r3_15]
noncomputable def power10 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power10_r0,power10_r1,power10_r2,power10_r3,power10_r4,power10_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers20
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
noncomputable def power13_r4 : Fin 16 → Fin 16 → CBox := ![power13_r4_0,power13_r4_1,power13_r4_2,power13_r4_3,power13_r4_4,power13_r4_5,power13_r4_6,power13_r4_7,power13_r4_8,power13_r4_9,power13_r4_10,power13_r4_11,power13_r4_12,power13_r4_13,power13_r4_14,power13_r4_15]
noncomputable def power13 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power13_r0,power13_r1,power13_r2,power13_r3,power13_r4,power13_r5]
noncomputable def power15_r0 : Fin 16 → Fin 16 → CBox := ![power15_r0_0,power15_r0_1,power15_r0_2,power15_r0_3,power15_r0_4,power15_r0_5,power15_r0_6,power15_r0_7,power15_r0_8,power15_r0_9,power15_r0_10,power15_r0_11,power15_r0_12,power15_r0_13,power15_r0_14,power15_r0_15]
noncomputable def power15 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power15_r0,power15_r1,power15_r2,power15_r3,power15_r4,power15_r5]
noncomputable def power18_r1 : Fin 16 → Fin 16 → CBox := ![power18_r1_0,power18_r1_1,power18_r1_2,power18_r1_3,power18_r1_4,power18_r1_5,power18_r1_6,power18_r1_7,power18_r1_8,power18_r1_9,power18_r1_10,power18_r1_11,power18_r1_12,power18_r1_13,power18_r1_14,power18_r1_15]
noncomputable def power18 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power18_r0,power18_r1,power18_r2,power18_r3,power18_r4,power18_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers30
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
noncomputable def power21_r3 : Fin 16 → Fin 16 → CBox := ![power21_r3_0,power21_r3_1,power21_r3_2,power21_r3_3,power21_r3_4,power21_r3_5,power21_r3_6,power21_r3_7,power21_r3_8,power21_r3_9,power21_r3_10,power21_r3_11,power21_r3_12,power21_r3_13,power21_r3_14,power21_r3_15]
noncomputable def power21 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power21_r0,power21_r1,power21_r2,power21_r3,power21_r4,power21_r5]
noncomputable def power24_r4 : Fin 16 → Fin 16 → CBox := ![power24_r4_0,power24_r4_1,power24_r4_2,power24_r4_3,power24_r4_4,power24_r4_5,power24_r4_6,power24_r4_7,power24_r4_8,power24_r4_9,power24_r4_10,power24_r4_11,power24_r4_12,power24_r4_13,power24_r4_14,power24_r4_15]
noncomputable def power24 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power24_r0,power24_r1,power24_r2,power24_r3,power24_r4,power24_r5]
noncomputable def power27_r5 : Fin 16 → Fin 16 → CBox := ![power27_r5_0,power27_r5_1,power27_r5_2,power27_r5_3,power27_r5_4,power27_r5_5,power27_r5_6,power27_r5_7,power27_r5_8,power27_r5_9,power27_r5_10,power27_r5_11,power27_r5_12,power27_r5_13,power27_r5_14,power27_r5_15]
noncomputable def power27 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power27_r0,power27_r1,power27_r2,power27_r3,power27_r4,power27_r5]
noncomputable def power29_r1 : Fin 16 → Fin 16 → CBox := ![power29_r1_0,power29_r1_1,power29_r1_2,power29_r1_3,power29_r1_4,power29_r1_5,power29_r1_6,power29_r1_7,power29_r1_8,power29_r1_9,power29_r1_10,power29_r1_11,power29_r1_12,power29_r1_13,power29_r1_14,power29_r1_15]
noncomputable def power29 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power29_r0,power29_r1,power29_r2,power29_r3,power29_r4,power29_r5]
end SharpPlanar.CachedData

end OAI
end

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
noncomputable def power32_r2 : Fin 16 → Fin 16 → CBox := ![power32_r2_0,power32_r2_1,power32_r2_2,power32_r2_3,power32_r2_4,power32_r2_5,power32_r2_6,power32_r2_7,power32_r2_8,power32_r2_9,power32_r2_10,power32_r2_11,power32_r2_12,power32_r2_13,power32_r2_14,power32_r2_15]
noncomputable def power32 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power32_r0,power32_r1,power32_r2,power32_r3,power32_r4,power32_r5]
noncomputable def power35_r3 : Fin 16 → Fin 16 → CBox := ![power35_r3_0,power35_r3_1,power35_r3_2,power35_r3_3,power35_r3_4,power35_r3_5,power35_r3_6,power35_r3_7,power35_r3_8,power35_r3_9,power35_r3_10,power35_r3_11,power35_r3_12,power35_r3_13,power35_r3_14,power35_r3_15]
noncomputable def power35 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power35_r0,power35_r1,power35_r2,power35_r3,power35_r4,power35_r5]
noncomputable def power38_r5 : Fin 16 → Fin 16 → CBox := ![power38_r5_0,power38_r5_1,power38_r5_2,power38_r5_3,power38_r5_4,power38_r5_5,power38_r5_6,power38_r5_7,power38_r5_8,power38_r5_9,power38_r5_10,power38_r5_11,power38_r5_12,power38_r5_13,power38_r5_14,power38_r5_15]
noncomputable def power38 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power38_r0,power38_r1,power38_r2,power38_r3,power38_r4,power38_r5]
noncomputable def power40_r0 : Fin 16 → Fin 16 → CBox := ![power40_r0_0,power40_r0_1,power40_r0_2,power40_r0_3,power40_r0_4,power40_r0_5,power40_r0_6,power40_r0_7,power40_r0_8,power40_r0_9,power40_r0_10,power40_r0_11,power40_r0_12,power40_r0_13,power40_r0_14,power40_r0_15]
noncomputable def power40 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power40_r0,power40_r1,power40_r2,power40_r3,power40_r4,power40_r5]
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
noncomputable def power43_r1 : Fin 16 → Fin 16 → CBox := ![power43_r1_0,power43_r1_1,power43_r1_2,power43_r1_3,power43_r1_4,power43_r1_5,power43_r1_6,power43_r1_7,power43_r1_8,power43_r1_9,power43_r1_10,power43_r1_11,power43_r1_12,power43_r1_13,power43_r1_14,power43_r1_15]
noncomputable def power43 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power43_r0,power43_r1,power43_r2,power43_r3,power43_r4,power43_r5]
noncomputable def power46_r3 : Fin 16 → Fin 16 → CBox := ![power46_r3_0,power46_r3_1,power46_r3_2,power46_r3_3,power46_r3_4,power46_r3_5,power46_r3_6,power46_r3_7,power46_r3_8,power46_r3_9,power46_r3_10,power46_r3_11,power46_r3_12,power46_r3_13,power46_r3_14,power46_r3_15]
noncomputable def power46 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power46_r0,power46_r1,power46_r2,power46_r3,power46_r4,power46_r5]
noncomputable def power49_r4 : Fin 16 → Fin 16 → CBox := ![power49_r4_0,power49_r4_1,power49_r4_2,power49_r4_3,power49_r4_4,power49_r4_5,power49_r4_6,power49_r4_7,power49_r4_8,power49_r4_9,power49_r4_10,power49_r4_11,power49_r4_12,power49_r4_13,power49_r4_14,power49_r4_15]
noncomputable def power49 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power49_r0,power49_r1,power49_r2,power49_r3,power49_r4,power49_r5]
end SharpPlanar.CachedData

end OAI
end

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
noncomputable def power54_r1 : Fin 16 → Fin 16 → CBox := ![power54_r1_0,power54_r1_1,power54_r1_2,power54_r1_3,power54_r1_4,power54_r1_5,power54_r1_6,power54_r1_7,power54_r1_8,power54_r1_9,power54_r1_10,power54_r1_11,power54_r1_12,power54_r1_13,power54_r1_14,power54_r1_15]
noncomputable def power54 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power54_r0,power54_r1,power54_r2,power54_r3,power54_r4,power54_r5]
noncomputable def power57_r2 : Fin 16 → Fin 16 → CBox := ![power57_r2_0,power57_r2_1,power57_r2_2,power57_r2_3,power57_r2_4,power57_r2_5,power57_r2_6,power57_r2_7,power57_r2_8,power57_r2_9,power57_r2_10,power57_r2_11,power57_r2_12,power57_r2_13,power57_r2_14,power57_r2_15]
noncomputable def power57 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power57_r0,power57_r1,power57_r2,power57_r3,power57_r4,power57_r5]
noncomputable def power60_r4 : Fin 16 → Fin 16 → CBox := ![power60_r4_0,power60_r4_1,power60_r4_2,power60_r4_3,power60_r4_4,power60_r4_5,power60_r4_6,power60_r4_7,power60_r4_8,power60_r4_9,power60_r4_10,power60_r4_11,power60_r4_12,power60_r4_13,power60_r4_14,power60_r4_15]
noncomputable def power60 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power60_r0,power60_r1,power60_r2,power60_r3,power60_r4,power60_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers70
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
noncomputable def power63_r5 : Fin 16 → Fin 16 → CBox := ![power63_r5_0,power63_r5_1,power63_r5_2,power63_r5_3,power63_r5_4,power63_r5_5,power63_r5_6,power63_r5_7,power63_r5_8,power63_r5_9,power63_r5_10,power63_r5_11,power63_r5_12,power63_r5_13,power63_r5_14,power63_r5_15]
noncomputable def power63 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power63_r0,power63_r1,power63_r2,power63_r3,power63_r4,power63_r5]
noncomputable def power65_r0 : Fin 16 → Fin 16 → CBox := ![power65_r0_0,power65_r0_1,power65_r0_2,power65_r0_3,power65_r0_4,power65_r0_5,power65_r0_6,power65_r0_7,power65_r0_8,power65_r0_9,power65_r0_10,power65_r0_11,power65_r0_12,power65_r0_13,power65_r0_14,power65_r0_15]
noncomputable def power65 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power65_r0,power65_r1,power65_r2,power65_r3,power65_r4,power65_r5]
noncomputable def power68_r2 : Fin 16 → Fin 16 → CBox := ![power68_r2_0,power68_r2_1,power68_r2_2,power68_r2_3,power68_r2_4,power68_r2_5,power68_r2_6,power68_r2_7,power68_r2_8,power68_r2_9,power68_r2_10,power68_r2_11,power68_r2_12,power68_r2_13,power68_r2_14,power68_r2_15]
noncomputable def power68 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power68_r0,power68_r1,power68_r2,power68_r3,power68_r4,power68_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers80
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
noncomputable def power71_r3 : Fin 16 → Fin 16 → CBox := ![power71_r3_0,power71_r3_1,power71_r3_2,power71_r3_3,power71_r3_4,power71_r3_5,power71_r3_6,power71_r3_7,power71_r3_8,power71_r3_9,power71_r3_10,power71_r3_11,power71_r3_12,power71_r3_13,power71_r3_14,power71_r3_15]
noncomputable def power71 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power71_r0,power71_r1,power71_r2,power71_r3,power71_r4,power71_r5]
noncomputable def power74_r4 : Fin 16 → Fin 16 → CBox := ![power74_r4_0,power74_r4_1,power74_r4_2,power74_r4_3,power74_r4_4,power74_r4_5,power74_r4_6,power74_r4_7,power74_r4_8,power74_r4_9,power74_r4_10,power74_r4_11,power74_r4_12,power74_r4_13,power74_r4_14,power74_r4_15]
noncomputable def power74 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power74_r0,power74_r1,power74_r2,power74_r3,power74_r4,power74_r5]
noncomputable def power76_r0 : Fin 16 → Fin 16 → CBox := ![power76_r0_0,power76_r0_1,power76_r0_2,power76_r0_3,power76_r0_4,power76_r0_5,power76_r0_6,power76_r0_7,power76_r0_8,power76_r0_9,power76_r0_10,power76_r0_11,power76_r0_12,power76_r0_13,power76_r0_14,power76_r0_15]
noncomputable def power76 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power76_r0,power76_r1,power76_r2,power76_r3,power76_r4,power76_r5]
noncomputable def power79_r1 : Fin 16 → Fin 16 → CBox := ![power79_r1_0,power79_r1_1,power79_r1_2,power79_r1_3,power79_r1_4,power79_r1_5,power79_r1_6,power79_r1_7,power79_r1_8,power79_r1_9,power79_r1_10,power79_r1_11,power79_r1_12,power79_r1_13,power79_r1_14,power79_r1_15]
noncomputable def power79 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power79_r0,power79_r1,power79_r2,power79_r3,power79_r4,power79_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Powers90
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
noncomputable def power85_r4 : Fin 16 → Fin 16 → CBox := ![power85_r4_0,power85_r4_1,power85_r4_2,power85_r4_3,power85_r4_4,power85_r4_5,power85_r4_6,power85_r4_7,power85_r4_8,power85_r4_9,power85_r4_10,power85_r4_11,power85_r4_12,power85_r4_13,power85_r4_14,power85_r4_15]
noncomputable def power85 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power85_r0,power85_r1,power85_r2,power85_r3,power85_r4,power85_r5]
noncomputable def power88_r5 : Fin 16 → Fin 16 → CBox := ![power88_r5_0,power88_r5_1,power88_r5_2,power88_r5_3,power88_r5_4,power88_r5_5,power88_r5_6,power88_r5_7,power88_r5_8,power88_r5_9,power88_r5_10,power88_r5_11,power88_r5_12,power88_r5_13,power88_r5_14,power88_r5_15]
noncomputable def power88 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power88_r0,power88_r1,power88_r2,power88_r3,power88_r4,power88_r5]
noncomputable def power90_r1 : Fin 16 → Fin 16 → CBox := ![power90_r1_0,power90_r1_1,power90_r1_2,power90_r1_3,power90_r1_4,power90_r1_5,power90_r1_6,power90_r1_7,power90_r1_8,power90_r1_9,power90_r1_10,power90_r1_11,power90_r1_12,power90_r1_13,power90_r1_14,power90_r1_15]
noncomputable def power90 : Fin 6 → Fin 16 → Fin 16 → CBox := ![power90_r0,power90_r1,power90_r2,power90_r3,power90_r4,power90_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns100
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
noncomputable def column100_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp4_1 j i k).mul (power100 j i k)
lemma column100_1_r0_0_eq : ∀ k : Fin 16, column100_1Expr 0 0 k = column100_1_r0_0 k := by decide +kernel
lemma column100_1_r0_1_eq : ∀ k : Fin 16, column100_1Expr 0 1 k = column100_1_r0_1 k := by decide +kernel
lemma column100_1_r0_2_eq : ∀ k : Fin 16, column100_1Expr 0 2 k = column100_1_r0_2 k := by decide +kernel
lemma column100_1_r0_3_eq : ∀ k : Fin 16, column100_1Expr 0 3 k = column100_1_r0_3 k := by decide +kernel
lemma column100_1_r0_4_eq : ∀ k : Fin 16, column100_1Expr 0 4 k = column100_1_r0_4 k := by decide +kernel
lemma column100_1_r0_5_eq : ∀ k : Fin 16, column100_1Expr 0 5 k = column100_1_r0_5 k := by decide +kernel
lemma column100_1_r0_6_eq : ∀ k : Fin 16, column100_1Expr 0 6 k = column100_1_r0_6 k := by decide +kernel
lemma column100_1_r0_7_eq : ∀ k : Fin 16, column100_1Expr 0 7 k = column100_1_r0_7 k := by decide +kernel
lemma column100_1_r0_8_eq : ∀ k : Fin 16, column100_1Expr 0 8 k = column100_1_r0_8 k := by decide +kernel
lemma column100_1_r0_9_eq : ∀ k : Fin 16, column100_1Expr 0 9 k = column100_1_r0_9 k := by decide +kernel
lemma column100_1_r0_10_eq : ∀ k : Fin 16, column100_1Expr 0 10 k = column100_1_r0_10 k := by decide +kernel
lemma column100_1_r0_11_eq : ∀ k : Fin 16, column100_1Expr 0 11 k = column100_1_r0_11 k := by decide +kernel
lemma column100_1_r0_12_eq : ∀ k : Fin 16, column100_1Expr 0 12 k = column100_1_r0_12 k := by decide +kernel
lemma column100_1_r0_13_eq : ∀ k : Fin 16, column100_1Expr 0 13 k = column100_1_r0_13 k := by decide +kernel
lemma column100_1_r0_14_eq : ∀ k : Fin 16, column100_1Expr 0 14 k = column100_1_r0_14 k := by decide +kernel
lemma column100_1_r0_15_eq : ∀ k : Fin 16, column100_1Expr 0 15 k = column100_1_r0_15 k := by decide +kernel
lemma column100_1_r0_eq (i k : Fin 16) : column100_1Expr 0 i k = column100_1_r0 i k := by
  fin_cases i
  · exact column100_1_r0_0_eq k
  · exact column100_1_r0_1_eq k
  · exact column100_1_r0_2_eq k
  · exact column100_1_r0_3_eq k
  · exact column100_1_r0_4_eq k
  · exact column100_1_r0_5_eq k
  · exact column100_1_r0_6_eq k
  · exact column100_1_r0_7_eq k
  · exact column100_1_r0_8_eq k
  · exact column100_1_r0_9_eq k
  · exact column100_1_r0_10_eq k
  · exact column100_1_r0_11_eq k
  · exact column100_1_r0_12_eq k
  · exact column100_1_r0_13_eq k
  · exact column100_1_r0_14_eq k
  · exact column100_1_r0_15_eq k
lemma column100_1_r1_0_eq : ∀ k : Fin 16, column100_1Expr 1 0 k = column100_1_r1_0 k := by decide +kernel
lemma column100_1_r1_1_eq : ∀ k : Fin 16, column100_1Expr 1 1 k = column100_1_r1_1 k := by decide +kernel
lemma column100_1_r1_2_eq : ∀ k : Fin 16, column100_1Expr 1 2 k = column100_1_r1_2 k := by decide +kernel
lemma column100_1_r1_3_eq : ∀ k : Fin 16, column100_1Expr 1 3 k = column100_1_r1_3 k := by decide +kernel
lemma column100_1_r1_4_eq : ∀ k : Fin 16, column100_1Expr 1 4 k = column100_1_r1_4 k := by decide +kernel
lemma column100_1_r1_5_eq : ∀ k : Fin 16, column100_1Expr 1 5 k = column100_1_r1_5 k := by decide +kernel
lemma column100_1_r1_6_eq : ∀ k : Fin 16, column100_1Expr 1 6 k = column100_1_r1_6 k := by decide +kernel
lemma column100_1_r1_7_eq : ∀ k : Fin 16, column100_1Expr 1 7 k = column100_1_r1_7 k := by decide +kernel
lemma column100_1_r1_8_eq : ∀ k : Fin 16, column100_1Expr 1 8 k = column100_1_r1_8 k := by decide +kernel
lemma column100_1_r1_9_eq : ∀ k : Fin 16, column100_1Expr 1 9 k = column100_1_r1_9 k := by decide +kernel
lemma column100_1_r1_10_eq : ∀ k : Fin 16, column100_1Expr 1 10 k = column100_1_r1_10 k := by decide +kernel
lemma column100_1_r1_11_eq : ∀ k : Fin 16, column100_1Expr 1 11 k = column100_1_r1_11 k := by decide +kernel
lemma column100_1_r1_12_eq : ∀ k : Fin 16, column100_1Expr 1 12 k = column100_1_r1_12 k := by decide +kernel
lemma column100_1_r1_13_eq : ∀ k : Fin 16, column100_1Expr 1 13 k = column100_1_r1_13 k := by decide +kernel
lemma column100_1_r1_14_eq : ∀ k : Fin 16, column100_1Expr 1 14 k = column100_1_r1_14 k := by decide +kernel
lemma column100_1_r1_15_eq : ∀ k : Fin 16, column100_1Expr 1 15 k = column100_1_r1_15 k := by decide +kernel
lemma column100_1_r1_eq (i k : Fin 16) : column100_1Expr 1 i k = column100_1_r1 i k := by
  fin_cases i
  · exact column100_1_r1_0_eq k
  · exact column100_1_r1_1_eq k
  · exact column100_1_r1_2_eq k
  · exact column100_1_r1_3_eq k
  · exact column100_1_r1_4_eq k
  · exact column100_1_r1_5_eq k
  · exact column100_1_r1_6_eq k
  · exact column100_1_r1_7_eq k
  · exact column100_1_r1_8_eq k
  · exact column100_1_r1_9_eq k
  · exact column100_1_r1_10_eq k
  · exact column100_1_r1_11_eq k
  · exact column100_1_r1_12_eq k
  · exact column100_1_r1_13_eq k
  · exact column100_1_r1_14_eq k
  · exact column100_1_r1_15_eq k
lemma column100_1_r2_0_eq : ∀ k : Fin 16, column100_1Expr 2 0 k = column100_1_r2_0 k := by decide +kernel
lemma column100_1_r2_1_eq : ∀ k : Fin 16, column100_1Expr 2 1 k = column100_1_r2_1 k := by decide +kernel
lemma column100_1_r2_2_eq : ∀ k : Fin 16, column100_1Expr 2 2 k = column100_1_r2_2 k := by decide +kernel
lemma column100_1_r2_3_eq : ∀ k : Fin 16, column100_1Expr 2 3 k = column100_1_r2_3 k := by decide +kernel
lemma column100_1_r2_4_eq : ∀ k : Fin 16, column100_1Expr 2 4 k = column100_1_r2_4 k := by decide +kernel
lemma column100_1_r2_5_eq : ∀ k : Fin 16, column100_1Expr 2 5 k = column100_1_r2_5 k := by decide +kernel
lemma column100_1_r2_6_eq : ∀ k : Fin 16, column100_1Expr 2 6 k = column100_1_r2_6 k := by decide +kernel
lemma column100_1_r2_7_eq : ∀ k : Fin 16, column100_1Expr 2 7 k = column100_1_r2_7 k := by decide +kernel
lemma column100_1_r2_8_eq : ∀ k : Fin 16, column100_1Expr 2 8 k = column100_1_r2_8 k := by decide +kernel
lemma column100_1_r2_9_eq : ∀ k : Fin 16, column100_1Expr 2 9 k = column100_1_r2_9 k := by decide +kernel
lemma column100_1_r2_10_eq : ∀ k : Fin 16, column100_1Expr 2 10 k = column100_1_r2_10 k := by decide +kernel
lemma column100_1_r2_11_eq : ∀ k : Fin 16, column100_1Expr 2 11 k = column100_1_r2_11 k := by decide +kernel
lemma column100_1_r2_12_eq : ∀ k : Fin 16, column100_1Expr 2 12 k = column100_1_r2_12 k := by decide +kernel
lemma column100_1_r2_13_eq : ∀ k : Fin 16, column100_1Expr 2 13 k = column100_1_r2_13 k := by decide +kernel
lemma column100_1_r2_14_eq : ∀ k : Fin 16, column100_1Expr 2 14 k = column100_1_r2_14 k := by decide +kernel
lemma column100_1_r2_15_eq : ∀ k : Fin 16, column100_1Expr 2 15 k = column100_1_r2_15 k := by decide +kernel
lemma column100_1_r2_eq (i k : Fin 16) : column100_1Expr 2 i k = column100_1_r2 i k := by
  fin_cases i
  · exact column100_1_r2_0_eq k
  · exact column100_1_r2_1_eq k
  · exact column100_1_r2_2_eq k
  · exact column100_1_r2_3_eq k
  · exact column100_1_r2_4_eq k
  · exact column100_1_r2_5_eq k
  · exact column100_1_r2_6_eq k
  · exact column100_1_r2_7_eq k
  · exact column100_1_r2_8_eq k
  · exact column100_1_r2_9_eq k
  · exact column100_1_r2_10_eq k
  · exact column100_1_r2_11_eq k
  · exact column100_1_r2_12_eq k
  · exact column100_1_r2_13_eq k
  · exact column100_1_r2_14_eq k
  · exact column100_1_r2_15_eq k
lemma column100_1_r3_0_eq : ∀ k : Fin 16, column100_1Expr 3 0 k = column100_1_r3_0 k := by decide +kernel
lemma column100_1_r3_1_eq : ∀ k : Fin 16, column100_1Expr 3 1 k = column100_1_r3_1 k := by decide +kernel
lemma column100_1_r3_2_eq : ∀ k : Fin 16, column100_1Expr 3 2 k = column100_1_r3_2 k := by decide +kernel
lemma column100_1_r3_3_eq : ∀ k : Fin 16, column100_1Expr 3 3 k = column100_1_r3_3 k := by decide +kernel
lemma column100_1_r3_4_eq : ∀ k : Fin 16, column100_1Expr 3 4 k = column100_1_r3_4 k := by decide +kernel
lemma column100_1_r3_5_eq : ∀ k : Fin 16, column100_1Expr 3 5 k = column100_1_r3_5 k := by decide +kernel
lemma column100_1_r3_6_eq : ∀ k : Fin 16, column100_1Expr 3 6 k = column100_1_r3_6 k := by decide +kernel
lemma column100_1_r3_7_eq : ∀ k : Fin 16, column100_1Expr 3 7 k = column100_1_r3_7 k := by decide +kernel
lemma column100_1_r3_8_eq : ∀ k : Fin 16, column100_1Expr 3 8 k = column100_1_r3_8 k := by decide +kernel
lemma column100_1_r3_9_eq : ∀ k : Fin 16, column100_1Expr 3 9 k = column100_1_r3_9 k := by decide +kernel
lemma column100_1_r3_10_eq : ∀ k : Fin 16, column100_1Expr 3 10 k = column100_1_r3_10 k := by decide +kernel
lemma column100_1_r3_11_eq : ∀ k : Fin 16, column100_1Expr 3 11 k = column100_1_r3_11 k := by decide +kernel
lemma column100_1_r3_12_eq : ∀ k : Fin 16, column100_1Expr 3 12 k = column100_1_r3_12 k := by decide +kernel
lemma column100_1_r3_13_eq : ∀ k : Fin 16, column100_1Expr 3 13 k = column100_1_r3_13 k := by decide +kernel
lemma column100_1_r3_14_eq : ∀ k : Fin 16, column100_1Expr 3 14 k = column100_1_r3_14 k := by decide +kernel
lemma column100_1_r3_15_eq : ∀ k : Fin 16, column100_1Expr 3 15 k = column100_1_r3_15 k := by decide +kernel
lemma column100_1_r3_eq (i k : Fin 16) : column100_1Expr 3 i k = column100_1_r3 i k := by
  fin_cases i
  · exact column100_1_r3_0_eq k
  · exact column100_1_r3_1_eq k
  · exact column100_1_r3_2_eq k
  · exact column100_1_r3_3_eq k
  · exact column100_1_r3_4_eq k
  · exact column100_1_r3_5_eq k
  · exact column100_1_r3_6_eq k
  · exact column100_1_r3_7_eq k
  · exact column100_1_r3_8_eq k
  · exact column100_1_r3_9_eq k
  · exact column100_1_r3_10_eq k
  · exact column100_1_r3_11_eq k
  · exact column100_1_r3_12_eq k
  · exact column100_1_r3_13_eq k
  · exact column100_1_r3_14_eq k
  · exact column100_1_r3_15_eq k
lemma column100_1_r4_0_eq : ∀ k : Fin 16, column100_1Expr 4 0 k = column100_1_r4_0 k := by decide +kernel
lemma column100_1_r4_1_eq : ∀ k : Fin 16, column100_1Expr 4 1 k = column100_1_r4_1 k := by decide +kernel
lemma column100_1_r4_2_eq : ∀ k : Fin 16, column100_1Expr 4 2 k = column100_1_r4_2 k := by decide +kernel
lemma column100_1_r4_3_eq : ∀ k : Fin 16, column100_1Expr 4 3 k = column100_1_r4_3 k := by decide +kernel
lemma column100_1_r4_4_eq : ∀ k : Fin 16, column100_1Expr 4 4 k = column100_1_r4_4 k := by decide +kernel
lemma column100_1_r4_5_eq : ∀ k : Fin 16, column100_1Expr 4 5 k = column100_1_r4_5 k := by decide +kernel
lemma column100_1_r4_6_eq : ∀ k : Fin 16, column100_1Expr 4 6 k = column100_1_r4_6 k := by decide +kernel
lemma column100_1_r4_7_eq : ∀ k : Fin 16, column100_1Expr 4 7 k = column100_1_r4_7 k := by decide +kernel
lemma column100_1_r4_8_eq : ∀ k : Fin 16, column100_1Expr 4 8 k = column100_1_r4_8 k := by decide +kernel
lemma column100_1_r4_9_eq : ∀ k : Fin 16, column100_1Expr 4 9 k = column100_1_r4_9 k := by decide +kernel
lemma column100_1_r4_10_eq : ∀ k : Fin 16, column100_1Expr 4 10 k = column100_1_r4_10 k := by decide +kernel
lemma column100_1_r4_11_eq : ∀ k : Fin 16, column100_1Expr 4 11 k = column100_1_r4_11 k := by decide +kernel
lemma column100_1_r4_12_eq : ∀ k : Fin 16, column100_1Expr 4 12 k = column100_1_r4_12 k := by decide +kernel
lemma column100_1_r4_13_eq : ∀ k : Fin 16, column100_1Expr 4 13 k = column100_1_r4_13 k := by decide +kernel
lemma column100_1_r4_14_eq : ∀ k : Fin 16, column100_1Expr 4 14 k = column100_1_r4_14 k := by decide +kernel
lemma column100_1_r4_15_eq : ∀ k : Fin 16, column100_1Expr 4 15 k = column100_1_r4_15 k := by decide +kernel
lemma column100_1_r4_eq (i k : Fin 16) : column100_1Expr 4 i k = column100_1_r4 i k := by
  fin_cases i
  · exact column100_1_r4_0_eq k
  · exact column100_1_r4_1_eq k
  · exact column100_1_r4_2_eq k
  · exact column100_1_r4_3_eq k
  · exact column100_1_r4_4_eq k
  · exact column100_1_r4_5_eq k
  · exact column100_1_r4_6_eq k
  · exact column100_1_r4_7_eq k
  · exact column100_1_r4_8_eq k
  · exact column100_1_r4_9_eq k
  · exact column100_1_r4_10_eq k
  · exact column100_1_r4_11_eq k
  · exact column100_1_r4_12_eq k
  · exact column100_1_r4_13_eq k
  · exact column100_1_r4_14_eq k
  · exact column100_1_r4_15_eq k
lemma column100_1_r5_0_eq : ∀ k : Fin 16, column100_1Expr 5 0 k = column100_1_r5_0 k := by decide +kernel
lemma column100_1_r5_1_eq : ∀ k : Fin 16, column100_1Expr 5 1 k = column100_1_r5_1 k := by decide +kernel
lemma column100_1_r5_2_eq : ∀ k : Fin 16, column100_1Expr 5 2 k = column100_1_r5_2 k := by decide +kernel
lemma column100_1_r5_3_eq : ∀ k : Fin 16, column100_1Expr 5 3 k = column100_1_r5_3 k := by decide +kernel
lemma column100_1_r5_4_eq : ∀ k : Fin 16, column100_1Expr 5 4 k = column100_1_r5_4 k := by decide +kernel
lemma column100_1_r5_5_eq : ∀ k : Fin 16, column100_1Expr 5 5 k = column100_1_r5_5 k := by decide +kernel
lemma column100_1_r5_6_eq : ∀ k : Fin 16, column100_1Expr 5 6 k = column100_1_r5_6 k := by decide +kernel
lemma column100_1_r5_7_eq : ∀ k : Fin 16, column100_1Expr 5 7 k = column100_1_r5_7 k := by decide +kernel
lemma column100_1_r5_8_eq : ∀ k : Fin 16, column100_1Expr 5 8 k = column100_1_r5_8 k := by decide +kernel
lemma column100_1_r5_9_eq : ∀ k : Fin 16, column100_1Expr 5 9 k = column100_1_r5_9 k := by decide +kernel
lemma column100_1_r5_10_eq : ∀ k : Fin 16, column100_1Expr 5 10 k = column100_1_r5_10 k := by decide +kernel
lemma column100_1_r5_11_eq : ∀ k : Fin 16, column100_1Expr 5 11 k = column100_1_r5_11 k := by decide +kernel
lemma column100_1_r5_12_eq : ∀ k : Fin 16, column100_1Expr 5 12 k = column100_1_r5_12 k := by decide +kernel
lemma column100_1_r5_13_eq : ∀ k : Fin 16, column100_1Expr 5 13 k = column100_1_r5_13 k := by decide +kernel
lemma column100_1_r5_14_eq : ∀ k : Fin 16, column100_1Expr 5 14 k = column100_1_r5_14 k := by decide +kernel
lemma column100_1_r5_15_eq : ∀ k : Fin 16, column100_1Expr 5 15 k = column100_1_r5_15 k := by decide +kernel
lemma column100_1_r5_eq (i k : Fin 16) : column100_1Expr 5 i k = column100_1_r5 i k := by
  fin_cases i
  · exact column100_1_r5_0_eq k
  · exact column100_1_r5_1_eq k
  · exact column100_1_r5_2_eq k
  · exact column100_1_r5_3_eq k
  · exact column100_1_r5_4_eq k
  · exact column100_1_r5_5_eq k
  · exact column100_1_r5_6_eq k
  · exact column100_1_r5_7_eq k
  · exact column100_1_r5_8_eq k
  · exact column100_1_r5_9_eq k
  · exact column100_1_r5_10_eq k
  · exact column100_1_r5_11_eq k
  · exact column100_1_r5_12_eq k
  · exact column100_1_r5_13_eq k
  · exact column100_1_r5_14_eq k
  · exact column100_1_r5_15_eq k
lemma column100_1_eq (j : Fin 6) (i k : Fin 16) : column100_1Expr j i k = column100_1 j i k := by
  fin_cases j
  · exact column100_1_r0_eq i k
  · exact column100_1_r1_eq i k
  · exact column100_1_r2_eq i k
  · exact column100_1_r3_eq i k
  · exact column100_1_r4_eq i k
  · exact column100_1_r5_eq i k
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns20
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
noncomputable def column12_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_0 j i k).mul (power12 j i k)
noncomputable def column12_1Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp0_1 j i k).mul (power12 j i k)
noncomputable def column13_0Expr (j : Fin 6) (i k : Fin 16) : CBox := (amp1_0 j i k).mul (power13 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers10
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
noncomputable def transStep_r4 : Fin 16 → Fin 16 → CBox := ![transStep_r4_0,transStep_r4_1,transStep_r4_2,transStep_r4_3,transStep_r4_4,transStep_r4_5,transStep_r4_6,transStep_r4_7,transStep_r4_8,transStep_r4_9,transStep_r4_10,transStep_r4_11,transStep_r4_12,transStep_r4_13,transStep_r4_14,transStep_r4_15]
noncomputable def transStep : Fin 6 → Fin 16 → Fin 16 → CBox := ![transStep_r0,transStep_r1,transStep_r2,transStep_r3,transStep_r4,transStep_r5]
noncomputable def trans0 (_j : Fin 6) (_i _k : Fin 16) : CBox := CBox.rat 1 1 0 1
noncomputable def trans1Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans0 j i k).mul (transStep j i k)
lemma trans1_r0_0_eq : ∀ k : Fin 16, trans1Expr 0 0 k = trans1_r0_0 k := by decide +kernel
lemma trans1_r0_1_eq : ∀ k : Fin 16, trans1Expr 0 1 k = trans1_r0_1 k := by decide +kernel
lemma trans1_r0_2_eq : ∀ k : Fin 16, trans1Expr 0 2 k = trans1_r0_2 k := by decide +kernel
lemma trans1_r0_3_eq : ∀ k : Fin 16, trans1Expr 0 3 k = trans1_r0_3 k := by decide +kernel
lemma trans1_r0_4_eq : ∀ k : Fin 16, trans1Expr 0 4 k = trans1_r0_4 k := by decide +kernel
lemma trans1_r0_5_eq : ∀ k : Fin 16, trans1Expr 0 5 k = trans1_r0_5 k := by decide +kernel
lemma trans1_r0_6_eq : ∀ k : Fin 16, trans1Expr 0 6 k = trans1_r0_6 k := by decide +kernel
lemma trans1_r0_7_eq : ∀ k : Fin 16, trans1Expr 0 7 k = trans1_r0_7 k := by decide +kernel
lemma trans1_r0_8_eq : ∀ k : Fin 16, trans1Expr 0 8 k = trans1_r0_8 k := by decide +kernel
lemma trans1_r0_9_eq : ∀ k : Fin 16, trans1Expr 0 9 k = trans1_r0_9 k := by decide +kernel
lemma trans1_r0_10_eq : ∀ k : Fin 16, trans1Expr 0 10 k = trans1_r0_10 k := by decide +kernel
lemma trans1_r0_11_eq : ∀ k : Fin 16, trans1Expr 0 11 k = trans1_r0_11 k := by decide +kernel
lemma trans1_r0_12_eq : ∀ k : Fin 16, trans1Expr 0 12 k = trans1_r0_12 k := by decide +kernel
lemma trans1_r0_13_eq : ∀ k : Fin 16, trans1Expr 0 13 k = trans1_r0_13 k := by decide +kernel
lemma trans1_r0_14_eq : ∀ k : Fin 16, trans1Expr 0 14 k = trans1_r0_14 k := by decide +kernel
lemma trans1_r0_15_eq : ∀ k : Fin 16, trans1Expr 0 15 k = trans1_r0_15 k := by decide +kernel
noncomputable def trans1_r0 : Fin 16 → Fin 16 → CBox := ![trans1_r0_0,trans1_r0_1,trans1_r0_2,trans1_r0_3,trans1_r0_4,trans1_r0_5,trans1_r0_6,trans1_r0_7,trans1_r0_8,trans1_r0_9,trans1_r0_10,trans1_r0_11,trans1_r0_12,trans1_r0_13,trans1_r0_14,trans1_r0_15]
lemma trans1_r0_eq (i k : Fin 16) : trans1Expr 0 i k = trans1_r0 i k := by
  fin_cases i
  · exact trans1_r0_0_eq k
  · exact trans1_r0_1_eq k
  · exact trans1_r0_2_eq k
  · exact trans1_r0_3_eq k
  · exact trans1_r0_4_eq k
  · exact trans1_r0_5_eq k
  · exact trans1_r0_6_eq k
  · exact trans1_r0_7_eq k
  · exact trans1_r0_8_eq k
  · exact trans1_r0_9_eq k
  · exact trans1_r0_10_eq k
  · exact trans1_r0_11_eq k
  · exact trans1_r0_12_eq k
  · exact trans1_r0_13_eq k
  · exact trans1_r0_14_eq k
  · exact trans1_r0_15_eq k
lemma trans1_r1_0_eq : ∀ k : Fin 16, trans1Expr 1 0 k = trans1_r1_0 k := by decide +kernel
lemma trans1_r1_1_eq : ∀ k : Fin 16, trans1Expr 1 1 k = trans1_r1_1 k := by decide +kernel
lemma trans1_r1_2_eq : ∀ k : Fin 16, trans1Expr 1 2 k = trans1_r1_2 k := by decide +kernel
lemma trans1_r1_3_eq : ∀ k : Fin 16, trans1Expr 1 3 k = trans1_r1_3 k := by decide +kernel
lemma trans1_r1_4_eq : ∀ k : Fin 16, trans1Expr 1 4 k = trans1_r1_4 k := by decide +kernel
lemma trans1_r1_5_eq : ∀ k : Fin 16, trans1Expr 1 5 k = trans1_r1_5 k := by decide +kernel
lemma trans1_r1_6_eq : ∀ k : Fin 16, trans1Expr 1 6 k = trans1_r1_6 k := by decide +kernel
lemma trans1_r1_7_eq : ∀ k : Fin 16, trans1Expr 1 7 k = trans1_r1_7 k := by decide +kernel
lemma trans1_r1_8_eq : ∀ k : Fin 16, trans1Expr 1 8 k = trans1_r1_8 k := by decide +kernel
lemma trans1_r1_9_eq : ∀ k : Fin 16, trans1Expr 1 9 k = trans1_r1_9 k := by decide +kernel
lemma trans1_r1_10_eq : ∀ k : Fin 16, trans1Expr 1 10 k = trans1_r1_10 k := by decide +kernel
lemma trans1_r1_11_eq : ∀ k : Fin 16, trans1Expr 1 11 k = trans1_r1_11 k := by decide +kernel
lemma trans1_r1_12_eq : ∀ k : Fin 16, trans1Expr 1 12 k = trans1_r1_12 k := by decide +kernel
lemma trans1_r1_13_eq : ∀ k : Fin 16, trans1Expr 1 13 k = trans1_r1_13 k := by decide +kernel
lemma trans1_r1_14_eq : ∀ k : Fin 16, trans1Expr 1 14 k = trans1_r1_14 k := by decide +kernel
lemma trans1_r1_15_eq : ∀ k : Fin 16, trans1Expr 1 15 k = trans1_r1_15 k := by decide +kernel
lemma trans1_r1_eq (i k : Fin 16) : trans1Expr 1 i k = trans1_r1 i k := by
  fin_cases i
  · exact trans1_r1_0_eq k
  · exact trans1_r1_1_eq k
  · exact trans1_r1_2_eq k
  · exact trans1_r1_3_eq k
  · exact trans1_r1_4_eq k
  · exact trans1_r1_5_eq k
  · exact trans1_r1_6_eq k
  · exact trans1_r1_7_eq k
  · exact trans1_r1_8_eq k
  · exact trans1_r1_9_eq k
  · exact trans1_r1_10_eq k
  · exact trans1_r1_11_eq k
  · exact trans1_r1_12_eq k
  · exact trans1_r1_13_eq k
  · exact trans1_r1_14_eq k
  · exact trans1_r1_15_eq k
lemma trans1_r2_0_eq : ∀ k : Fin 16, trans1Expr 2 0 k = trans1_r2_0 k := by decide +kernel
lemma trans1_r2_1_eq : ∀ k : Fin 16, trans1Expr 2 1 k = trans1_r2_1 k := by decide +kernel
lemma trans1_r2_2_eq : ∀ k : Fin 16, trans1Expr 2 2 k = trans1_r2_2 k := by decide +kernel
lemma trans1_r2_3_eq : ∀ k : Fin 16, trans1Expr 2 3 k = trans1_r2_3 k := by decide +kernel
lemma trans1_r2_4_eq : ∀ k : Fin 16, trans1Expr 2 4 k = trans1_r2_4 k := by decide +kernel
lemma trans1_r2_5_eq : ∀ k : Fin 16, trans1Expr 2 5 k = trans1_r2_5 k := by decide +kernel
lemma trans1_r2_6_eq : ∀ k : Fin 16, trans1Expr 2 6 k = trans1_r2_6 k := by decide +kernel
lemma trans1_r2_7_eq : ∀ k : Fin 16, trans1Expr 2 7 k = trans1_r2_7 k := by decide +kernel
lemma trans1_r2_8_eq : ∀ k : Fin 16, trans1Expr 2 8 k = trans1_r2_8 k := by decide +kernel
lemma trans1_r2_9_eq : ∀ k : Fin 16, trans1Expr 2 9 k = trans1_r2_9 k := by decide +kernel
lemma trans1_r2_10_eq : ∀ k : Fin 16, trans1Expr 2 10 k = trans1_r2_10 k := by decide +kernel
lemma trans1_r2_11_eq : ∀ k : Fin 16, trans1Expr 2 11 k = trans1_r2_11 k := by decide +kernel
lemma trans1_r2_12_eq : ∀ k : Fin 16, trans1Expr 2 12 k = trans1_r2_12 k := by decide +kernel
lemma trans1_r2_13_eq : ∀ k : Fin 16, trans1Expr 2 13 k = trans1_r2_13 k := by decide +kernel
lemma trans1_r2_14_eq : ∀ k : Fin 16, trans1Expr 2 14 k = trans1_r2_14 k := by decide +kernel
lemma trans1_r2_15_eq : ∀ k : Fin 16, trans1Expr 2 15 k = trans1_r2_15 k := by decide +kernel
lemma trans1_r2_eq (i k : Fin 16) : trans1Expr 2 i k = trans1_r2 i k := by
  fin_cases i
  · exact trans1_r2_0_eq k
  · exact trans1_r2_1_eq k
  · exact trans1_r2_2_eq k
  · exact trans1_r2_3_eq k
  · exact trans1_r2_4_eq k
  · exact trans1_r2_5_eq k
  · exact trans1_r2_6_eq k
  · exact trans1_r2_7_eq k
  · exact trans1_r2_8_eq k
  · exact trans1_r2_9_eq k
  · exact trans1_r2_10_eq k
  · exact trans1_r2_11_eq k
  · exact trans1_r2_12_eq k
  · exact trans1_r2_13_eq k
  · exact trans1_r2_14_eq k
  · exact trans1_r2_15_eq k
lemma trans1_r3_0_eq : ∀ k : Fin 16, trans1Expr 3 0 k = trans1_r3_0 k := by decide +kernel
lemma trans1_r3_1_eq : ∀ k : Fin 16, trans1Expr 3 1 k = trans1_r3_1 k := by decide +kernel
lemma trans1_r3_2_eq : ∀ k : Fin 16, trans1Expr 3 2 k = trans1_r3_2 k := by decide +kernel
lemma trans1_r3_3_eq : ∀ k : Fin 16, trans1Expr 3 3 k = trans1_r3_3 k := by decide +kernel
lemma trans1_r3_4_eq : ∀ k : Fin 16, trans1Expr 3 4 k = trans1_r3_4 k := by decide +kernel
lemma trans1_r3_5_eq : ∀ k : Fin 16, trans1Expr 3 5 k = trans1_r3_5 k := by decide +kernel
lemma trans1_r3_6_eq : ∀ k : Fin 16, trans1Expr 3 6 k = trans1_r3_6 k := by decide +kernel
lemma trans1_r3_7_eq : ∀ k : Fin 16, trans1Expr 3 7 k = trans1_r3_7 k := by decide +kernel
lemma trans1_r3_8_eq : ∀ k : Fin 16, trans1Expr 3 8 k = trans1_r3_8 k := by decide +kernel
lemma trans1_r3_9_eq : ∀ k : Fin 16, trans1Expr 3 9 k = trans1_r3_9 k := by decide +kernel
lemma trans1_r3_10_eq : ∀ k : Fin 16, trans1Expr 3 10 k = trans1_r3_10 k := by decide +kernel
lemma trans1_r3_11_eq : ∀ k : Fin 16, trans1Expr 3 11 k = trans1_r3_11 k := by decide +kernel
lemma trans1_r3_12_eq : ∀ k : Fin 16, trans1Expr 3 12 k = trans1_r3_12 k := by decide +kernel
lemma trans1_r3_13_eq : ∀ k : Fin 16, trans1Expr 3 13 k = trans1_r3_13 k := by decide +kernel
lemma trans1_r3_14_eq : ∀ k : Fin 16, trans1Expr 3 14 k = trans1_r3_14 k := by decide +kernel
lemma trans1_r3_15_eq : ∀ k : Fin 16, trans1Expr 3 15 k = trans1_r3_15 k := by decide +kernel
lemma trans1_r3_eq (i k : Fin 16) : trans1Expr 3 i k = trans1_r3 i k := by
  fin_cases i
  · exact trans1_r3_0_eq k
  · exact trans1_r3_1_eq k
  · exact trans1_r3_2_eq k
  · exact trans1_r3_3_eq k
  · exact trans1_r3_4_eq k
  · exact trans1_r3_5_eq k
  · exact trans1_r3_6_eq k
  · exact trans1_r3_7_eq k
  · exact trans1_r3_8_eq k
  · exact trans1_r3_9_eq k
  · exact trans1_r3_10_eq k
  · exact trans1_r3_11_eq k
  · exact trans1_r3_12_eq k
  · exact trans1_r3_13_eq k
  · exact trans1_r3_14_eq k
  · exact trans1_r3_15_eq k
lemma trans1_r4_0_eq : ∀ k : Fin 16, trans1Expr 4 0 k = trans1_r4_0 k := by decide +kernel
lemma trans1_r4_1_eq : ∀ k : Fin 16, trans1Expr 4 1 k = trans1_r4_1 k := by decide +kernel
lemma trans1_r4_2_eq : ∀ k : Fin 16, trans1Expr 4 2 k = trans1_r4_2 k := by decide +kernel
lemma trans1_r4_3_eq : ∀ k : Fin 16, trans1Expr 4 3 k = trans1_r4_3 k := by decide +kernel
lemma trans1_r4_4_eq : ∀ k : Fin 16, trans1Expr 4 4 k = trans1_r4_4 k := by decide +kernel
lemma trans1_r4_5_eq : ∀ k : Fin 16, trans1Expr 4 5 k = trans1_r4_5 k := by decide +kernel
lemma trans1_r4_6_eq : ∀ k : Fin 16, trans1Expr 4 6 k = trans1_r4_6 k := by decide +kernel
lemma trans1_r4_7_eq : ∀ k : Fin 16, trans1Expr 4 7 k = trans1_r4_7 k := by decide +kernel
lemma trans1_r4_8_eq : ∀ k : Fin 16, trans1Expr 4 8 k = trans1_r4_8 k := by decide +kernel
lemma trans1_r4_9_eq : ∀ k : Fin 16, trans1Expr 4 9 k = trans1_r4_9 k := by decide +kernel
lemma trans1_r4_10_eq : ∀ k : Fin 16, trans1Expr 4 10 k = trans1_r4_10 k := by decide +kernel
lemma trans1_r4_11_eq : ∀ k : Fin 16, trans1Expr 4 11 k = trans1_r4_11 k := by decide +kernel
lemma trans1_r4_12_eq : ∀ k : Fin 16, trans1Expr 4 12 k = trans1_r4_12 k := by decide +kernel
lemma trans1_r4_13_eq : ∀ k : Fin 16, trans1Expr 4 13 k = trans1_r4_13 k := by decide +kernel
lemma trans1_r4_14_eq : ∀ k : Fin 16, trans1Expr 4 14 k = trans1_r4_14 k := by decide +kernel
lemma trans1_r4_15_eq : ∀ k : Fin 16, trans1Expr 4 15 k = trans1_r4_15 k := by decide +kernel
lemma trans1_r4_eq (i k : Fin 16) : trans1Expr 4 i k = trans1_r4 i k := by
  fin_cases i
  · exact trans1_r4_0_eq k
  · exact trans1_r4_1_eq k
  · exact trans1_r4_2_eq k
  · exact trans1_r4_3_eq k
  · exact trans1_r4_4_eq k
  · exact trans1_r4_5_eq k
  · exact trans1_r4_6_eq k
  · exact trans1_r4_7_eq k
  · exact trans1_r4_8_eq k
  · exact trans1_r4_9_eq k
  · exact trans1_r4_10_eq k
  · exact trans1_r4_11_eq k
  · exact trans1_r4_12_eq k
  · exact trans1_r4_13_eq k
  · exact trans1_r4_14_eq k
  · exact trans1_r4_15_eq k
lemma trans1_r5_0_eq : ∀ k : Fin 16, trans1Expr 5 0 k = trans1_r5_0 k := by decide +kernel
lemma trans1_r5_1_eq : ∀ k : Fin 16, trans1Expr 5 1 k = trans1_r5_1 k := by decide +kernel
lemma trans1_r5_2_eq : ∀ k : Fin 16, trans1Expr 5 2 k = trans1_r5_2 k := by decide +kernel
lemma trans1_r5_3_eq : ∀ k : Fin 16, trans1Expr 5 3 k = trans1_r5_3 k := by decide +kernel
lemma trans1_r5_4_eq : ∀ k : Fin 16, trans1Expr 5 4 k = trans1_r5_4 k := by decide +kernel
lemma trans1_r5_5_eq : ∀ k : Fin 16, trans1Expr 5 5 k = trans1_r5_5 k := by decide +kernel
lemma trans1_r5_6_eq : ∀ k : Fin 16, trans1Expr 5 6 k = trans1_r5_6 k := by decide +kernel
lemma trans1_r5_7_eq : ∀ k : Fin 16, trans1Expr 5 7 k = trans1_r5_7 k := by decide +kernel
lemma trans1_r5_8_eq : ∀ k : Fin 16, trans1Expr 5 8 k = trans1_r5_8 k := by decide +kernel
lemma trans1_r5_9_eq : ∀ k : Fin 16, trans1Expr 5 9 k = trans1_r5_9 k := by decide +kernel
lemma trans1_r5_10_eq : ∀ k : Fin 16, trans1Expr 5 10 k = trans1_r5_10 k := by decide +kernel
lemma trans1_r5_11_eq : ∀ k : Fin 16, trans1Expr 5 11 k = trans1_r5_11 k := by decide +kernel
lemma trans1_r5_12_eq : ∀ k : Fin 16, trans1Expr 5 12 k = trans1_r5_12 k := by decide +kernel
lemma trans1_r5_13_eq : ∀ k : Fin 16, trans1Expr 5 13 k = trans1_r5_13 k := by decide +kernel
lemma trans1_r5_14_eq : ∀ k : Fin 16, trans1Expr 5 14 k = trans1_r5_14 k := by decide +kernel
lemma trans1_r5_15_eq : ∀ k : Fin 16, trans1Expr 5 15 k = trans1_r5_15 k := by decide +kernel
lemma trans1_r5_eq (i k : Fin 16) : trans1Expr 5 i k = trans1_r5 i k := by
  fin_cases i
  · exact trans1_r5_0_eq k
  · exact trans1_r5_1_eq k
  · exact trans1_r5_2_eq k
  · exact trans1_r5_3_eq k
  · exact trans1_r5_4_eq k
  · exact trans1_r5_5_eq k
  · exact trans1_r5_6_eq k
  · exact trans1_r5_7_eq k
  · exact trans1_r5_8_eq k
  · exact trans1_r5_9_eq k
  · exact trans1_r5_10_eq k
  · exact trans1_r5_11_eq k
  · exact trans1_r5_12_eq k
  · exact trans1_r5_13_eq k
  · exact trans1_r5_14_eq k
  · exact trans1_r5_15_eq k
noncomputable def trans1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans1_r0,trans1_r1,trans1_r2,trans1_r3,trans1_r4,trans1_r5]
lemma trans1_eq (j : Fin 6) (i k : Fin 16) : trans1Expr j i k = trans1 j i k := by
  fin_cases j
  · exact trans1_r0_eq i k
  · exact trans1_r1_eq i k
  · exact trans1_r2_eq i k
  · exact trans1_r3_eq i k
  · exact trans1_r4_eq i k
  · exact trans1_r5_eq i k
noncomputable def trans2Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans1 j i k).mul (transStep j i k)
lemma trans2_r0_0_eq : ∀ k : Fin 16, trans2Expr 0 0 k = trans2_r0_0 k := by decide +kernel
lemma trans2_r0_1_eq : ∀ k : Fin 16, trans2Expr 0 1 k = trans2_r0_1 k := by decide +kernel
lemma trans2_r0_2_eq : ∀ k : Fin 16, trans2Expr 0 2 k = trans2_r0_2 k := by decide +kernel
lemma trans2_r0_3_eq : ∀ k : Fin 16, trans2Expr 0 3 k = trans2_r0_3 k := by decide +kernel
lemma trans2_r0_4_eq : ∀ k : Fin 16, trans2Expr 0 4 k = trans2_r0_4 k := by decide +kernel
lemma trans2_r0_5_eq : ∀ k : Fin 16, trans2Expr 0 5 k = trans2_r0_5 k := by decide +kernel
lemma trans2_r0_6_eq : ∀ k : Fin 16, trans2Expr 0 6 k = trans2_r0_6 k := by decide +kernel
lemma trans2_r0_7_eq : ∀ k : Fin 16, trans2Expr 0 7 k = trans2_r0_7 k := by decide +kernel
lemma trans2_r0_8_eq : ∀ k : Fin 16, trans2Expr 0 8 k = trans2_r0_8 k := by decide +kernel
lemma trans2_r0_9_eq : ∀ k : Fin 16, trans2Expr 0 9 k = trans2_r0_9 k := by decide +kernel
lemma trans2_r0_10_eq : ∀ k : Fin 16, trans2Expr 0 10 k = trans2_r0_10 k := by decide +kernel
lemma trans2_r0_11_eq : ∀ k : Fin 16, trans2Expr 0 11 k = trans2_r0_11 k := by decide +kernel
lemma trans2_r0_12_eq : ∀ k : Fin 16, trans2Expr 0 12 k = trans2_r0_12 k := by decide +kernel
lemma trans2_r0_13_eq : ∀ k : Fin 16, trans2Expr 0 13 k = trans2_r0_13 k := by decide +kernel
lemma trans2_r0_14_eq : ∀ k : Fin 16, trans2Expr 0 14 k = trans2_r0_14 k := by decide +kernel
lemma trans2_r0_15_eq : ∀ k : Fin 16, trans2Expr 0 15 k = trans2_r0_15 k := by decide +kernel
lemma trans2_r0_eq (i k : Fin 16) : trans2Expr 0 i k = trans2_r0 i k := by
  fin_cases i
  · exact trans2_r0_0_eq k
  · exact trans2_r0_1_eq k
  · exact trans2_r0_2_eq k
  · exact trans2_r0_3_eq k
  · exact trans2_r0_4_eq k
  · exact trans2_r0_5_eq k
  · exact trans2_r0_6_eq k
  · exact trans2_r0_7_eq k
  · exact trans2_r0_8_eq k
  · exact trans2_r0_9_eq k
  · exact trans2_r0_10_eq k
  · exact trans2_r0_11_eq k
  · exact trans2_r0_12_eq k
  · exact trans2_r0_13_eq k
  · exact trans2_r0_14_eq k
  · exact trans2_r0_15_eq k
lemma trans2_r1_0_eq : ∀ k : Fin 16, trans2Expr 1 0 k = trans2_r1_0 k := by decide +kernel
lemma trans2_r1_1_eq : ∀ k : Fin 16, trans2Expr 1 1 k = trans2_r1_1 k := by decide +kernel
lemma trans2_r1_2_eq : ∀ k : Fin 16, trans2Expr 1 2 k = trans2_r1_2 k := by decide +kernel
lemma trans2_r1_3_eq : ∀ k : Fin 16, trans2Expr 1 3 k = trans2_r1_3 k := by decide +kernel
lemma trans2_r1_4_eq : ∀ k : Fin 16, trans2Expr 1 4 k = trans2_r1_4 k := by decide +kernel
lemma trans2_r1_5_eq : ∀ k : Fin 16, trans2Expr 1 5 k = trans2_r1_5 k := by decide +kernel
lemma trans2_r1_6_eq : ∀ k : Fin 16, trans2Expr 1 6 k = trans2_r1_6 k := by decide +kernel
lemma trans2_r1_7_eq : ∀ k : Fin 16, trans2Expr 1 7 k = trans2_r1_7 k := by decide +kernel
lemma trans2_r1_8_eq : ∀ k : Fin 16, trans2Expr 1 8 k = trans2_r1_8 k := by decide +kernel
lemma trans2_r1_9_eq : ∀ k : Fin 16, trans2Expr 1 9 k = trans2_r1_9 k := by decide +kernel
lemma trans2_r1_10_eq : ∀ k : Fin 16, trans2Expr 1 10 k = trans2_r1_10 k := by decide +kernel
lemma trans2_r1_11_eq : ∀ k : Fin 16, trans2Expr 1 11 k = trans2_r1_11 k := by decide +kernel
lemma trans2_r1_12_eq : ∀ k : Fin 16, trans2Expr 1 12 k = trans2_r1_12 k := by decide +kernel
lemma trans2_r1_13_eq : ∀ k : Fin 16, trans2Expr 1 13 k = trans2_r1_13 k := by decide +kernel
lemma trans2_r1_14_eq : ∀ k : Fin 16, trans2Expr 1 14 k = trans2_r1_14 k := by decide +kernel
lemma trans2_r1_15_eq : ∀ k : Fin 16, trans2Expr 1 15 k = trans2_r1_15 k := by decide +kernel
lemma trans2_r1_eq (i k : Fin 16) : trans2Expr 1 i k = trans2_r1 i k := by
  fin_cases i
  · exact trans2_r1_0_eq k
  · exact trans2_r1_1_eq k
  · exact trans2_r1_2_eq k
  · exact trans2_r1_3_eq k
  · exact trans2_r1_4_eq k
  · exact trans2_r1_5_eq k
  · exact trans2_r1_6_eq k
  · exact trans2_r1_7_eq k
  · exact trans2_r1_8_eq k
  · exact trans2_r1_9_eq k
  · exact trans2_r1_10_eq k
  · exact trans2_r1_11_eq k
  · exact trans2_r1_12_eq k
  · exact trans2_r1_13_eq k
  · exact trans2_r1_14_eq k
  · exact trans2_r1_15_eq k
lemma trans2_r2_0_eq : ∀ k : Fin 16, trans2Expr 2 0 k = trans2_r2_0 k := by decide +kernel
lemma trans2_r2_1_eq : ∀ k : Fin 16, trans2Expr 2 1 k = trans2_r2_1 k := by decide +kernel
lemma trans2_r2_2_eq : ∀ k : Fin 16, trans2Expr 2 2 k = trans2_r2_2 k := by decide +kernel
lemma trans2_r2_3_eq : ∀ k : Fin 16, trans2Expr 2 3 k = trans2_r2_3 k := by decide +kernel
lemma trans2_r2_4_eq : ∀ k : Fin 16, trans2Expr 2 4 k = trans2_r2_4 k := by decide +kernel
lemma trans2_r2_5_eq : ∀ k : Fin 16, trans2Expr 2 5 k = trans2_r2_5 k := by decide +kernel
lemma trans2_r2_6_eq : ∀ k : Fin 16, trans2Expr 2 6 k = trans2_r2_6 k := by decide +kernel
lemma trans2_r2_7_eq : ∀ k : Fin 16, trans2Expr 2 7 k = trans2_r2_7 k := by decide +kernel
lemma trans2_r2_8_eq : ∀ k : Fin 16, trans2Expr 2 8 k = trans2_r2_8 k := by decide +kernel
lemma trans2_r2_9_eq : ∀ k : Fin 16, trans2Expr 2 9 k = trans2_r2_9 k := by decide +kernel
lemma trans2_r2_10_eq : ∀ k : Fin 16, trans2Expr 2 10 k = trans2_r2_10 k := by decide +kernel
lemma trans2_r2_11_eq : ∀ k : Fin 16, trans2Expr 2 11 k = trans2_r2_11 k := by decide +kernel
lemma trans2_r2_12_eq : ∀ k : Fin 16, trans2Expr 2 12 k = trans2_r2_12 k := by decide +kernel
lemma trans2_r2_13_eq : ∀ k : Fin 16, trans2Expr 2 13 k = trans2_r2_13 k := by decide +kernel
lemma trans2_r2_14_eq : ∀ k : Fin 16, trans2Expr 2 14 k = trans2_r2_14 k := by decide +kernel
lemma trans2_r2_15_eq : ∀ k : Fin 16, trans2Expr 2 15 k = trans2_r2_15 k := by decide +kernel
lemma trans2_r2_eq (i k : Fin 16) : trans2Expr 2 i k = trans2_r2 i k := by
  fin_cases i
  · exact trans2_r2_0_eq k
  · exact trans2_r2_1_eq k
  · exact trans2_r2_2_eq k
  · exact trans2_r2_3_eq k
  · exact trans2_r2_4_eq k
  · exact trans2_r2_5_eq k
  · exact trans2_r2_6_eq k
  · exact trans2_r2_7_eq k
  · exact trans2_r2_8_eq k
  · exact trans2_r2_9_eq k
  · exact trans2_r2_10_eq k
  · exact trans2_r2_11_eq k
  · exact trans2_r2_12_eq k
  · exact trans2_r2_13_eq k
  · exact trans2_r2_14_eq k
  · exact trans2_r2_15_eq k
lemma trans2_r3_0_eq : ∀ k : Fin 16, trans2Expr 3 0 k = trans2_r3_0 k := by decide +kernel
lemma trans2_r3_1_eq : ∀ k : Fin 16, trans2Expr 3 1 k = trans2_r3_1 k := by decide +kernel
lemma trans2_r3_2_eq : ∀ k : Fin 16, trans2Expr 3 2 k = trans2_r3_2 k := by decide +kernel
lemma trans2_r3_3_eq : ∀ k : Fin 16, trans2Expr 3 3 k = trans2_r3_3 k := by decide +kernel
lemma trans2_r3_4_eq : ∀ k : Fin 16, trans2Expr 3 4 k = trans2_r3_4 k := by decide +kernel
lemma trans2_r3_5_eq : ∀ k : Fin 16, trans2Expr 3 5 k = trans2_r3_5 k := by decide +kernel
lemma trans2_r3_6_eq : ∀ k : Fin 16, trans2Expr 3 6 k = trans2_r3_6 k := by decide +kernel
lemma trans2_r3_7_eq : ∀ k : Fin 16, trans2Expr 3 7 k = trans2_r3_7 k := by decide +kernel
lemma trans2_r3_8_eq : ∀ k : Fin 16, trans2Expr 3 8 k = trans2_r3_8 k := by decide +kernel
lemma trans2_r3_9_eq : ∀ k : Fin 16, trans2Expr 3 9 k = trans2_r3_9 k := by decide +kernel
lemma trans2_r3_10_eq : ∀ k : Fin 16, trans2Expr 3 10 k = trans2_r3_10 k := by decide +kernel
lemma trans2_r3_11_eq : ∀ k : Fin 16, trans2Expr 3 11 k = trans2_r3_11 k := by decide +kernel
lemma trans2_r3_12_eq : ∀ k : Fin 16, trans2Expr 3 12 k = trans2_r3_12 k := by decide +kernel
lemma trans2_r3_13_eq : ∀ k : Fin 16, trans2Expr 3 13 k = trans2_r3_13 k := by decide +kernel
lemma trans2_r3_14_eq : ∀ k : Fin 16, trans2Expr 3 14 k = trans2_r3_14 k := by decide +kernel
lemma trans2_r3_15_eq : ∀ k : Fin 16, trans2Expr 3 15 k = trans2_r3_15 k := by decide +kernel
lemma trans2_r3_eq (i k : Fin 16) : trans2Expr 3 i k = trans2_r3 i k := by
  fin_cases i
  · exact trans2_r3_0_eq k
  · exact trans2_r3_1_eq k
  · exact trans2_r3_2_eq k
  · exact trans2_r3_3_eq k
  · exact trans2_r3_4_eq k
  · exact trans2_r3_5_eq k
  · exact trans2_r3_6_eq k
  · exact trans2_r3_7_eq k
  · exact trans2_r3_8_eq k
  · exact trans2_r3_9_eq k
  · exact trans2_r3_10_eq k
  · exact trans2_r3_11_eq k
  · exact trans2_r3_12_eq k
  · exact trans2_r3_13_eq k
  · exact trans2_r3_14_eq k
  · exact trans2_r3_15_eq k
lemma trans2_r4_0_eq : ∀ k : Fin 16, trans2Expr 4 0 k = trans2_r4_0 k := by decide +kernel
lemma trans2_r4_1_eq : ∀ k : Fin 16, trans2Expr 4 1 k = trans2_r4_1 k := by decide +kernel
lemma trans2_r4_2_eq : ∀ k : Fin 16, trans2Expr 4 2 k = trans2_r4_2 k := by decide +kernel
lemma trans2_r4_3_eq : ∀ k : Fin 16, trans2Expr 4 3 k = trans2_r4_3 k := by decide +kernel
lemma trans2_r4_4_eq : ∀ k : Fin 16, trans2Expr 4 4 k = trans2_r4_4 k := by decide +kernel
lemma trans2_r4_5_eq : ∀ k : Fin 16, trans2Expr 4 5 k = trans2_r4_5 k := by decide +kernel
lemma trans2_r4_6_eq : ∀ k : Fin 16, trans2Expr 4 6 k = trans2_r4_6 k := by decide +kernel
lemma trans2_r4_7_eq : ∀ k : Fin 16, trans2Expr 4 7 k = trans2_r4_7 k := by decide +kernel
lemma trans2_r4_8_eq : ∀ k : Fin 16, trans2Expr 4 8 k = trans2_r4_8 k := by decide +kernel
lemma trans2_r4_9_eq : ∀ k : Fin 16, trans2Expr 4 9 k = trans2_r4_9 k := by decide +kernel
lemma trans2_r4_10_eq : ∀ k : Fin 16, trans2Expr 4 10 k = trans2_r4_10 k := by decide +kernel
lemma trans2_r4_11_eq : ∀ k : Fin 16, trans2Expr 4 11 k = trans2_r4_11 k := by decide +kernel
lemma trans2_r4_12_eq : ∀ k : Fin 16, trans2Expr 4 12 k = trans2_r4_12 k := by decide +kernel
lemma trans2_r4_13_eq : ∀ k : Fin 16, trans2Expr 4 13 k = trans2_r4_13 k := by decide +kernel
lemma trans2_r4_14_eq : ∀ k : Fin 16, trans2Expr 4 14 k = trans2_r4_14 k := by decide +kernel
lemma trans2_r4_15_eq : ∀ k : Fin 16, trans2Expr 4 15 k = trans2_r4_15 k := by decide +kernel
lemma trans2_r4_eq (i k : Fin 16) : trans2Expr 4 i k = trans2_r4 i k := by
  fin_cases i
  · exact trans2_r4_0_eq k
  · exact trans2_r4_1_eq k
  · exact trans2_r4_2_eq k
  · exact trans2_r4_3_eq k
  · exact trans2_r4_4_eq k
  · exact trans2_r4_5_eq k
  · exact trans2_r4_6_eq k
  · exact trans2_r4_7_eq k
  · exact trans2_r4_8_eq k
  · exact trans2_r4_9_eq k
  · exact trans2_r4_10_eq k
  · exact trans2_r4_11_eq k
  · exact trans2_r4_12_eq k
  · exact trans2_r4_13_eq k
  · exact trans2_r4_14_eq k
  · exact trans2_r4_15_eq k
lemma trans2_r5_0_eq : ∀ k : Fin 16, trans2Expr 5 0 k = trans2_r5_0 k := by decide +kernel
lemma trans2_r5_1_eq : ∀ k : Fin 16, trans2Expr 5 1 k = trans2_r5_1 k := by decide +kernel
lemma trans2_r5_2_eq : ∀ k : Fin 16, trans2Expr 5 2 k = trans2_r5_2 k := by decide +kernel
lemma trans2_r5_3_eq : ∀ k : Fin 16, trans2Expr 5 3 k = trans2_r5_3 k := by decide +kernel
lemma trans2_r5_4_eq : ∀ k : Fin 16, trans2Expr 5 4 k = trans2_r5_4 k := by decide +kernel
lemma trans2_r5_5_eq : ∀ k : Fin 16, trans2Expr 5 5 k = trans2_r5_5 k := by decide +kernel
lemma trans2_r5_6_eq : ∀ k : Fin 16, trans2Expr 5 6 k = trans2_r5_6 k := by decide +kernel
lemma trans2_r5_7_eq : ∀ k : Fin 16, trans2Expr 5 7 k = trans2_r5_7 k := by decide +kernel
lemma trans2_r5_8_eq : ∀ k : Fin 16, trans2Expr 5 8 k = trans2_r5_8 k := by decide +kernel
lemma trans2_r5_9_eq : ∀ k : Fin 16, trans2Expr 5 9 k = trans2_r5_9 k := by decide +kernel
lemma trans2_r5_10_eq : ∀ k : Fin 16, trans2Expr 5 10 k = trans2_r5_10 k := by decide +kernel
lemma trans2_r5_11_eq : ∀ k : Fin 16, trans2Expr 5 11 k = trans2_r5_11 k := by decide +kernel
lemma trans2_r5_12_eq : ∀ k : Fin 16, trans2Expr 5 12 k = trans2_r5_12 k := by decide +kernel
lemma trans2_r5_13_eq : ∀ k : Fin 16, trans2Expr 5 13 k = trans2_r5_13 k := by decide +kernel
lemma trans2_r5_14_eq : ∀ k : Fin 16, trans2Expr 5 14 k = trans2_r5_14 k := by decide +kernel
lemma trans2_r5_15_eq : ∀ k : Fin 16, trans2Expr 5 15 k = trans2_r5_15 k := by decide +kernel
lemma trans2_r5_eq (i k : Fin 16) : trans2Expr 5 i k = trans2_r5 i k := by
  fin_cases i
  · exact trans2_r5_0_eq k
  · exact trans2_r5_1_eq k
  · exact trans2_r5_2_eq k
  · exact trans2_r5_3_eq k
  · exact trans2_r5_4_eq k
  · exact trans2_r5_5_eq k
  · exact trans2_r5_6_eq k
  · exact trans2_r5_7_eq k
  · exact trans2_r5_8_eq k
  · exact trans2_r5_9_eq k
  · exact trans2_r5_10_eq k
  · exact trans2_r5_11_eq k
  · exact trans2_r5_12_eq k
  · exact trans2_r5_13_eq k
  · exact trans2_r5_14_eq k
  · exact trans2_r5_15_eq k
lemma trans2_eq (j : Fin 6) (i k : Fin 16) : trans2Expr j i k = trans2 j i k := by
  fin_cases j
  · exact trans2_r0_eq i k
  · exact trans2_r1_eq i k
  · exact trans2_r2_eq i k
  · exact trans2_r3_eq i k
  · exact trans2_r4_eq i k
  · exact trans2_r5_eq i k
noncomputable def trans3Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans2 j i k).mul (transStep j i k)
lemma trans3_r0_0_eq : ∀ k : Fin 16, trans3Expr 0 0 k = trans3_r0_0 k := by decide +kernel
lemma trans3_r0_1_eq : ∀ k : Fin 16, trans3Expr 0 1 k = trans3_r0_1 k := by decide +kernel
lemma trans3_r0_2_eq : ∀ k : Fin 16, trans3Expr 0 2 k = trans3_r0_2 k := by decide +kernel
lemma trans3_r0_3_eq : ∀ k : Fin 16, trans3Expr 0 3 k = trans3_r0_3 k := by decide +kernel
lemma trans3_r0_4_eq : ∀ k : Fin 16, trans3Expr 0 4 k = trans3_r0_4 k := by decide +kernel
lemma trans3_r0_5_eq : ∀ k : Fin 16, trans3Expr 0 5 k = trans3_r0_5 k := by decide +kernel
lemma trans3_r0_6_eq : ∀ k : Fin 16, trans3Expr 0 6 k = trans3_r0_6 k := by decide +kernel
lemma trans3_r0_7_eq : ∀ k : Fin 16, trans3Expr 0 7 k = trans3_r0_7 k := by decide +kernel
lemma trans3_r0_8_eq : ∀ k : Fin 16, trans3Expr 0 8 k = trans3_r0_8 k := by decide +kernel
lemma trans3_r0_9_eq : ∀ k : Fin 16, trans3Expr 0 9 k = trans3_r0_9 k := by decide +kernel
lemma trans3_r0_10_eq : ∀ k : Fin 16, trans3Expr 0 10 k = trans3_r0_10 k := by decide +kernel
lemma trans3_r0_11_eq : ∀ k : Fin 16, trans3Expr 0 11 k = trans3_r0_11 k := by decide +kernel
lemma trans3_r0_12_eq : ∀ k : Fin 16, trans3Expr 0 12 k = trans3_r0_12 k := by decide +kernel
lemma trans3_r0_13_eq : ∀ k : Fin 16, trans3Expr 0 13 k = trans3_r0_13 k := by decide +kernel
lemma trans3_r0_14_eq : ∀ k : Fin 16, trans3Expr 0 14 k = trans3_r0_14 k := by decide +kernel
lemma trans3_r0_15_eq : ∀ k : Fin 16, trans3Expr 0 15 k = trans3_r0_15 k := by decide +kernel
lemma trans3_r0_eq (i k : Fin 16) : trans3Expr 0 i k = trans3_r0 i k := by
  fin_cases i
  · exact trans3_r0_0_eq k
  · exact trans3_r0_1_eq k
  · exact trans3_r0_2_eq k
  · exact trans3_r0_3_eq k
  · exact trans3_r0_4_eq k
  · exact trans3_r0_5_eq k
  · exact trans3_r0_6_eq k
  · exact trans3_r0_7_eq k
  · exact trans3_r0_8_eq k
  · exact trans3_r0_9_eq k
  · exact trans3_r0_10_eq k
  · exact trans3_r0_11_eq k
  · exact trans3_r0_12_eq k
  · exact trans3_r0_13_eq k
  · exact trans3_r0_14_eq k
  · exact trans3_r0_15_eq k
lemma trans3_r1_0_eq : ∀ k : Fin 16, trans3Expr 1 0 k = trans3_r1_0 k := by decide +kernel
lemma trans3_r1_1_eq : ∀ k : Fin 16, trans3Expr 1 1 k = trans3_r1_1 k := by decide +kernel
lemma trans3_r1_2_eq : ∀ k : Fin 16, trans3Expr 1 2 k = trans3_r1_2 k := by decide +kernel
lemma trans3_r1_3_eq : ∀ k : Fin 16, trans3Expr 1 3 k = trans3_r1_3 k := by decide +kernel
lemma trans3_r1_4_eq : ∀ k : Fin 16, trans3Expr 1 4 k = trans3_r1_4 k := by decide +kernel
lemma trans3_r1_5_eq : ∀ k : Fin 16, trans3Expr 1 5 k = trans3_r1_5 k := by decide +kernel
lemma trans3_r1_6_eq : ∀ k : Fin 16, trans3Expr 1 6 k = trans3_r1_6 k := by decide +kernel
lemma trans3_r1_7_eq : ∀ k : Fin 16, trans3Expr 1 7 k = trans3_r1_7 k := by decide +kernel
lemma trans3_r1_8_eq : ∀ k : Fin 16, trans3Expr 1 8 k = trans3_r1_8 k := by decide +kernel
lemma trans3_r1_9_eq : ∀ k : Fin 16, trans3Expr 1 9 k = trans3_r1_9 k := by decide +kernel
lemma trans3_r1_10_eq : ∀ k : Fin 16, trans3Expr 1 10 k = trans3_r1_10 k := by decide +kernel
lemma trans3_r1_11_eq : ∀ k : Fin 16, trans3Expr 1 11 k = trans3_r1_11 k := by decide +kernel
lemma trans3_r1_12_eq : ∀ k : Fin 16, trans3Expr 1 12 k = trans3_r1_12 k := by decide +kernel
lemma trans3_r1_13_eq : ∀ k : Fin 16, trans3Expr 1 13 k = trans3_r1_13 k := by decide +kernel
lemma trans3_r1_14_eq : ∀ k : Fin 16, trans3Expr 1 14 k = trans3_r1_14 k := by decide +kernel
lemma trans3_r1_15_eq : ∀ k : Fin 16, trans3Expr 1 15 k = trans3_r1_15 k := by decide +kernel
lemma trans3_r1_eq (i k : Fin 16) : trans3Expr 1 i k = trans3_r1 i k := by
  fin_cases i
  · exact trans3_r1_0_eq k
  · exact trans3_r1_1_eq k
  · exact trans3_r1_2_eq k
  · exact trans3_r1_3_eq k
  · exact trans3_r1_4_eq k
  · exact trans3_r1_5_eq k
  · exact trans3_r1_6_eq k
  · exact trans3_r1_7_eq k
  · exact trans3_r1_8_eq k
  · exact trans3_r1_9_eq k
  · exact trans3_r1_10_eq k
  · exact trans3_r1_11_eq k
  · exact trans3_r1_12_eq k
  · exact trans3_r1_13_eq k
  · exact trans3_r1_14_eq k
  · exact trans3_r1_15_eq k
lemma trans3_r2_0_eq : ∀ k : Fin 16, trans3Expr 2 0 k = trans3_r2_0 k := by decide +kernel
lemma trans3_r2_1_eq : ∀ k : Fin 16, trans3Expr 2 1 k = trans3_r2_1 k := by decide +kernel
lemma trans3_r2_2_eq : ∀ k : Fin 16, trans3Expr 2 2 k = trans3_r2_2 k := by decide +kernel
lemma trans3_r2_3_eq : ∀ k : Fin 16, trans3Expr 2 3 k = trans3_r2_3 k := by decide +kernel
lemma trans3_r2_4_eq : ∀ k : Fin 16, trans3Expr 2 4 k = trans3_r2_4 k := by decide +kernel
lemma trans3_r2_5_eq : ∀ k : Fin 16, trans3Expr 2 5 k = trans3_r2_5 k := by decide +kernel
lemma trans3_r2_6_eq : ∀ k : Fin 16, trans3Expr 2 6 k = trans3_r2_6 k := by decide +kernel
lemma trans3_r2_7_eq : ∀ k : Fin 16, trans3Expr 2 7 k = trans3_r2_7 k := by decide +kernel
lemma trans3_r2_8_eq : ∀ k : Fin 16, trans3Expr 2 8 k = trans3_r2_8 k := by decide +kernel
lemma trans3_r2_9_eq : ∀ k : Fin 16, trans3Expr 2 9 k = trans3_r2_9 k := by decide +kernel
lemma trans3_r2_10_eq : ∀ k : Fin 16, trans3Expr 2 10 k = trans3_r2_10 k := by decide +kernel
lemma trans3_r2_11_eq : ∀ k : Fin 16, trans3Expr 2 11 k = trans3_r2_11 k := by decide +kernel
lemma trans3_r2_12_eq : ∀ k : Fin 16, trans3Expr 2 12 k = trans3_r2_12 k := by decide +kernel
lemma trans3_r2_13_eq : ∀ k : Fin 16, trans3Expr 2 13 k = trans3_r2_13 k := by decide +kernel
lemma trans3_r2_14_eq : ∀ k : Fin 16, trans3Expr 2 14 k = trans3_r2_14 k := by decide +kernel
lemma trans3_r2_15_eq : ∀ k : Fin 16, trans3Expr 2 15 k = trans3_r2_15 k := by decide +kernel
lemma trans3_r2_eq (i k : Fin 16) : trans3Expr 2 i k = trans3_r2 i k := by
  fin_cases i
  · exact trans3_r2_0_eq k
  · exact trans3_r2_1_eq k
  · exact trans3_r2_2_eq k
  · exact trans3_r2_3_eq k
  · exact trans3_r2_4_eq k
  · exact trans3_r2_5_eq k
  · exact trans3_r2_6_eq k
  · exact trans3_r2_7_eq k
  · exact trans3_r2_8_eq k
  · exact trans3_r2_9_eq k
  · exact trans3_r2_10_eq k
  · exact trans3_r2_11_eq k
  · exact trans3_r2_12_eq k
  · exact trans3_r2_13_eq k
  · exact trans3_r2_14_eq k
  · exact trans3_r2_15_eq k
lemma trans3_r3_0_eq : ∀ k : Fin 16, trans3Expr 3 0 k = trans3_r3_0 k := by decide +kernel
lemma trans3_r3_1_eq : ∀ k : Fin 16, trans3Expr 3 1 k = trans3_r3_1 k := by decide +kernel
lemma trans3_r3_2_eq : ∀ k : Fin 16, trans3Expr 3 2 k = trans3_r3_2 k := by decide +kernel
lemma trans3_r3_3_eq : ∀ k : Fin 16, trans3Expr 3 3 k = trans3_r3_3 k := by decide +kernel
lemma trans3_r3_4_eq : ∀ k : Fin 16, trans3Expr 3 4 k = trans3_r3_4 k := by decide +kernel
lemma trans3_r3_5_eq : ∀ k : Fin 16, trans3Expr 3 5 k = trans3_r3_5 k := by decide +kernel
lemma trans3_r3_6_eq : ∀ k : Fin 16, trans3Expr 3 6 k = trans3_r3_6 k := by decide +kernel
lemma trans3_r3_7_eq : ∀ k : Fin 16, trans3Expr 3 7 k = trans3_r3_7 k := by decide +kernel
lemma trans3_r3_8_eq : ∀ k : Fin 16, trans3Expr 3 8 k = trans3_r3_8 k := by decide +kernel
lemma trans3_r3_9_eq : ∀ k : Fin 16, trans3Expr 3 9 k = trans3_r3_9 k := by decide +kernel
lemma trans3_r3_10_eq : ∀ k : Fin 16, trans3Expr 3 10 k = trans3_r3_10 k := by decide +kernel
lemma trans3_r3_11_eq : ∀ k : Fin 16, trans3Expr 3 11 k = trans3_r3_11 k := by decide +kernel
lemma trans3_r3_12_eq : ∀ k : Fin 16, trans3Expr 3 12 k = trans3_r3_12 k := by decide +kernel
lemma trans3_r3_13_eq : ∀ k : Fin 16, trans3Expr 3 13 k = trans3_r3_13 k := by decide +kernel
lemma trans3_r3_14_eq : ∀ k : Fin 16, trans3Expr 3 14 k = trans3_r3_14 k := by decide +kernel
lemma trans3_r3_15_eq : ∀ k : Fin 16, trans3Expr 3 15 k = trans3_r3_15 k := by decide +kernel
lemma trans3_r3_eq (i k : Fin 16) : trans3Expr 3 i k = trans3_r3 i k := by
  fin_cases i
  · exact trans3_r3_0_eq k
  · exact trans3_r3_1_eq k
  · exact trans3_r3_2_eq k
  · exact trans3_r3_3_eq k
  · exact trans3_r3_4_eq k
  · exact trans3_r3_5_eq k
  · exact trans3_r3_6_eq k
  · exact trans3_r3_7_eq k
  · exact trans3_r3_8_eq k
  · exact trans3_r3_9_eq k
  · exact trans3_r3_10_eq k
  · exact trans3_r3_11_eq k
  · exact trans3_r3_12_eq k
  · exact trans3_r3_13_eq k
  · exact trans3_r3_14_eq k
  · exact trans3_r3_15_eq k
lemma trans3_r4_0_eq : ∀ k : Fin 16, trans3Expr 4 0 k = trans3_r4_0 k := by decide +kernel
lemma trans3_r4_1_eq : ∀ k : Fin 16, trans3Expr 4 1 k = trans3_r4_1 k := by decide +kernel
lemma trans3_r4_2_eq : ∀ k : Fin 16, trans3Expr 4 2 k = trans3_r4_2 k := by decide +kernel
lemma trans3_r4_3_eq : ∀ k : Fin 16, trans3Expr 4 3 k = trans3_r4_3 k := by decide +kernel
lemma trans3_r4_4_eq : ∀ k : Fin 16, trans3Expr 4 4 k = trans3_r4_4 k := by decide +kernel
lemma trans3_r4_5_eq : ∀ k : Fin 16, trans3Expr 4 5 k = trans3_r4_5 k := by decide +kernel
lemma trans3_r4_6_eq : ∀ k : Fin 16, trans3Expr 4 6 k = trans3_r4_6 k := by decide +kernel
lemma trans3_r4_7_eq : ∀ k : Fin 16, trans3Expr 4 7 k = trans3_r4_7 k := by decide +kernel
lemma trans3_r4_8_eq : ∀ k : Fin 16, trans3Expr 4 8 k = trans3_r4_8 k := by decide +kernel
lemma trans3_r4_9_eq : ∀ k : Fin 16, trans3Expr 4 9 k = trans3_r4_9 k := by decide +kernel
lemma trans3_r4_10_eq : ∀ k : Fin 16, trans3Expr 4 10 k = trans3_r4_10 k := by decide +kernel
lemma trans3_r4_11_eq : ∀ k : Fin 16, trans3Expr 4 11 k = trans3_r4_11 k := by decide +kernel
lemma trans3_r4_12_eq : ∀ k : Fin 16, trans3Expr 4 12 k = trans3_r4_12 k := by decide +kernel
lemma trans3_r4_13_eq : ∀ k : Fin 16, trans3Expr 4 13 k = trans3_r4_13 k := by decide +kernel
lemma trans3_r4_14_eq : ∀ k : Fin 16, trans3Expr 4 14 k = trans3_r4_14 k := by decide +kernel
lemma trans3_r4_15_eq : ∀ k : Fin 16, trans3Expr 4 15 k = trans3_r4_15 k := by decide +kernel
noncomputable def trans3_r4 : Fin 16 → Fin 16 → CBox := ![trans3_r4_0,trans3_r4_1,trans3_r4_2,trans3_r4_3,trans3_r4_4,trans3_r4_5,trans3_r4_6,trans3_r4_7,trans3_r4_8,trans3_r4_9,trans3_r4_10,trans3_r4_11,trans3_r4_12,trans3_r4_13,trans3_r4_14,trans3_r4_15]
lemma trans3_r4_eq (i k : Fin 16) : trans3Expr 4 i k = trans3_r4 i k := by
  fin_cases i
  · exact trans3_r4_0_eq k
  · exact trans3_r4_1_eq k
  · exact trans3_r4_2_eq k
  · exact trans3_r4_3_eq k
  · exact trans3_r4_4_eq k
  · exact trans3_r4_5_eq k
  · exact trans3_r4_6_eq k
  · exact trans3_r4_7_eq k
  · exact trans3_r4_8_eq k
  · exact trans3_r4_9_eq k
  · exact trans3_r4_10_eq k
  · exact trans3_r4_11_eq k
  · exact trans3_r4_12_eq k
  · exact trans3_r4_13_eq k
  · exact trans3_r4_14_eq k
  · exact trans3_r4_15_eq k
lemma trans3_r5_0_eq : ∀ k : Fin 16, trans3Expr 5 0 k = trans3_r5_0 k := by decide +kernel
lemma trans3_r5_1_eq : ∀ k : Fin 16, trans3Expr 5 1 k = trans3_r5_1 k := by decide +kernel
lemma trans3_r5_2_eq : ∀ k : Fin 16, trans3Expr 5 2 k = trans3_r5_2 k := by decide +kernel
lemma trans3_r5_3_eq : ∀ k : Fin 16, trans3Expr 5 3 k = trans3_r5_3 k := by decide +kernel
lemma trans3_r5_4_eq : ∀ k : Fin 16, trans3Expr 5 4 k = trans3_r5_4 k := by decide +kernel
lemma trans3_r5_5_eq : ∀ k : Fin 16, trans3Expr 5 5 k = trans3_r5_5 k := by decide +kernel
lemma trans3_r5_6_eq : ∀ k : Fin 16, trans3Expr 5 6 k = trans3_r5_6 k := by decide +kernel
lemma trans3_r5_7_eq : ∀ k : Fin 16, trans3Expr 5 7 k = trans3_r5_7 k := by decide +kernel
lemma trans3_r5_8_eq : ∀ k : Fin 16, trans3Expr 5 8 k = trans3_r5_8 k := by decide +kernel
lemma trans3_r5_9_eq : ∀ k : Fin 16, trans3Expr 5 9 k = trans3_r5_9 k := by decide +kernel
lemma trans3_r5_10_eq : ∀ k : Fin 16, trans3Expr 5 10 k = trans3_r5_10 k := by decide +kernel
lemma trans3_r5_11_eq : ∀ k : Fin 16, trans3Expr 5 11 k = trans3_r5_11 k := by decide +kernel
lemma trans3_r5_12_eq : ∀ k : Fin 16, trans3Expr 5 12 k = trans3_r5_12 k := by decide +kernel
lemma trans3_r5_13_eq : ∀ k : Fin 16, trans3Expr 5 13 k = trans3_r5_13 k := by decide +kernel
lemma trans3_r5_14_eq : ∀ k : Fin 16, trans3Expr 5 14 k = trans3_r5_14 k := by decide +kernel
lemma trans3_r5_15_eq : ∀ k : Fin 16, trans3Expr 5 15 k = trans3_r5_15 k := by decide +kernel
lemma trans3_r5_eq (i k : Fin 16) : trans3Expr 5 i k = trans3_r5 i k := by
  fin_cases i
  · exact trans3_r5_0_eq k
  · exact trans3_r5_1_eq k
  · exact trans3_r5_2_eq k
  · exact trans3_r5_3_eq k
  · exact trans3_r5_4_eq k
  · exact trans3_r5_5_eq k
  · exact trans3_r5_6_eq k
  · exact trans3_r5_7_eq k
  · exact trans3_r5_8_eq k
  · exact trans3_r5_9_eq k
  · exact trans3_r5_10_eq k
  · exact trans3_r5_11_eq k
  · exact trans3_r5_12_eq k
  · exact trans3_r5_13_eq k
  · exact trans3_r5_14_eq k
  · exact trans3_r5_15_eq k
noncomputable def trans3 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans3_r0,trans3_r1,trans3_r2,trans3_r3,trans3_r4,trans3_r5]
lemma trans3_eq (j : Fin 6) (i k : Fin 16) : trans3Expr j i k = trans3 j i k := by
  fin_cases j
  · exact trans3_r0_eq i k
  · exact trans3_r1_eq i k
  · exact trans3_r2_eq i k
  · exact trans3_r3_eq i k
  · exact trans3_r4_eq i k
  · exact trans3_r5_eq i k
noncomputable def trans4Expr (j : Fin 6) (i k : Fin 16) : CBox := (trans3 j i k).mul (transStep j i k)
lemma trans4_r0_0_eq : ∀ k : Fin 16, trans4Expr 0 0 k = trans4_r0_0 k := by decide +kernel
lemma trans4_r0_1_eq : ∀ k : Fin 16, trans4Expr 0 1 k = trans4_r0_1 k := by decide +kernel
lemma trans4_r0_2_eq : ∀ k : Fin 16, trans4Expr 0 2 k = trans4_r0_2 k := by decide +kernel
lemma trans4_r0_3_eq : ∀ k : Fin 16, trans4Expr 0 3 k = trans4_r0_3 k := by decide +kernel
lemma trans4_r0_4_eq : ∀ k : Fin 16, trans4Expr 0 4 k = trans4_r0_4 k := by decide +kernel
lemma trans4_r0_5_eq : ∀ k : Fin 16, trans4Expr 0 5 k = trans4_r0_5 k := by decide +kernel
lemma trans4_r0_6_eq : ∀ k : Fin 16, trans4Expr 0 6 k = trans4_r0_6 k := by decide +kernel
lemma trans4_r0_7_eq : ∀ k : Fin 16, trans4Expr 0 7 k = trans4_r0_7 k := by decide +kernel
lemma trans4_r0_8_eq : ∀ k : Fin 16, trans4Expr 0 8 k = trans4_r0_8 k := by decide +kernel
lemma trans4_r0_9_eq : ∀ k : Fin 16, trans4Expr 0 9 k = trans4_r0_9 k := by decide +kernel
lemma trans4_r0_10_eq : ∀ k : Fin 16, trans4Expr 0 10 k = trans4_r0_10 k := by decide +kernel
lemma trans4_r0_11_eq : ∀ k : Fin 16, trans4Expr 0 11 k = trans4_r0_11 k := by decide +kernel
lemma trans4_r0_12_eq : ∀ k : Fin 16, trans4Expr 0 12 k = trans4_r0_12 k := by decide +kernel
lemma trans4_r0_13_eq : ∀ k : Fin 16, trans4Expr 0 13 k = trans4_r0_13 k := by decide +kernel
lemma trans4_r0_14_eq : ∀ k : Fin 16, trans4Expr 0 14 k = trans4_r0_14 k := by decide +kernel
lemma trans4_r0_15_eq : ∀ k : Fin 16, trans4Expr 0 15 k = trans4_r0_15 k := by decide +kernel
lemma trans4_r0_eq (i k : Fin 16) : trans4Expr 0 i k = trans4_r0 i k := by
  fin_cases i
  · exact trans4_r0_0_eq k
  · exact trans4_r0_1_eq k
  · exact trans4_r0_2_eq k
  · exact trans4_r0_3_eq k
  · exact trans4_r0_4_eq k
  · exact trans4_r0_5_eq k
  · exact trans4_r0_6_eq k
  · exact trans4_r0_7_eq k
  · exact trans4_r0_8_eq k
  · exact trans4_r0_9_eq k
  · exact trans4_r0_10_eq k
  · exact trans4_r0_11_eq k
  · exact trans4_r0_12_eq k
  · exact trans4_r0_13_eq k
  · exact trans4_r0_14_eq k
  · exact trans4_r0_15_eq k
lemma trans4_r1_0_eq : ∀ k : Fin 16, trans4Expr 1 0 k = trans4_r1_0 k := by decide +kernel
lemma trans4_r1_1_eq : ∀ k : Fin 16, trans4Expr 1 1 k = trans4_r1_1 k := by decide +kernel
lemma trans4_r1_2_eq : ∀ k : Fin 16, trans4Expr 1 2 k = trans4_r1_2 k := by decide +kernel
lemma trans4_r1_3_eq : ∀ k : Fin 16, trans4Expr 1 3 k = trans4_r1_3 k := by decide +kernel
lemma trans4_r1_4_eq : ∀ k : Fin 16, trans4Expr 1 4 k = trans4_r1_4 k := by decide +kernel
lemma trans4_r1_5_eq : ∀ k : Fin 16, trans4Expr 1 5 k = trans4_r1_5 k := by decide +kernel
lemma trans4_r1_6_eq : ∀ k : Fin 16, trans4Expr 1 6 k = trans4_r1_6 k := by decide +kernel
lemma trans4_r1_7_eq : ∀ k : Fin 16, trans4Expr 1 7 k = trans4_r1_7 k := by decide +kernel
lemma trans4_r1_8_eq : ∀ k : Fin 16, trans4Expr 1 8 k = trans4_r1_8 k := by decide +kernel
lemma trans4_r1_9_eq : ∀ k : Fin 16, trans4Expr 1 9 k = trans4_r1_9 k := by decide +kernel
lemma trans4_r1_10_eq : ∀ k : Fin 16, trans4Expr 1 10 k = trans4_r1_10 k := by decide +kernel
lemma trans4_r1_11_eq : ∀ k : Fin 16, trans4Expr 1 11 k = trans4_r1_11 k := by decide +kernel
lemma trans4_r1_12_eq : ∀ k : Fin 16, trans4Expr 1 12 k = trans4_r1_12 k := by decide +kernel
lemma trans4_r1_13_eq : ∀ k : Fin 16, trans4Expr 1 13 k = trans4_r1_13 k := by decide +kernel
lemma trans4_r1_14_eq : ∀ k : Fin 16, trans4Expr 1 14 k = trans4_r1_14 k := by decide +kernel
lemma trans4_r1_15_eq : ∀ k : Fin 16, trans4Expr 1 15 k = trans4_r1_15 k := by decide +kernel
lemma trans4_r1_eq (i k : Fin 16) : trans4Expr 1 i k = trans4_r1 i k := by
  fin_cases i
  · exact trans4_r1_0_eq k
  · exact trans4_r1_1_eq k
  · exact trans4_r1_2_eq k
  · exact trans4_r1_3_eq k
  · exact trans4_r1_4_eq k
  · exact trans4_r1_5_eq k
  · exact trans4_r1_6_eq k
  · exact trans4_r1_7_eq k
  · exact trans4_r1_8_eq k
  · exact trans4_r1_9_eq k
  · exact trans4_r1_10_eq k
  · exact trans4_r1_11_eq k
  · exact trans4_r1_12_eq k
  · exact trans4_r1_13_eq k
  · exact trans4_r1_14_eq k
  · exact trans4_r1_15_eq k
lemma trans4_r2_0_eq : ∀ k : Fin 16, trans4Expr 2 0 k = trans4_r2_0 k := by decide +kernel
lemma trans4_r2_1_eq : ∀ k : Fin 16, trans4Expr 2 1 k = trans4_r2_1 k := by decide +kernel
lemma trans4_r2_2_eq : ∀ k : Fin 16, trans4Expr 2 2 k = trans4_r2_2 k := by decide +kernel
lemma trans4_r2_3_eq : ∀ k : Fin 16, trans4Expr 2 3 k = trans4_r2_3 k := by decide +kernel
lemma trans4_r2_4_eq : ∀ k : Fin 16, trans4Expr 2 4 k = trans4_r2_4 k := by decide +kernel
lemma trans4_r2_5_eq : ∀ k : Fin 16, trans4Expr 2 5 k = trans4_r2_5 k := by decide +kernel
lemma trans4_r2_6_eq : ∀ k : Fin 16, trans4Expr 2 6 k = trans4_r2_6 k := by decide +kernel
lemma trans4_r2_7_eq : ∀ k : Fin 16, trans4Expr 2 7 k = trans4_r2_7 k := by decide +kernel
lemma trans4_r2_8_eq : ∀ k : Fin 16, trans4Expr 2 8 k = trans4_r2_8 k := by decide +kernel
lemma trans4_r2_9_eq : ∀ k : Fin 16, trans4Expr 2 9 k = trans4_r2_9 k := by decide +kernel
lemma trans4_r2_10_eq : ∀ k : Fin 16, trans4Expr 2 10 k = trans4_r2_10 k := by decide +kernel
lemma trans4_r2_11_eq : ∀ k : Fin 16, trans4Expr 2 11 k = trans4_r2_11 k := by decide +kernel
lemma trans4_r2_12_eq : ∀ k : Fin 16, trans4Expr 2 12 k = trans4_r2_12 k := by decide +kernel
lemma trans4_r2_13_eq : ∀ k : Fin 16, trans4Expr 2 13 k = trans4_r2_13 k := by decide +kernel
lemma trans4_r2_14_eq : ∀ k : Fin 16, trans4Expr 2 14 k = trans4_r2_14 k := by decide +kernel
lemma trans4_r2_15_eq : ∀ k : Fin 16, trans4Expr 2 15 k = trans4_r2_15 k := by decide +kernel
lemma trans4_r2_eq (i k : Fin 16) : trans4Expr 2 i k = trans4_r2 i k := by
  fin_cases i
  · exact trans4_r2_0_eq k
  · exact trans4_r2_1_eq k
  · exact trans4_r2_2_eq k
  · exact trans4_r2_3_eq k
  · exact trans4_r2_4_eq k
  · exact trans4_r2_5_eq k
  · exact trans4_r2_6_eq k
  · exact trans4_r2_7_eq k
  · exact trans4_r2_8_eq k
  · exact trans4_r2_9_eq k
  · exact trans4_r2_10_eq k
  · exact trans4_r2_11_eq k
  · exact trans4_r2_12_eq k
  · exact trans4_r2_13_eq k
  · exact trans4_r2_14_eq k
  · exact trans4_r2_15_eq k
lemma trans4_r3_0_eq : ∀ k : Fin 16, trans4Expr 3 0 k = trans4_r3_0 k := by decide +kernel
lemma trans4_r3_10_eq : ∀ k : Fin 16, trans4Expr 3 10 k = trans4_r3_10 k := by decide +kernel
lemma trans4_r3_11_eq : ∀ k : Fin 16, trans4Expr 3 11 k = trans4_r3_11 k := by decide +kernel
lemma trans4_r3_12_eq : ∀ k : Fin 16, trans4Expr 3 12 k = trans4_r3_12 k := by decide +kernel
lemma trans4_r3_13_eq : ∀ k : Fin 16, trans4Expr 3 13 k = trans4_r3_13 k := by decide +kernel
lemma trans4_r3_14_eq : ∀ k : Fin 16, trans4Expr 3 14 k = trans4_r3_14 k := by decide +kernel
end SharpPlanar.CachedData

end OAI
end

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
noncomputable def kernel4_0_r3 : Fin 16 → Fin 16 → CBox := ![kernel4_0_r3_0,kernel4_0_r3_1,kernel4_0_r3_2,kernel4_0_r3_3,kernel4_0_r3_4,kernel4_0_r3_5,kernel4_0_r3_6,kernel4_0_r3_7,kernel4_0_r3_8,kernel4_0_r3_9,kernel4_0_r3_10,kernel4_0_r3_11,kernel4_0_r3_12,kernel4_0_r3_13,kernel4_0_r3_14,kernel4_0_r3_15]
noncomputable def kernel4_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel4_0_r0,kernel4_0_r1,kernel4_0_r2,kernel4_0_r3,kernel4_0_r4,kernel4_0_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments100
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
namespace cm100_1_0_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm100_1_0_1
namespace cm100_1_1_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm100_1_1_0
namespace cm100_1_1_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm100_1_1_1
namespace cm100_3_0_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm100_3_0_0
namespace cm100_3_0_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm100_3_0_1
namespace cm100_4_0_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end cm100_4_0_0
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_UMoments12
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
namespace cm12_3_0_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
end cm12_3_0_1
end SharpPlanar.CachedData

end OAI
end


