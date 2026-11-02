-- Prove2me | Definitions.Def_OAIQ098D274
-- name    : OAIQ098D274
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T16:58:03.217191+00:00
-- url     : https://prove2.me/theorems/57e4180e-fff4-4743-8fb4-1ba8d8c1e17b
-- title:
--   Definitions bundle OAIQ098D274 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 432 declarations of OpenAI's Lean: 133 definitions and 299 theorems. The definitions and types are `OAI.SharpPlanar.CachedData.hm4_1_1_17.s1`, `OAI.SharpPlanar.CachedData.hm4_1_1_17.s2`, `OAI.SharpPlanar.CachedData.hm4_1_1_17.s3`, `OAI.SharpPlanar.CachedData.hm4_1_1_17.s4`, `OAI.SharpPlanar.CachedData.hm4_1_1_17.s5`, `OAI.SharpPlanar.CachedData.hm7_0_0_10.s0`, `OAI.SharpPlanar.CachedData.hm7_0_0_10.sums`, `OAI.SharpPlanar.CachedData.hm7_0_0_13.s0`, `OAI.SharpPlanar.CachedData.hm7_0_0_13.s1`, `OAI.SharpPlanar.CachedData.hm7_0_0_13.s2`, `OAI.SharpPlanar.CachedData.hm7_0_0_13.s3`, `OAI.SharpPlanar.CachedData.hm7_0_0_13.s4`, `OAI.SharpPlanar.CachedData.hm7_0_0_13.sums`, `OAI.SharpPlanar.CachedData.hm7_0_1_13.s0`, `OAI.SharpPlanar.CachedData.hm7_0_1_13.sums`, `OAI.SharpPlanar.CachedData.hm7_1_0_12.s1`, `OAI.SharpPlanar.CachedData.hm7_1_0_12.s2`, `OAI.SharpPlanar.CachedData.hm7_1_0_12.s3`, `OAI.SharpPlanar.CachedData.hm7_1_0_12.s4`, `OAI.SharpPlanar.CachedData.hm7_1_0_12.sums`, `OAI.SharpPlanar.CachedData.hm7_1_1_12.s0`, `OAI.SharpPlanar.CachedData.hm7_1_1_12.s1`, `OAI.SharpPlanar.CachedData.hm7_1_1_12.s2`, `OAI.SharpPlanar.CachedData.hm7_1_1_12.sums`, `OAI.SharpPlanar.CachedData.hm7_1_1_13.s0`, `OAI.SharpPlanar.CachedData.hm7_1_1_13.sums`, `OAI.SharpPlanar.CachedData.hm9_0_0_12.s0`, `OAI.SharpPlanar.CachedData.hm9_0_0_12.s1`, `OAI.SharpPlanar.CachedData.hm9_0_0_12.sums`, `OAI.SharpPlanar.CachedData.hm9_0_1_11.s0`, `OAI.SharpPlanar.CachedData.hm9_0_1_11.s1`, `OAI.SharpPlanar.CachedData.hm9_0_1_11.s2`, `OAI.SharpPlanar.CachedData.hm9_0_1_11.s3`, `OAI.SharpPlanar.CachedData.hm9_0_1_11.sums`, `OAI.SharpPlanar.CachedData.hm9_1_0_10.s0`, `OAI.SharpPlanar.CachedData.hm9_1_0_10.sums`, `OAI.SharpPlanar.CachedData.hm9_1_0_11.s0`, `OAI.SharpPlanar.CachedData.hm9_1_0_11.s1`, `OAI.SharpPlanar.CachedData.hm9_1_0_11.s2`, `OAI.SharpPlanar.CachedData.hm9_1_0_11.s3` and 93 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_Certificate_KernelValues100`, `PlanarPacking_Certificate_KernelValues40`, `PlanarPacking_Certificate_KernelValues50`, `PlanarPacking_Certificate_KernelValues60`, `PlanarPacking_Certificate_KernelValues70`, `PlanarPacking_Certificate_KernelValues80`, `PlanarPacking_Certificate_KernelValues90`, `PlanarPacking_Certificate_LowBlock4_10`, `PlanarPacking_Certificate_LowBlock4_11`, `PlanarPacking_Certificate_LowBlock4_12`, `PlanarPacking_Certificate_LowBlock7_0`, `PlanarPacking_Certificate_LowBlock7_1`, `PlanarPacking_Certificate_LowBlock7_10`, `PlanarPacking_Certificate_LowBlock7_11`, `PlanarPacking_Certificate_LowBlock7_12`, `PlanarPacking_Certificate_LowBlock7_2`, `PlanarPacking_Certificate_LowBlock9_0`, `PlanarPacking_Certificate_LowBlock9_1`, `PlanarPacking_Certificate_LowBlock9_10`, `PlanarPacking_Certificate_LowBlock9_11`, `PlanarPacking_Certificate_LowBlock9_12`, `PlanarPacking_Certificate_LowBlock9_2`, `PlanarPacking_Certificate_TableMoments1`, `PlanarPacking_Certificate_TableMoments100`, `PlanarPacking_Certificate_TableMoments12`, `PlanarPacking_Certificate_TableMoments13`, `PlanarPacking_Certificate_TableMoments15`, `PlanarPacking_Certificate_TableMoments16`, `PlanarPacking_Certificate_TableMoments19`, `PlanarPacking_Certificate_TableMoments21`, `PlanarPacking_Certificate_TableMoments24`, `PlanarPacking_Certificate_TableMoments25`, `PlanarPacking_Certificate_TableMoments27`, `PlanarPacking_Certificate_TableMoments28`, `PlanarPacking_Certificate_TableMoments3`, `PlanarPacking_Certificate_TableMoments31`, `PlanarPacking_Certificate_TableMoments33`, `PlanarPacking_Certificate_TableMoments36`, `PlanarPacking_Certificate_TableMoments37`, `PlanarPacking_Certificate_TableMoments39`, `PlanarPacking_Certificate_TableMoments4`, `PlanarPacking_Certificate_TableMoments40`, `PlanarPacking_Certificate_TableMoments43`, `PlanarPacking_Certificate_TableMoments45`, `PlanarPacking_Certificate_TableMoments48`, `PlanarPacking_Certificate_TableMoments49`, `PlanarPacking_Certificate_TableMoments51`, `PlanarPacking_Certificate_TableMoments52`, `PlanarPacking_Certificate_TableMoments55`, `PlanarPacking_Certificate_TableMoments57`, `PlanarPacking_Certificate_TableMoments60`, `PlanarPacking_Certificate_TableMoments61`, `PlanarPacking_Certificate_TableMoments63`, `PlanarPacking_Certificate_TableMoments64`, `PlanarPacking_Certificate_TableMoments67`, `PlanarPacking_Certificate_TableMoments69`, `PlanarPacking_Certificate_TableMoments7`, `PlanarPacking_Certificate_TableMoments72`, `PlanarPacking_Certificate_TableMoments73`, `PlanarPacking_Certificate_TableMoments75`, `PlanarPacking_Certificate_TableMoments76`, `PlanarPacking_Certificate_TableMoments79`, `PlanarPacking_Certificate_TableMoments81`, `PlanarPacking_Certificate_TableMoments84`, `PlanarPacking_Certificate_TableMoments85`, `PlanarPacking_Certificate_TableMoments87`, `PlanarPacking_Certificate_TableMoments88`, `PlanarPacking_Certificate_TableMoments9`, `PlanarPacking_Certificate_TableMoments91`, `PlanarPacking_Certificate_TableMoments93`, `PlanarPacking_Certificate_TableMoments96`, `PlanarPacking_Certificate_TableMoments97`, `PlanarPacking_Certificate_TableMoments99`, `PlanarPacking_Certificate_TransformedPowers100`, `PlanarPacking_Certificate_TransformedPowers30`, `PlanarPacking_Certificate_TransformedPowers40`, `PlanarPacking_Certificate_TransformedPowers50`, `PlanarPacking_Certificate_TransformedPowers60`, `PlanarPacking_Certificate_TransformedPowers70`, `PlanarPacking_Certificate_TransformedPowers80`, `PlanarPacking_Certificate_TransformedPowers90`.
--
--   **Imports.** It imports the bundles `OAIQ098D041`, `OAIQ098D126`, `OAIQ098D130`, `OAIQ098D160`, `OAIQ098D197`, `OAIQ098D222`, `OAIQ098D223`, `OAIQ098D224`, `OAIQ098D225`, `OAIQ098D226`, `OAIQ098D227`, `OAIQ098D228`, `OAIQ098D229`, `OAIQ098D230`, `OAIQ098D231`, `OAIQ098D232`, `OAIQ098D233`, `OAIQ098D234`, `OAIQ098D235`, `OAIQ098D236`, `OAIQ098D237`, `OAIQ098D238`, `OAIQ098D239`, `OAIQ098D240`, `OAIQ098D241`, `OAIQ098D242`, `OAIQ098D243`, `OAIQ098D244`, `OAIQ098D245`, `OAIQ098D246`, `OAIQ098D247`, `OAIQ098D248`, `OAIQ098D249`, `OAIQ098D250`, `OAIQ098D251`, `OAIQ098D252` and `OAIQ098D253` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098D358`, `OAIQ098D363`, `OAIQ098D421`, `OAIQ098D427`, `OAIQ098D430`, `OAIQ098D443`, `OAIQ098D445`, `OAIQ098D447`, `OAIQ098D448`, `OAIQ098D449`, `OAIQ098D450`, `OAIQ098D451`, `OAIQ098D452`, `OAIQ098D453`, `OAIQ098D457`, `OAIQ098D458`, `OAIQ098D459`, `OAIQ098D460`, `OAIQ098D461`, `OAIQ098D462`, `OAIQ098D463`, `OAIQ098D464`, `OAIQ098D465`, `OAIQ098D466`, `OAIQ098D491`, `OAIQ098D497`, `OAIQ098D504`, `OAIQ098D521`, `OAIQ098D529`, `OAIQ098D538`, `OAIQ098D540`, `OAIQ098D554`, `OAIQ098D555`, `OAIQ098D556`, `OAIQ098D580`, `OAIQ098D586`, `OAIQ098D598`, `OAIQ098D600`, `OAIQ098D601` and `OAIQ098D602`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098D041
import Definitions.Def_OAIQ098D126
import Definitions.Def_OAIQ098D130
import Definitions.Def_OAIQ098D160
import Definitions.Def_OAIQ098D197
import Definitions.Def_OAIQ098D222
import Definitions.Def_OAIQ098D223
import Definitions.Def_OAIQ098D224
import Definitions.Def_OAIQ098D225
import Definitions.Def_OAIQ098D226
import Definitions.Def_OAIQ098D227
import Definitions.Def_OAIQ098D228
import Definitions.Def_OAIQ098D229
import Definitions.Def_OAIQ098D230
import Definitions.Def_OAIQ098D231
import Definitions.Def_OAIQ098D232
import Definitions.Def_OAIQ098D233
import Definitions.Def_OAIQ098D234
import Definitions.Def_OAIQ098D235
import Definitions.Def_OAIQ098D236
import Definitions.Def_OAIQ098D237
import Definitions.Def_OAIQ098D238
import Definitions.Def_OAIQ098D239
import Definitions.Def_OAIQ098D240
import Definitions.Def_OAIQ098D241
import Definitions.Def_OAIQ098D242
import Definitions.Def_OAIQ098D243
import Definitions.Def_OAIQ098D244
import Definitions.Def_OAIQ098D245
import Definitions.Def_OAIQ098D246
import Definitions.Def_OAIQ098D247
import Definitions.Def_OAIQ098D248
import Definitions.Def_OAIQ098D249
import Definitions.Def_OAIQ098D250
import Definitions.Def_OAIQ098D251
import Definitions.Def_OAIQ098D252
import Definitions.Def_OAIQ098D253

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers30
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
noncomputable def trans24_r3 : Fin 16 → Fin 16 → CBox := ![trans24_r3_0,trans24_r3_1,trans24_r3_2,trans24_r3_3,trans24_r3_4,trans24_r3_5,trans24_r3_6,trans24_r3_7,trans24_r3_8,trans24_r3_9,trans24_r3_10,trans24_r3_11,trans24_r3_12,trans24_r3_13,trans24_r3_14,trans24_r3_15]
noncomputable def trans24 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans24_r0,trans24_r1,trans24_r2,trans24_r3,trans24_r4,trans24_r5]
noncomputable def trans28_r3 : Fin 16 → Fin 16 → CBox := ![trans28_r3_0,trans28_r3_1,trans28_r3_2,trans28_r3_3,trans28_r3_4,trans28_r3_5,trans28_r3_6,trans28_r3_7,trans28_r3_8,trans28_r3_9,trans28_r3_10,trans28_r3_11,trans28_r3_12,trans28_r3_13,trans28_r3_14,trans28_r3_15]
noncomputable def trans28 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans28_r0,trans28_r1,trans28_r2,trans28_r3,trans28_r4,trans28_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers40
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
noncomputable def trans36_r5 : Fin 16 → Fin 16 → CBox := ![trans36_r5_0,trans36_r5_1,trans36_r5_2,trans36_r5_3,trans36_r5_4,trans36_r5_5,trans36_r5_6,trans36_r5_7,trans36_r5_8,trans36_r5_9,trans36_r5_10,trans36_r5_11,trans36_r5_12,trans36_r5_13,trans36_r5_14,trans36_r5_15]
noncomputable def trans36 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans36_r0,trans36_r1,trans36_r2,trans36_r3,trans36_r4,trans36_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers50
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
noncomputable def trans48_r0 : Fin 16 → Fin 16 → CBox := ![trans48_r0_0,trans48_r0_1,trans48_r0_2,trans48_r0_3,trans48_r0_4,trans48_r0_5,trans48_r0_6,trans48_r0_7,trans48_r0_8,trans48_r0_9,trans48_r0_10,trans48_r0_11,trans48_r0_12,trans48_r0_13,trans48_r0_14,trans48_r0_15]
noncomputable def trans48 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans48_r0,trans48_r1,trans48_r2,trans48_r3,trans48_r4,trans48_r5]
end SharpPlanar.CachedData

end OAI
end

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
noncomputable def trans57_r3 : Fin 16 → Fin 16 → CBox := ![trans57_r3_0,trans57_r3_1,trans57_r3_2,trans57_r3_3,trans57_r3_4,trans57_r3_5,trans57_r3_6,trans57_r3_7,trans57_r3_8,trans57_r3_9,trans57_r3_10,trans57_r3_11,trans57_r3_12,trans57_r3_13,trans57_r3_14,trans57_r3_15]
noncomputable def trans57 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans57_r0,trans57_r1,trans57_r2,trans57_r3,trans57_r4,trans57_r5]
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
noncomputable def trans67_r4 : Fin 16 → Fin 16 → CBox := ![trans67_r4_0,trans67_r4_1,trans67_r4_2,trans67_r4_3,trans67_r4_4,trans67_r4_5,trans67_r4_6,trans67_r4_7,trans67_r4_8,trans67_r4_9,trans67_r4_10,trans67_r4_11,trans67_r4_12,trans67_r4_13,trans67_r4_14,trans67_r4_15]
noncomputable def trans67 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans67_r0,trans67_r1,trans67_r2,trans67_r3,trans67_r4,trans67_r5]
noncomputable def trans69_r0 : Fin 16 → Fin 16 → CBox := ![trans69_r0_0,trans69_r0_1,trans69_r0_2,trans69_r0_3,trans69_r0_4,trans69_r0_5,trans69_r0_6,trans69_r0_7,trans69_r0_8,trans69_r0_9,trans69_r0_10,trans69_r0_11,trans69_r0_12,trans69_r0_13,trans69_r0_14,trans69_r0_15]
noncomputable def trans69 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans69_r0,trans69_r1,trans69_r2,trans69_r3,trans69_r4,trans69_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers80
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
noncomputable def trans73_r1 : Fin 16 → Fin 16 → CBox := ![trans73_r1_0,trans73_r1_1,trans73_r1_2,trans73_r1_3,trans73_r1_4,trans73_r1_5,trans73_r1_6,trans73_r1_7,trans73_r1_8,trans73_r1_9,trans73_r1_10,trans73_r1_11,trans73_r1_12,trans73_r1_13,trans73_r1_14,trans73_r1_15]
noncomputable def trans73 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans73_r0,trans73_r1,trans73_r2,trans73_r3,trans73_r4,trans73_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers90
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
noncomputable def trans84_r0 : Fin 16 → Fin 16 → CBox := ![trans84_r0_0,trans84_r0_1,trans84_r0_2,trans84_r0_3,trans84_r0_4,trans84_r0_5,trans84_r0_6,trans84_r0_7,trans84_r0_8,trans84_r0_9,trans84_r0_10,trans84_r0_11,trans84_r0_12,trans84_r0_13,trans84_r0_14,trans84_r0_15]
noncomputable def trans84 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans84_r0,trans84_r1,trans84_r2,trans84_r3,trans84_r4,trans84_r5]
noncomputable def trans87_r4 : Fin 16 → Fin 16 → CBox := ![trans87_r4_0,trans87_r4_1,trans87_r4_2,trans87_r4_3,trans87_r4_4,trans87_r4_5,trans87_r4_6,trans87_r4_7,trans87_r4_8,trans87_r4_9,trans87_r4_10,trans87_r4_11,trans87_r4_12,trans87_r4_13,trans87_r4_14,trans87_r4_15]
noncomputable def trans87 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans87_r0,trans87_r1,trans87_r2,trans87_r3,trans87_r4,trans87_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TransformedPowers100
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
noncomputable def trans97_r3 : Fin 16 → Fin 16 → CBox := ![trans97_r3_0,trans97_r3_1,trans97_r3_2,trans97_r3_3,trans97_r3_4,trans97_r3_5,trans97_r3_6,trans97_r3_7,trans97_r3_8,trans97_r3_9,trans97_r3_10,trans97_r3_11,trans97_r3_12,trans97_r3_13,trans97_r3_14,trans97_r3_15]
noncomputable def trans97_r5 : Fin 16 → Fin 16 → CBox := ![trans97_r5_0,trans97_r5_1,trans97_r5_2,trans97_r5_3,trans97_r5_4,trans97_r5_5,trans97_r5_6,trans97_r5_7,trans97_r5_8,trans97_r5_9,trans97_r5_10,trans97_r5_11,trans97_r5_12,trans97_r5_13,trans97_r5_14,trans97_r5_15]
noncomputable def trans97 : Fin 6 → Fin 16 → Fin 16 → CBox := ![trans97_r0,trans97_r1,trans97_r2,trans97_r3,trans97_r4,trans97_r5]
end SharpPlanar.CachedData

end OAI
end

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
noncomputable def kernel91_1_r5 : Fin 16 → Fin 16 → CBox := ![kernel91_1_r5_0,kernel91_1_r5_1,kernel91_1_r5_2,kernel91_1_r5_3,kernel91_1_r5_4,kernel91_1_r5_5,kernel91_1_r5_6,kernel91_1_r5_7,kernel91_1_r5_8,kernel91_1_r5_9,kernel91_1_r5_10,kernel91_1_r5_11,kernel91_1_r5_12,kernel91_1_r5_13,kernel91_1_r5_14,kernel91_1_r5_15]
noncomputable def kernel91_1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel91_1_r0,kernel91_1_r1,kernel91_1_r2,kernel91_1_r3,kernel91_1_r4,kernel91_1_r5]
noncomputable def kernel100_0_r5 : Fin 16 → Fin 16 → CBox := ![kernel100_0_r5_0,kernel100_0_r5_1,kernel100_0_r5_2,kernel100_0_r5_3,kernel100_0_r5_4,kernel100_0_r5_5,kernel100_0_r5_6,kernel100_0_r5_7,kernel100_0_r5_8,kernel100_0_r5_9,kernel100_0_r5_10,kernel100_0_r5_11,kernel100_0_r5_12,kernel100_0_r5_13,kernel100_0_r5_14,kernel100_0_r5_15]
noncomputable def kernel100_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel100_0_r0,kernel100_0_r1,kernel100_0_r2,kernel100_0_r3,kernel100_0_r4,kernel100_0_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues40
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
noncomputable def kernel40_1_r4 : Fin 16 → Fin 16 → CBox := ![kernel40_1_r4_0,kernel40_1_r4_1,kernel40_1_r4_2,kernel40_1_r4_3,kernel40_1_r4_4,kernel40_1_r4_5,kernel40_1_r4_6,kernel40_1_r4_7,kernel40_1_r4_8,kernel40_1_r4_9,kernel40_1_r4_10,kernel40_1_r4_11,kernel40_1_r4_12,kernel40_1_r4_13,kernel40_1_r4_14,kernel40_1_r4_15]
noncomputable def kernel40_1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel40_1_r0,kernel40_1_r1,kernel40_1_r2,kernel40_1_r3,kernel40_1_r4,kernel40_1_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues50
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
noncomputable def kernel43_0_r0 : Fin 16 → Fin 16 → CBox := ![kernel43_0_r0_0,kernel43_0_r0_1,kernel43_0_r0_2,kernel43_0_r0_3,kernel43_0_r0_4,kernel43_0_r0_5,kernel43_0_r0_6,kernel43_0_r0_7,kernel43_0_r0_8,kernel43_0_r0_9,kernel43_0_r0_10,kernel43_0_r0_11,kernel43_0_r0_12,kernel43_0_r0_13,kernel43_0_r0_14,kernel43_0_r0_15]
noncomputable def kernel43_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel43_0_r0,kernel43_0_r1,kernel43_0_r2,kernel43_0_r3,kernel43_0_r4,kernel43_0_r5]
noncomputable def kernel48_0_r5 : Fin 16 → Fin 16 → CBox := ![kernel48_0_r5_0,kernel48_0_r5_1,kernel48_0_r5_2,kernel48_0_r5_3,kernel48_0_r5_4,kernel48_0_r5_5,kernel48_0_r5_6,kernel48_0_r5_7,kernel48_0_r5_8,kernel48_0_r5_9,kernel48_0_r5_10,kernel48_0_r5_11,kernel48_0_r5_12,kernel48_0_r5_13,kernel48_0_r5_14,kernel48_0_r5_15]
noncomputable def kernel48_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel48_0_r0,kernel48_0_r1,kernel48_0_r2,kernel48_0_r3,kernel48_0_r4,kernel48_0_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues60
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
noncomputable def kernel51_1_r4 : Fin 16 → Fin 16 → CBox := ![kernel51_1_r4_0,kernel51_1_r4_1,kernel51_1_r4_2,kernel51_1_r4_3,kernel51_1_r4_4,kernel51_1_r4_5,kernel51_1_r4_6,kernel51_1_r4_7,kernel51_1_r4_8,kernel51_1_r4_9,kernel51_1_r4_10,kernel51_1_r4_11,kernel51_1_r4_12,kernel51_1_r4_13,kernel51_1_r4_14,kernel51_1_r4_15]
noncomputable def kernel51_1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel51_1_r0,kernel51_1_r1,kernel51_1_r2,kernel51_1_r3,kernel51_1_r4,kernel51_1_r5]
noncomputable def kernel60_0_r4 : Fin 16 → Fin 16 → CBox := ![kernel60_0_r4_0,kernel60_0_r4_1,kernel60_0_r4_2,kernel60_0_r4_3,kernel60_0_r4_4,kernel60_0_r4_5,kernel60_0_r4_6,kernel60_0_r4_7,kernel60_0_r4_8,kernel60_0_r4_9,kernel60_0_r4_10,kernel60_0_r4_11,kernel60_0_r4_12,kernel60_0_r4_13,kernel60_0_r4_14,kernel60_0_r4_15]
noncomputable def kernel60_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel60_0_r0,kernel60_0_r1,kernel60_0_r2,kernel60_0_r3,kernel60_0_r4,kernel60_0_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues70
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
noncomputable def kernel63_0_r3 : Fin 16 → Fin 16 → CBox := ![kernel63_0_r3_0,kernel63_0_r3_1,kernel63_0_r3_2,kernel63_0_r3_3,kernel63_0_r3_4,kernel63_0_r3_5,kernel63_0_r3_6,kernel63_0_r3_7,kernel63_0_r3_8,kernel63_0_r3_9,kernel63_0_r3_10,kernel63_0_r3_11,kernel63_0_r3_12,kernel63_0_r3_13,kernel63_0_r3_14,kernel63_0_r3_15]
noncomputable def kernel63_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel63_0_r0,kernel63_0_r1,kernel63_0_r2,kernel63_0_r3,kernel63_0_r4,kernel63_0_r5]
noncomputable def kernel67_1_r3 : Fin 16 → Fin 16 → CBox := ![kernel67_1_r3_0,kernel67_1_r3_1,kernel67_1_r3_2,kernel67_1_r3_3,kernel67_1_r3_4,kernel67_1_r3_5,kernel67_1_r3_6,kernel67_1_r3_7,kernel67_1_r3_8,kernel67_1_r3_9,kernel67_1_r3_10,kernel67_1_r3_11,kernel67_1_r3_12,kernel67_1_r3_13,kernel67_1_r3_14,kernel67_1_r3_15]
noncomputable def kernel67_1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel67_1_r0,kernel67_1_r1,kernel67_1_r2,kernel67_1_r3,kernel67_1_r4,kernel67_1_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues80
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
noncomputable def kernel76_1_r5 : Fin 16 → Fin 16 → CBox := ![kernel76_1_r5_0,kernel76_1_r5_1,kernel76_1_r5_2,kernel76_1_r5_3,kernel76_1_r5_4,kernel76_1_r5_5,kernel76_1_r5_6,kernel76_1_r5_7,kernel76_1_r5_8,kernel76_1_r5_9,kernel76_1_r5_10,kernel76_1_r5_11,kernel76_1_r5_12,kernel76_1_r5_13,kernel76_1_r5_14,kernel76_1_r5_15]
noncomputable def kernel76_1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel76_1_r0,kernel76_1_r1,kernel76_1_r2,kernel76_1_r3,kernel76_1_r4,kernel76_1_r5]
noncomputable def kernel79_0_r0 : Fin 16 → Fin 16 → CBox := ![kernel79_0_r0_0,kernel79_0_r0_1,kernel79_0_r0_2,kernel79_0_r0_3,kernel79_0_r0_4,kernel79_0_r0_5,kernel79_0_r0_6,kernel79_0_r0_7,kernel79_0_r0_8,kernel79_0_r0_9,kernel79_0_r0_10,kernel79_0_r0_11,kernel79_0_r0_12,kernel79_0_r0_13,kernel79_0_r0_14,kernel79_0_r0_15]
noncomputable def kernel79_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel79_0_r0,kernel79_0_r1,kernel79_0_r2,kernel79_0_r3,kernel79_0_r4,kernel79_0_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues90
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
noncomputable def kernel84_0_r5 : Fin 16 → Fin 16 → CBox := ![kernel84_0_r5_0,kernel84_0_r5_1,kernel84_0_r5_2,kernel84_0_r5_3,kernel84_0_r5_4,kernel84_0_r5_5,kernel84_0_r5_6,kernel84_0_r5_7,kernel84_0_r5_8,kernel84_0_r5_9,kernel84_0_r5_10,kernel84_0_r5_11,kernel84_0_r5_12,kernel84_0_r5_13,kernel84_0_r5_14,kernel84_0_r5_15]
noncomputable def kernel84_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel84_0_r0,kernel84_0_r1,kernel84_0_r2,kernel84_0_r3,kernel84_0_r4,kernel84_0_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock4_10
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm4_1_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_1_2
namespace hm4_1_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_1_3
namespace hm4_1_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_1_4
namespace hm4_1_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_1_5
namespace hm4_1_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_1_6
namespace hm4_1_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock4_11
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm4_1_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_1_8
namespace hm4_1_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_1_9
namespace hm4_1_1_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_1_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock4_12
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm4_1_1_14
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_1_14
namespace hm4_1_1_15
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_1_15
namespace hm4_1_1_16
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_1_16
namespace hm4_1_1_17
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_1_17
namespace hm4_1_1_18
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_1_18
namespace hm4_1_1_19
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm4_1_1_19
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock7_0
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm7_0_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_0_2
namespace hm7_1_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_0_2
namespace hm7_0_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_0_3
namespace hm7_1_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_0_3
namespace hm7_0_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_0_4
namespace hm7_1_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_0_4
namespace hm7_0_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_0_5
namespace hm7_1_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_0_5
namespace hm7_0_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_0_6
namespace hm7_1_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_0_6
namespace hm7_0_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_0_7
namespace hm7_1_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock7_1
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm7_0_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_0_8
namespace hm7_1_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_0_8
namespace hm7_0_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_0_9
namespace hm7_1_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_0_9
namespace hm7_0_0_10
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_0_10
namespace hm7_1_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_0_10
namespace hm7_0_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_0_11
namespace hm7_1_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_0_11
namespace hm7_0_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_0_12
namespace hm7_1_0_12
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_0_12
namespace hm7_0_0_13
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_0_13
namespace hm7_1_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_0_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock7_10
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm7_0_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_1_2
namespace hm7_1_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_1_2
namespace hm7_0_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_1_3
namespace hm7_1_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_1_3
namespace hm7_0_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_1_4
namespace hm7_1_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_1_4
namespace hm7_0_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_1_5
namespace hm7_1_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_1_5
namespace hm7_0_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_1_6
namespace hm7_1_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_1_6
namespace hm7_0_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_1_7
namespace hm7_1_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock7_11
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm7_0_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_1_8
namespace hm7_1_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_1_8
namespace hm7_0_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_1_9
namespace hm7_1_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_1_9
namespace hm7_0_1_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_1_10
namespace hm7_1_1_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_1_10
namespace hm7_0_1_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_1_11
namespace hm7_1_1_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_1_11
namespace hm7_0_1_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_1_12
namespace hm7_1_1_12
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_1_12
namespace hm7_0_1_13
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_1_13
namespace hm7_1_1_13
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_1_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock7_12
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm7_0_1_14
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_1_14
namespace hm7_1_1_14
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_1_14
namespace hm7_0_1_15
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_1_15
namespace hm7_1_1_15
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_1_15
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock7_2
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm7_0_0_14
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_0_14
namespace hm7_1_0_14
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_0_14
namespace hm7_0_0_15
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_0_0_15
namespace hm7_1_0_15
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm7_1_0_15
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock9_0
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm9_0_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_0_2
namespace hm9_1_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_0_2
namespace hm9_0_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_0_3
namespace hm9_1_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_0_3
namespace hm9_0_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_0_4
namespace hm9_1_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_0_4
namespace hm9_0_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_0_5
namespace hm9_1_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_0_5
namespace hm9_0_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_0_6
namespace hm9_1_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_0_6
namespace hm9_0_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_0_7
namespace hm9_1_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock9_1
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm9_0_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_0_8
namespace hm9_1_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_0_8
namespace hm9_0_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_0_9
namespace hm9_1_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_0_9
namespace hm9_0_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_0_10
namespace hm9_1_0_10
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_0_10
namespace hm9_0_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_0_11
namespace hm9_1_0_11
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_0_11
namespace hm9_0_0_12
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_0_12
namespace hm9_1_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_0_12
namespace hm9_0_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_0_13
namespace hm9_1_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_0_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock9_10
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm9_0_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_1_2
namespace hm9_1_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_1_2
namespace hm9_0_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_1_3
namespace hm9_1_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_1_3
namespace hm9_0_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_1_4
namespace hm9_1_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_1_4
namespace hm9_0_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_1_5
namespace hm9_1_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_1_5
namespace hm9_0_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_1_6
namespace hm9_1_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_1_6
namespace hm9_0_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_1_7
namespace hm9_1_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock9_11
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm9_0_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_1_8
namespace hm9_1_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_1_8
namespace hm9_0_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_1_9
namespace hm9_1_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_1_9
namespace hm9_0_1_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_1_10
namespace hm9_1_1_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_1_10
namespace hm9_0_1_11
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_1_11
namespace hm9_1_1_11
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_1_11
namespace hm9_0_1_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_1_12
namespace hm9_1_1_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_1_12
namespace hm9_0_1_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_1_13
namespace hm9_1_1_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_1_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock9_12
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm9_0_1_14
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_1_14
namespace hm9_1_1_14
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_1_14
namespace hm9_0_1_15
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_1_15
namespace hm9_1_1_15
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_1_15
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock9_2
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm9_0_0_14
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_0_14
namespace hm9_1_0_14
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_0_14
namespace hm9_0_0_15
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_0_0_15
namespace hm9_1_0_15
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm9_1_0_15
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments1
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_1_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_1_0

namespace tm0_1_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_1_1

namespace tm1_1_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_1_0

namespace tm1_1_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_1_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments100
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_100_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_100_0

namespace tm0_100_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_100_1

namespace tm1_100_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_100_0

namespace tm1_100_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_100_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments12
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_12_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_12_0

namespace tm0_12_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_12_1

namespace tm1_12_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_12_0

namespace tm1_12_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_12_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments13
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_13_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_13_0

namespace tm0_13_1
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_13_1

namespace tm1_13_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_13_0

namespace tm1_13_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_13_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments15
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_15_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_15_0

namespace tm0_15_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_15_1

namespace tm1_15_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_15_0

namespace tm1_15_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_15_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments16
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_16_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_16_0

namespace tm0_16_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_16_1

namespace tm1_16_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_16_0

namespace tm1_16_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_16_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments19
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_19_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_19_0

namespace tm0_19_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_19_1

namespace tm1_19_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_19_0

namespace tm1_19_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_19_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments21
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_21_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_21_0

namespace tm0_21_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_21_1

namespace tm1_21_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_21_0

namespace tm1_21_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_21_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments24
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_24_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_24_0

namespace tm0_24_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_24_1

namespace tm1_24_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_24_0

namespace tm1_24_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_24_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments25
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_25_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_25_0

namespace tm0_25_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_25_1

namespace tm1_25_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_25_0

namespace tm1_25_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_25_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments27
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_27_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_27_0

namespace tm0_27_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_27_1

namespace tm1_27_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_27_0

namespace tm1_27_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_27_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments28
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_28_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_28_0

namespace tm0_28_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_28_1

namespace tm1_28_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_28_0

namespace tm1_28_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_28_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments3
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_3_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_3_0

namespace tm0_3_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_3_1

namespace tm1_3_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_3_0

namespace tm1_3_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_3_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments31
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_31_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_31_0

namespace tm0_31_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_31_1

namespace tm1_31_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_31_0

namespace tm1_31_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_31_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments33
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_33_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_33_0

namespace tm0_33_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_33_1

namespace tm1_33_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_33_0

namespace tm1_33_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_33_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments36
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_36_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_36_0

namespace tm0_36_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_36_1

namespace tm1_36_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_36_0

namespace tm1_36_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_36_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments37
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_37_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_37_0

namespace tm0_37_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_37_1

namespace tm1_37_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_37_0

namespace tm1_37_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_37_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments39
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_39_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_39_0

namespace tm0_39_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_39_1

namespace tm1_39_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_39_0

namespace tm1_39_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_39_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments4
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_4_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_4_0

namespace tm0_4_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_4_1

namespace tm1_4_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_4_0

namespace tm1_4_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_4_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments40
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_40_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_40_0

namespace tm0_40_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_40_1

namespace tm1_40_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_40_0

namespace tm1_40_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_40_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments43
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_43_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_43_0

namespace tm0_43_1
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_43_1

namespace tm1_43_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_43_0

namespace tm1_43_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_43_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments45
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_45_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_45_0

namespace tm0_45_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_45_1

namespace tm1_45_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_45_0

namespace tm1_45_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_45_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments48
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_48_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_48_0

namespace tm0_48_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_48_1

namespace tm1_48_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_48_0

namespace tm1_48_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_48_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments49
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_49_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_49_0

namespace tm0_49_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_49_1

namespace tm1_49_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_49_0

namespace tm1_49_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_49_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments51
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_51_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_51_0

namespace tm0_51_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_51_1

namespace tm1_51_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_51_0

namespace tm1_51_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_51_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments52
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_52_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_52_0

namespace tm0_52_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_52_1

namespace tm1_52_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_52_0

namespace tm1_52_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_52_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments55
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_55_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_55_0

namespace tm0_55_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_55_1

namespace tm1_55_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_55_0

namespace tm1_55_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_55_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments57
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_57_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_57_0

namespace tm0_57_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_57_1

namespace tm1_57_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_57_0

namespace tm1_57_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_57_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments60
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_60_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_60_0

namespace tm0_60_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_60_1

namespace tm1_60_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_60_0

namespace tm1_60_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_60_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments61
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_61_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_61_0

namespace tm0_61_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_61_1

namespace tm1_61_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_61_0

namespace tm1_61_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_61_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments63
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_63_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_63_0

namespace tm0_63_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_63_1

namespace tm1_63_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_63_0

namespace tm1_63_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_63_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments64
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_64_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_64_0

namespace tm0_64_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_64_1

namespace tm1_64_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_64_0

namespace tm1_64_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_64_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments67
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_67_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_67_0

namespace tm0_67_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_67_1

namespace tm1_67_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_67_0

namespace tm1_67_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_67_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments69
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_69_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_69_0

namespace tm0_69_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_69_1

namespace tm1_69_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_69_0

namespace tm1_69_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_69_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments7
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_7_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_7_0

namespace tm0_7_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_7_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments72
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_72_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_72_0

namespace tm0_72_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_72_1

namespace tm1_72_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_72_0

namespace tm1_72_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm1_72_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments73
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_73_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_73_0

namespace tm0_73_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_73_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments75
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_75_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_75_0

namespace tm0_75_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_75_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments76
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_76_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_76_0

namespace tm0_76_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_76_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments79
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_79_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_79_0

namespace tm0_79_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_79_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments81
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_81_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_81_0

namespace tm0_81_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_81_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments84
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_84_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_84_0

namespace tm0_84_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_84_1

namespace tm1_84_1
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
end tm1_84_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments85
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_85_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_85_0

namespace tm0_85_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_85_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments87
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_87_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_87_0

namespace tm0_87_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_87_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments88
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_88_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_88_0

namespace tm0_88_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_88_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments9
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_9_0
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_9_0

namespace tm0_9_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_9_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments91
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_91_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_91_0

namespace tm0_91_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_91_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments93
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_93_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_93_0

namespace tm0_93_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_93_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments96
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_96_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_96_0

namespace tm0_96_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_96_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments97
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_97_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_97_0

namespace tm0_97_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_97_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableMoments99
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_99_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_99_0

namespace tm0_99_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end tm0_99_1

end SharpPlanar.CachedData

end OAI
end


