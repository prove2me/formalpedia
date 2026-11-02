-- Prove2me | Definitions.Def_OAIQ098D270
-- name    : OAIQ098D270
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T16:56:02.814723+00:00
-- url     : https://prove2.me/theorems/145058fc-d35f-4ae3-8570-d10a5e9e3673
-- title:
--   Definitions bundle OAIQ098D270 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 711 declarations of OpenAI's Lean: 493 definitions and 218 theorems. The definitions and types are `OAI.SharpPlanar.CachedData.density0`, `OAI.SharpPlanar.CachedData.density0_r0`, `OAI.SharpPlanar.CachedData.density0_r1`, `OAI.SharpPlanar.CachedData.density0_r2`, `OAI.SharpPlanar.CachedData.density0_r3`, `OAI.SharpPlanar.CachedData.density0_r4`, `OAI.SharpPlanar.CachedData.density0_r5`, `OAI.SharpPlanar.CachedData.density1`, `OAI.SharpPlanar.CachedData.density1_r0`, `OAI.SharpPlanar.CachedData.density1_r1`, `OAI.SharpPlanar.CachedData.density1_r2`, `OAI.SharpPlanar.CachedData.density1_r3`, `OAI.SharpPlanar.CachedData.density1_r4`, `OAI.SharpPlanar.CachedData.density1_r5`, `OAI.SharpPlanar.CachedData.hk0_1_1`, `OAI.SharpPlanar.CachedData.hk0_1_10`, `OAI.SharpPlanar.CachedData.hk0_1_11`, `OAI.SharpPlanar.CachedData.hk0_1_12`, `OAI.SharpPlanar.CachedData.hk0_1_13`, `OAI.SharpPlanar.CachedData.hk0_1_14`, `OAI.SharpPlanar.CachedData.hk0_1_15`, `OAI.SharpPlanar.CachedData.hk0_1_16`, `OAI.SharpPlanar.CachedData.hk0_1_17`, `OAI.SharpPlanar.CachedData.hk0_1_18`, `OAI.SharpPlanar.CachedData.hk0_1_19`, `OAI.SharpPlanar.CachedData.hk0_1_2`, `OAI.SharpPlanar.CachedData.hk0_1_20`, `OAI.SharpPlanar.CachedData.hk0_1_21`, `OAI.SharpPlanar.CachedData.hk0_1_22`, `OAI.SharpPlanar.CachedData.hk0_1_23`, `OAI.SharpPlanar.CachedData.hk0_1_24`, `OAI.SharpPlanar.CachedData.hk0_1_25`, `OAI.SharpPlanar.CachedData.hk0_1_26`, `OAI.SharpPlanar.CachedData.hk0_1_27`, `OAI.SharpPlanar.CachedData.hk0_1_28`, `OAI.SharpPlanar.CachedData.hk0_1_3`, `OAI.SharpPlanar.CachedData.hk0_1_4`, `OAI.SharpPlanar.CachedData.hk0_1_5`, `OAI.SharpPlanar.CachedData.hk0_1_6`, `OAI.SharpPlanar.CachedData.hk0_1_7` and 453 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_Certificate_HighHeaders0`, `PlanarPacking_Certificate_HighHeaders1`, `PlanarPacking_Certificate_HighHeaders12`, `PlanarPacking_Certificate_HighHeaders13`, `PlanarPacking_Certificate_HighHeaders15`, `PlanarPacking_Certificate_HighHeaders16`, `PlanarPacking_Certificate_HighHeaders19`, `PlanarPacking_Certificate_HighHeaders21`, `PlanarPacking_Certificate_HighHeaders24`, `PlanarPacking_Certificate_HighHeaders25`, `PlanarPacking_Certificate_HighHeaders27`, `PlanarPacking_Certificate_HighHeaders28`, `PlanarPacking_Certificate_HighHeaders3`, `PlanarPacking_Certificate_HighHeaders31`, `PlanarPacking_Certificate_HighHeaders33`, `PlanarPacking_Certificate_HighHeaders36`, `PlanarPacking_Certificate_HighHeaders37`, `PlanarPacking_Certificate_HighHeaders39`, `PlanarPacking_Certificate_HighHeaders4`, `PlanarPacking_Certificate_HighHeaders40`, `PlanarPacking_Certificate_HighHeaders7`, `PlanarPacking_Certificate_HighHeaders9`, `PlanarPacking_Certificate_HighMoments0_0`, `PlanarPacking_Certificate_HighMoments0_1`, `PlanarPacking_Certificate_HighMoments0_2`, `PlanarPacking_Certificate_HighMoments0_3`, `PlanarPacking_Certificate_HighMoments0_4`, `PlanarPacking_Certificate_HighMoments0_5`, `PlanarPacking_Certificate_HighMoments0_6`, `PlanarPacking_Certificate_HighMoments0_7`, `PlanarPacking_Certificate_KernelValues10`, `PlanarPacking_Certificate_KernelValues20`, `PlanarPacking_Certificate_KernelValues30`, `PlanarPacking_Certificate_KernelValues40`, `PlanarPacking_Certificate_LowBlock12_0`, `PlanarPacking_Certificate_LowBlock12_1`, `PlanarPacking_Certificate_LowBlock12_10`, `PlanarPacking_Certificate_LowBlock12_11`, `PlanarPacking_Certificate_LowBlock13_0`, `PlanarPacking_Certificate_LowBlock13_1`, `PlanarPacking_Certificate_LowBlock13_10`, `PlanarPacking_Certificate_LowBlock13_11`, `PlanarPacking_Certificate_LowBlock15_0`, `PlanarPacking_Certificate_LowBlock15_1`, `PlanarPacking_Certificate_LowBlock15_10`, `PlanarPacking_Certificate_LowBlock15_11`, `PlanarPacking_Certificate_LowBlock16_0`, `PlanarPacking_Certificate_LowBlock16_1`, `PlanarPacking_Certificate_LowBlock16_11`, `PlanarPacking_Certificate_MomentPowers10`, `PlanarPacking_Certificate_MomentPowers15`, `PlanarPacking_Certificate_MomentPowers20`, `PlanarPacking_Certificate_MomentPowers25`, `PlanarPacking_Certificate_MomentPowers30`, `PlanarPacking_Certificate_MomentPowers5`, `PlanarPacking_Certificate_TableDensity0Panel0`, `PlanarPacking_Certificate_TableDensity0Panel1`, `PlanarPacking_Certificate_TableDensity0Panel2`, `PlanarPacking_Certificate_TableDensity0Panel3`, `PlanarPacking_Certificate_TableDensity0Panel4`, `PlanarPacking_Certificate_TableDensity0Panel5`, `PlanarPacking_Certificate_TableDensity1Panel0`, `PlanarPacking_Certificate_TableDensity1Panel1`, `PlanarPacking_Certificate_TableDensity1Panel2`, `PlanarPacking_Certificate_TableDensity1Panel3`, `PlanarPacking_Certificate_TableDensity1Panel4`, `PlanarPacking_Certificate_TableDensity1Panel5`, `PlanarPacking_Certificate_TableDensityValues`.
--
--   **Imports.** It imports the bundles `OAIQ098D041`, `OAIQ098D044`, `OAIQ098D045`, `OAIQ098D067`, `OAIQ098D068`, `OAIQ098D069`, `OAIQ098D070`, `OAIQ098D071`, `OAIQ098D072`, `OAIQ098D073`, `OAIQ098D075`, `OAIQ098D076`, `OAIQ098D078`, `OAIQ098D081`, `OAIQ098D082`, `OAIQ098D083`, `OAIQ098D088`, `OAIQ098D091`, `OAIQ098D092`, `OAIQ098D094`, `OAIQ098D099`, `OAIQ098D123`, `OAIQ098D124`, `OAIQ098D125`, `OAIQ098D126`, `OAIQ098D127`, `OAIQ098D128`, `OAIQ098D129`, `OAIQ098D130`, `OAIQ098D131`, `OAIQ098D132`, `OAIQ098D133`, `OAIQ098D134`, `OAIQ098D135`, `OAIQ098D136`, `OAIQ098D137`, `OAIQ098D138`, `OAIQ098D139`, `OAIQ098D140`, `OAIQ098D141`, `OAIQ098D142`, `OAIQ098D143`, `OAIQ098D144`, `OAIQ098D145`, `OAIQ098D146`, `OAIQ098D147`, `OAIQ098D148`, `OAIQ098D149`, `OAIQ098D150`, `OAIQ098D151`, `OAIQ098D152`, `OAIQ098D153`, `OAIQ098D154`, `OAIQ098D155`, `OAIQ098D156`, `OAIQ098D157`, `OAIQ098D158`, `OAIQ098D159`, `OAIQ098D160`, `OAIQ098D161`, `OAIQ098D162`, `OAIQ098D163`, `OAIQ098D164`, `OAIQ098D165`, `OAIQ098D166`, `OAIQ098D167`, `OAIQ098D168`, `OAIQ098D169`, `OAIQ098D170` and `OAIQ098D171` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098D302`, `OAIQ098D308`, `OAIQ098D319`, `OAIQ098D321`, `OAIQ098D331`, `OAIQ098D335`, `OAIQ098D344`, `OAIQ098D348`, `OAIQ098D350`, `OAIQ098D351`, `OAIQ098D355`, `OAIQ098D356`, `OAIQ098D357`, `OAIQ098D358`, `OAIQ098D359`, `OAIQ098D360`, `OAIQ098D361`, `OAIQ098D362`, `OAIQ098D363`, `OAIQ098D364`, `OAIQ098D365`, `OAIQ098D366`, `OAIQ098D367`, `OAIQ098D368`, `OAIQ098D369`, `OAIQ098D370`, `OAIQ098D371`, `OAIQ098D372`, `OAIQ098D373`, `OAIQ098D374`, `OAIQ098D375`, `OAIQ098D376`, `OAIQ098D377`, `OAIQ098D378`, `OAIQ098D379`, `OAIQ098D380`, `OAIQ098D381`, `OAIQ098D382`, `OAIQ098D383`, `OAIQ098D384`, `OAIQ098D385`, `OAIQ098D386`, `OAIQ098D387`, `OAIQ098D388`, `OAIQ098D389`, `OAIQ098D390`, `OAIQ098D391`, `OAIQ098D392`, `OAIQ098D393`, `OAIQ098D394`, `OAIQ098D395`, `OAIQ098D396`, `OAIQ098D397`, `OAIQ098D398`, `OAIQ098D399`, `OAIQ098D400`, `OAIQ098D401`, `OAIQ098D402`, `OAIQ098D403`, `OAIQ098D404`, `OAIQ098D405`, `OAIQ098D406`, `OAIQ098D407`, `OAIQ098D408`, `OAIQ098D409`, `OAIQ098D410`, `OAIQ098D411`, `OAIQ098D412`, `OAIQ098D413`, `OAIQ098D414`, `OAIQ098D415`, `OAIQ098D416`, `OAIQ098D417`, `OAIQ098D418`, `OAIQ098D419`, `OAIQ098D420`, `OAIQ098D421`, `OAIQ098D422`, `OAIQ098D423`, `OAIQ098D424`, `OAIQ098D425`, `OAIQ098D426`, `OAIQ098D427`, `OAIQ098D428`, `OAIQ098D429`, `OAIQ098D430`, `OAIQ098D431`, `OAIQ098D432`, `OAIQ098D433`, `OAIQ098D434`, `OAIQ098D435`, `OAIQ098D436`, `OAIQ098D437`, `OAIQ098D438`, `OAIQ098D439`, `OAIQ098D440`, `OAIQ098D441`, `OAIQ098D442`, `OAIQ098D443`, `OAIQ098D444`, `OAIQ098D445`, `OAIQ098D446`, `OAIQ098D447`, `OAIQ098D448`, `OAIQ098D449`, `OAIQ098D450`, `OAIQ098D451`, `OAIQ098D452`, `OAIQ098D453`, `OAIQ098D454`, `OAIQ098D455`, `OAIQ098D456`, `OAIQ098D457`, `OAIQ098D458`, `OAIQ098D459`, `OAIQ098D460`, `OAIQ098D461`, `OAIQ098D462`, `OAIQ098D463`, `OAIQ098D464`, `OAIQ098D481`, `OAIQ098D489`, `OAIQ098D493`, `OAIQ098D494`, `OAIQ098D496`, `OAIQ098D603` and `OAIQ098D604`; the statements `OAI.SharpPlanar.CachedData.density0_contains` and `OAI.SharpPlanar.CachedData.density1_contains`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098D041
import Definitions.Def_OAIQ098D044
import Definitions.Def_OAIQ098D045
import Definitions.Def_OAIQ098D067
import Definitions.Def_OAIQ098D068
import Definitions.Def_OAIQ098D069
import Definitions.Def_OAIQ098D070
import Definitions.Def_OAIQ098D071
import Definitions.Def_OAIQ098D072
import Definitions.Def_OAIQ098D073
import Definitions.Def_OAIQ098D075
import Definitions.Def_OAIQ098D076
import Definitions.Def_OAIQ098D078
import Definitions.Def_OAIQ098D081
import Definitions.Def_OAIQ098D082
import Definitions.Def_OAIQ098D083
import Definitions.Def_OAIQ098D088
import Definitions.Def_OAIQ098D091
import Definitions.Def_OAIQ098D092
import Definitions.Def_OAIQ098D094
import Definitions.Def_OAIQ098D099
import Definitions.Def_OAIQ098D123
import Definitions.Def_OAIQ098D124
import Definitions.Def_OAIQ098D125
import Definitions.Def_OAIQ098D126
import Definitions.Def_OAIQ098D127
import Definitions.Def_OAIQ098D128
import Definitions.Def_OAIQ098D129
import Definitions.Def_OAIQ098D130
import Definitions.Def_OAIQ098D131
import Definitions.Def_OAIQ098D132
import Definitions.Def_OAIQ098D133
import Definitions.Def_OAIQ098D134
import Definitions.Def_OAIQ098D135
import Definitions.Def_OAIQ098D136
import Definitions.Def_OAIQ098D137
import Definitions.Def_OAIQ098D138
import Definitions.Def_OAIQ098D139
import Definitions.Def_OAIQ098D140
import Definitions.Def_OAIQ098D141
import Definitions.Def_OAIQ098D142
import Definitions.Def_OAIQ098D143
import Definitions.Def_OAIQ098D144
import Definitions.Def_OAIQ098D145
import Definitions.Def_OAIQ098D146
import Definitions.Def_OAIQ098D147
import Definitions.Def_OAIQ098D148
import Definitions.Def_OAIQ098D149
import Definitions.Def_OAIQ098D150
import Definitions.Def_OAIQ098D151
import Definitions.Def_OAIQ098D152
import Definitions.Def_OAIQ098D153
import Definitions.Def_OAIQ098D154
import Definitions.Def_OAIQ098D155
import Definitions.Def_OAIQ098D156
import Definitions.Def_OAIQ098D157
import Definitions.Def_OAIQ098D158
import Definitions.Def_OAIQ098D159
import Definitions.Def_OAIQ098D160
import Definitions.Def_OAIQ098D161
import Definitions.Def_OAIQ098D162
import Definitions.Def_OAIQ098D163
import Definitions.Def_OAIQ098D164
import Definitions.Def_OAIQ098D165
import Definitions.Def_OAIQ098D166
import Definitions.Def_OAIQ098D167
import Definitions.Def_OAIQ098D168
import Definitions.Def_OAIQ098D169
import Definitions.Def_OAIQ098D170
import Definitions.Def_OAIQ098D171

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
noncomputable def kernel0_0_r1 : Fin 16 → Fin 16 → CBox := ![kernel0_0_r1_0,kernel0_0_r1_1,kernel0_0_r1_2,kernel0_0_r1_3,kernel0_0_r1_4,kernel0_0_r1_5,kernel0_0_r1_6,kernel0_0_r1_7,kernel0_0_r1_8,kernel0_0_r1_9,kernel0_0_r1_10,kernel0_0_r1_11,kernel0_0_r1_12,kernel0_0_r1_13,kernel0_0_r1_14,kernel0_0_r1_15]
noncomputable def kernel0_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel0_0_r0,kernel0_0_r1,kernel0_0_r2,kernel0_0_r3,kernel0_0_r4,kernel0_0_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MomentPowers5
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
noncomputable def mpower0_1_r2 : Fin 16 → Fin 16 → CBox := ![mpower0_1_r2_0,mpower0_1_r2_1,mpower0_1_r2_2,mpower0_1_r2_3,mpower0_1_r2_4,mpower0_1_r2_5,mpower0_1_r2_6,mpower0_1_r2_7,mpower0_1_r2_8,mpower0_1_r2_9,mpower0_1_r2_10,mpower0_1_r2_11,mpower0_1_r2_12,mpower0_1_r2_13,mpower0_1_r2_14,mpower0_1_r2_15]
noncomputable def mpower0_1_r5 : Fin 16 → Fin 16 → CBox := ![mpower0_1_r5_0,mpower0_1_r5_1,mpower0_1_r5_2,mpower0_1_r5_3,mpower0_1_r5_4,mpower0_1_r5_5,mpower0_1_r5_6,mpower0_1_r5_7,mpower0_1_r5_8,mpower0_1_r5_9,mpower0_1_r5_10,mpower0_1_r5_11,mpower0_1_r5_12,mpower0_1_r5_13,mpower0_1_r5_14,mpower0_1_r5_15]
noncomputable def mpower0_1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower0_1_r0,mpower0_1_r1,mpower0_1_r2,mpower0_1_r3,mpower0_1_r4,mpower0_1_r5]
noncomputable def mpower1_4_r3 : Fin 16 → Fin 16 → CBox := ![mpower1_4_r3_0,mpower1_4_r3_1,mpower1_4_r3_2,mpower1_4_r3_3,mpower1_4_r3_4,mpower1_4_r3_5,mpower1_4_r3_6,mpower1_4_r3_7,mpower1_4_r3_8,mpower1_4_r3_9,mpower1_4_r3_10,mpower1_4_r3_11,mpower1_4_r3_12,mpower1_4_r3_13,mpower1_4_r3_14,mpower1_4_r3_15]
noncomputable def mpower1_4 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower1_4_r0,mpower1_4_r1,mpower1_4_r2,mpower1_4_r3,mpower1_4_r4,mpower1_4_r5]
noncomputable def mpower0_5_r3 : Fin 16 → Fin 16 → CBox := ![mpower0_5_r3_0,mpower0_5_r3_1,mpower0_5_r3_2,mpower0_5_r3_3,mpower0_5_r3_4,mpower0_5_r3_5,mpower0_5_r3_6,mpower0_5_r3_7,mpower0_5_r3_8,mpower0_5_r3_9,mpower0_5_r3_10,mpower0_5_r3_11,mpower0_5_r3_12,mpower0_5_r3_13,mpower0_5_r3_14,mpower0_5_r3_15]
noncomputable def mpower0_5 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower0_5_r0,mpower0_5_r1,mpower0_5_r2,mpower0_5_r3,mpower0_5_r4,mpower0_5_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MomentPowers10
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
noncomputable def mpower1_7_r1 : Fin 16 → Fin 16 → CBox := ![mpower1_7_r1_0,mpower1_7_r1_1,mpower1_7_r1_2,mpower1_7_r1_3,mpower1_7_r1_4,mpower1_7_r1_5,mpower1_7_r1_6,mpower1_7_r1_7,mpower1_7_r1_8,mpower1_7_r1_9,mpower1_7_r1_10,mpower1_7_r1_11,mpower1_7_r1_12,mpower1_7_r1_13,mpower1_7_r1_14,mpower1_7_r1_15]
noncomputable def mpower1_7 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower1_7_r0,mpower1_7_r1,mpower1_7_r2,mpower1_7_r3,mpower1_7_r4,mpower1_7_r5]
noncomputable def mpower0_8_r0 : Fin 16 → Fin 16 → CBox := ![mpower0_8_r0_0,mpower0_8_r0_1,mpower0_8_r0_2,mpower0_8_r0_3,mpower0_8_r0_4,mpower0_8_r0_5,mpower0_8_r0_6,mpower0_8_r0_7,mpower0_8_r0_8,mpower0_8_r0_9,mpower0_8_r0_10,mpower0_8_r0_11,mpower0_8_r0_12,mpower0_8_r0_13,mpower0_8_r0_14,mpower0_8_r0_15]
noncomputable def mpower0_8 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower0_8_r0,mpower0_8_r1,mpower0_8_r2,mpower0_8_r3,mpower0_8_r4,mpower0_8_r5]
noncomputable def mpower1_9_r4 : Fin 16 → Fin 16 → CBox := ![mpower1_9_r4_0,mpower1_9_r4_1,mpower1_9_r4_2,mpower1_9_r4_3,mpower1_9_r4_4,mpower1_9_r4_5,mpower1_9_r4_6,mpower1_9_r4_7,mpower1_9_r4_8,mpower1_9_r4_9,mpower1_9_r4_10,mpower1_9_r4_11,mpower1_9_r4_12,mpower1_9_r4_13,mpower1_9_r4_14,mpower1_9_r4_15]
noncomputable def mpower1_9 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower1_9_r0,mpower1_9_r1,mpower1_9_r2,mpower1_9_r3,mpower1_9_r4,mpower1_9_r5]
noncomputable def mpower0_10_r0 : Fin 16 → Fin 16 → CBox := ![mpower0_10_r0_0,mpower0_10_r0_1,mpower0_10_r0_2,mpower0_10_r0_3,mpower0_10_r0_4,mpower0_10_r0_5,mpower0_10_r0_6,mpower0_10_r0_7,mpower0_10_r0_8,mpower0_10_r0_9,mpower0_10_r0_10,mpower0_10_r0_11,mpower0_10_r0_12,mpower0_10_r0_13,mpower0_10_r0_14,mpower0_10_r0_15]
noncomputable def mpower0_10_r3 : Fin 16 → Fin 16 → CBox := ![mpower0_10_r3_0,mpower0_10_r3_1,mpower0_10_r3_2,mpower0_10_r3_3,mpower0_10_r3_4,mpower0_10_r3_5,mpower0_10_r3_6,mpower0_10_r3_7,mpower0_10_r3_8,mpower0_10_r3_9,mpower0_10_r3_10,mpower0_10_r3_11,mpower0_10_r3_12,mpower0_10_r3_13,mpower0_10_r3_14,mpower0_10_r3_15]
noncomputable def mpower0_10 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower0_10_r0,mpower0_10_r1,mpower0_10_r2,mpower0_10_r3,mpower0_10_r4,mpower0_10_r5]
noncomputable def mpower1_10_r5 : Fin 16 → Fin 16 → CBox := ![mpower1_10_r5_0,mpower1_10_r5_1,mpower1_10_r5_2,mpower1_10_r5_3,mpower1_10_r5_4,mpower1_10_r5_5,mpower1_10_r5_6,mpower1_10_r5_7,mpower1_10_r5_8,mpower1_10_r5_9,mpower1_10_r5_10,mpower1_10_r5_11,mpower1_10_r5_12,mpower1_10_r5_13,mpower1_10_r5_14,mpower1_10_r5_15]
noncomputable def mpower1_10 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower1_10_r0,mpower1_10_r1,mpower1_10_r2,mpower1_10_r3,mpower1_10_r4,mpower1_10_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MomentPowers15
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
noncomputable def mpower0_11_r0 : Fin 16 → Fin 16 → CBox := ![mpower0_11_r0_0,mpower0_11_r0_1,mpower0_11_r0_2,mpower0_11_r0_3,mpower0_11_r0_4,mpower0_11_r0_5,mpower0_11_r0_6,mpower0_11_r0_7,mpower0_11_r0_8,mpower0_11_r0_9,mpower0_11_r0_10,mpower0_11_r0_11,mpower0_11_r0_12,mpower0_11_r0_13,mpower0_11_r0_14,mpower0_11_r0_15]
noncomputable def mpower0_11 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower0_11_r0,mpower0_11_r1,mpower0_11_r2,mpower0_11_r3,mpower0_11_r4,mpower0_11_r5]
noncomputable def mpower0_12_r0 : Fin 16 → Fin 16 → CBox := ![mpower0_12_r0_0,mpower0_12_r0_1,mpower0_12_r0_2,mpower0_12_r0_3,mpower0_12_r0_4,mpower0_12_r0_5,mpower0_12_r0_6,mpower0_12_r0_7,mpower0_12_r0_8,mpower0_12_r0_9,mpower0_12_r0_10,mpower0_12_r0_11,mpower0_12_r0_12,mpower0_12_r0_13,mpower0_12_r0_14,mpower0_12_r0_15]
noncomputable def mpower0_12 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower0_12_r0,mpower0_12_r1,mpower0_12_r2,mpower0_12_r3,mpower0_12_r4,mpower0_12_r5]
noncomputable def mpower0_13_r0 : Fin 16 → Fin 16 → CBox := ![mpower0_13_r0_0,mpower0_13_r0_1,mpower0_13_r0_2,mpower0_13_r0_3,mpower0_13_r0_4,mpower0_13_r0_5,mpower0_13_r0_6,mpower0_13_r0_7,mpower0_13_r0_8,mpower0_13_r0_9,mpower0_13_r0_10,mpower0_13_r0_11,mpower0_13_r0_12,mpower0_13_r0_13,mpower0_13_r0_14,mpower0_13_r0_15]
noncomputable def mpower0_13 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower0_13_r0,mpower0_13_r1,mpower0_13_r2,mpower0_13_r3,mpower0_13_r4,mpower0_13_r5]
noncomputable def mpower1_13_r3 : Fin 16 → Fin 16 → CBox := ![mpower1_13_r3_0,mpower1_13_r3_1,mpower1_13_r3_2,mpower1_13_r3_3,mpower1_13_r3_4,mpower1_13_r3_5,mpower1_13_r3_6,mpower1_13_r3_7,mpower1_13_r3_8,mpower1_13_r3_9,mpower1_13_r3_10,mpower1_13_r3_11,mpower1_13_r3_12,mpower1_13_r3_13,mpower1_13_r3_14,mpower1_13_r3_15]
noncomputable def mpower1_13 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower1_13_r0,mpower1_13_r1,mpower1_13_r2,mpower1_13_r3,mpower1_13_r4,mpower1_13_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MomentPowers20
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
noncomputable def mpower1_16_r2 : Fin 16 → Fin 16 → CBox := ![mpower1_16_r2_0,mpower1_16_r2_1,mpower1_16_r2_2,mpower1_16_r2_3,mpower1_16_r2_4,mpower1_16_r2_5,mpower1_16_r2_6,mpower1_16_r2_7,mpower1_16_r2_8,mpower1_16_r2_9,mpower1_16_r2_10,mpower1_16_r2_11,mpower1_16_r2_12,mpower1_16_r2_13,mpower1_16_r2_14,mpower1_16_r2_15]
noncomputable def mpower1_16 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower1_16_r0,mpower1_16_r1,mpower1_16_r2,mpower1_16_r3,mpower1_16_r4,mpower1_16_r5]
noncomputable def mpower1_18_r5 : Fin 16 → Fin 16 → CBox := ![mpower1_18_r5_0,mpower1_18_r5_1,mpower1_18_r5_2,mpower1_18_r5_3,mpower1_18_r5_4,mpower1_18_r5_5,mpower1_18_r5_6,mpower1_18_r5_7,mpower1_18_r5_8,mpower1_18_r5_9,mpower1_18_r5_10,mpower1_18_r5_11,mpower1_18_r5_12,mpower1_18_r5_13,mpower1_18_r5_14,mpower1_18_r5_15]
noncomputable def mpower1_18 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower1_18_r0,mpower1_18_r1,mpower1_18_r2,mpower1_18_r3,mpower1_18_r4,mpower1_18_r5]
noncomputable def mpower0_19_r1 : Fin 16 → Fin 16 → CBox := ![mpower0_19_r1_0,mpower0_19_r1_1,mpower0_19_r1_2,mpower0_19_r1_3,mpower0_19_r1_4,mpower0_19_r1_5,mpower0_19_r1_6,mpower0_19_r1_7,mpower0_19_r1_8,mpower0_19_r1_9,mpower0_19_r1_10,mpower0_19_r1_11,mpower0_19_r1_12,mpower0_19_r1_13,mpower0_19_r1_14,mpower0_19_r1_15]
noncomputable def mpower0_19 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower0_19_r0,mpower0_19_r1,mpower0_19_r2,mpower0_19_r3,mpower0_19_r4,mpower0_19_r5]
noncomputable def mpower1_19_r1 : Fin 16 → Fin 16 → CBox := ![mpower1_19_r1_0,mpower1_19_r1_1,mpower1_19_r1_2,mpower1_19_r1_3,mpower1_19_r1_4,mpower1_19_r1_5,mpower1_19_r1_6,mpower1_19_r1_7,mpower1_19_r1_8,mpower1_19_r1_9,mpower1_19_r1_10,mpower1_19_r1_11,mpower1_19_r1_12,mpower1_19_r1_13,mpower1_19_r1_14,mpower1_19_r1_15]
noncomputable def mpower1_19 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower1_19_r0,mpower1_19_r1,mpower1_19_r2,mpower1_19_r3,mpower1_19_r4,mpower1_19_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MomentPowers25
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
noncomputable def mpower1_21_r1 : Fin 16 → Fin 16 → CBox := ![mpower1_21_r1_0,mpower1_21_r1_1,mpower1_21_r1_2,mpower1_21_r1_3,mpower1_21_r1_4,mpower1_21_r1_5,mpower1_21_r1_6,mpower1_21_r1_7,mpower1_21_r1_8,mpower1_21_r1_9,mpower1_21_r1_10,mpower1_21_r1_11,mpower1_21_r1_12,mpower1_21_r1_13,mpower1_21_r1_14,mpower1_21_r1_15]
noncomputable def mpower1_21 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower1_21_r0,mpower1_21_r1,mpower1_21_r2,mpower1_21_r3,mpower1_21_r4,mpower1_21_r5]
noncomputable def mpower0_24_r5 : Fin 16 → Fin 16 → CBox := ![mpower0_24_r5_0,mpower0_24_r5_1,mpower0_24_r5_2,mpower0_24_r5_3,mpower0_24_r5_4,mpower0_24_r5_5,mpower0_24_r5_6,mpower0_24_r5_7,mpower0_24_r5_8,mpower0_24_r5_9,mpower0_24_r5_10,mpower0_24_r5_11,mpower0_24_r5_12,mpower0_24_r5_13,mpower0_24_r5_14,mpower0_24_r5_15]
noncomputable def mpower0_24 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower0_24_r0,mpower0_24_r1,mpower0_24_r2,mpower0_24_r3,mpower0_24_r4,mpower0_24_r5]
noncomputable def mpower1_24_r1 : Fin 16 → Fin 16 → CBox := ![mpower1_24_r1_0,mpower1_24_r1_1,mpower1_24_r1_2,mpower1_24_r1_3,mpower1_24_r1_4,mpower1_24_r1_5,mpower1_24_r1_6,mpower1_24_r1_7,mpower1_24_r1_8,mpower1_24_r1_9,mpower1_24_r1_10,mpower1_24_r1_11,mpower1_24_r1_12,mpower1_24_r1_13,mpower1_24_r1_14,mpower1_24_r1_15]
noncomputable def mpower1_24 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower1_24_r0,mpower1_24_r1,mpower1_24_r2,mpower1_24_r3,mpower1_24_r4,mpower1_24_r5]
noncomputable def mpower0_25_r0 : Fin 16 → Fin 16 → CBox := ![mpower0_25_r0_0,mpower0_25_r0_1,mpower0_25_r0_2,mpower0_25_r0_3,mpower0_25_r0_4,mpower0_25_r0_5,mpower0_25_r0_6,mpower0_25_r0_7,mpower0_25_r0_8,mpower0_25_r0_9,mpower0_25_r0_10,mpower0_25_r0_11,mpower0_25_r0_12,mpower0_25_r0_13,mpower0_25_r0_14,mpower0_25_r0_15]
noncomputable def mpower0_25 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower0_25_r0,mpower0_25_r1,mpower0_25_r2,mpower0_25_r3,mpower0_25_r4,mpower0_25_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MomentPowers30
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
noncomputable def mpower1_26_r5 : Fin 16 → Fin 16 → CBox := ![mpower1_26_r5_0,mpower1_26_r5_1,mpower1_26_r5_2,mpower1_26_r5_3,mpower1_26_r5_4,mpower1_26_r5_5,mpower1_26_r5_6,mpower1_26_r5_7,mpower1_26_r5_8,mpower1_26_r5_9,mpower1_26_r5_10,mpower1_26_r5_11,mpower1_26_r5_12,mpower1_26_r5_13,mpower1_26_r5_14,mpower1_26_r5_15]
noncomputable def mpower1_26 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower1_26_r0,mpower1_26_r1,mpower1_26_r2,mpower1_26_r3,mpower1_26_r4,mpower1_26_r5]
noncomputable def mpower1_27_r3 : Fin 16 → Fin 16 → CBox := ![mpower1_27_r3_0,mpower1_27_r3_1,mpower1_27_r3_2,mpower1_27_r3_3,mpower1_27_r3_4,mpower1_27_r3_5,mpower1_27_r3_6,mpower1_27_r3_7,mpower1_27_r3_8,mpower1_27_r3_9,mpower1_27_r3_10,mpower1_27_r3_11,mpower1_27_r3_12,mpower1_27_r3_13,mpower1_27_r3_14,mpower1_27_r3_15]
noncomputable def mpower1_27 : Fin 6 → Fin 16 → Fin 16 → CBox := ![mpower1_27_r0,mpower1_27_r1,mpower1_27_r2,mpower1_27_r3,mpower1_27_r4,mpower1_27_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders0
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
lemma ha0_1_0_eq (j : Fin 7) : ha0_1_0 j = atomKernel0_0 j := by fin_cases j <;> decide +kernel
noncomputable def hk0_1_1 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_1 j i k)
noncomputable def hk0_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_2 j i k)
noncomputable def hk0_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_3 j i k)
noncomputable def hk0_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_4 j i k)
noncomputable def hk0_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_5 j i k)
noncomputable def hk0_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_6 j i k)
noncomputable def hk0_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_7 j i k)
noncomputable def hk0_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_8 j i k)
noncomputable def hk0_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_9 j i k)
noncomputable def hk0_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_10 j i k)
noncomputable def hk0_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_11 j i k)
noncomputable def hk0_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_12 j i k)
noncomputable def hk0_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_13 j i k)
noncomputable def hk0_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_14 j i k)
noncomputable def hk0_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_15 j i k)
noncomputable def hk0_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_16 j i k)
noncomputable def hk0_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_17 j i k)
noncomputable def hk0_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_18 j i k)
noncomputable def hk0_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_19 j i k)
noncomputable def hk0_1_20 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_20 j i k)
noncomputable def hk0_1_21 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_21 j i k)
noncomputable def hk0_1_22 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_22 j i k)
noncomputable def hk0_1_23 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_23 j i k)
noncomputable def hk0_1_24 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_24 j i k)
noncomputable def hk0_1_25 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_25 j i k)
noncomputable def hk0_1_26 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_26 j i k)
noncomputable def hk0_1_27 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_27 j i k)
noncomputable def hk0_1_28 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_28 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders1
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
noncomputable def hk1_0_1 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_1 j i k)
noncomputable def hk1_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_2 j i k)
noncomputable def hk1_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_3 j i k)
noncomputable def hk1_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_4 j i k)
noncomputable def hk1_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_5 j i k)
noncomputable def hk1_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_6 j i k)
noncomputable def hk1_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_7 j i k)
noncomputable def hk1_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_8 j i k)
noncomputable def hk1_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_9 j i k)
noncomputable def hk1_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_10 j i k)
noncomputable def hk1_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_11 j i k)
noncomputable def hk1_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_12 j i k)
noncomputable def hk1_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_13 j i k)
noncomputable def hk1_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_14 j i k)
noncomputable def hk1_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_15 j i k)
noncomputable def hk1_0_16 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_16 j i k)
noncomputable def hk1_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_17 j i k)
noncomputable def hk1_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_18 j i k)
noncomputable def hk1_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_19 j i k)
noncomputable def hk1_0_20 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_20 j i k)
noncomputable def hk1_0_21 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_21 j i k)
noncomputable def hk1_0_22 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_22 j i k)
noncomputable def hk1_0_23 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_23 j i k)
noncomputable def hk1_0_24 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_24 j i k)
noncomputable def hk1_0_25 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_25 j i k)
noncomputable def hk1_0_26 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_26 j i k)
noncomputable def hk1_0_27 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_27 j i k)
noncomputable def hk1_0_28 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_28 j i k)
noncomputable def hk1_0_29 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_29 j i k)
noncomputable def hk1_0_30 (j : Fin 6) (i k : Fin 16) : CBox := (power1 j i k).conj.mul (mpower0_30 j i k)
lemma ha1_1_0_eq (j : Fin 7) : ha1_1_0 j = atomKernel1_0 j := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues20
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
noncomputable def kernel19_0_r0 : Fin 16 → Fin 16 → CBox := ![kernel19_0_r0_0,kernel19_0_r0_1,kernel19_0_r0_2,kernel19_0_r0_3,kernel19_0_r0_4,kernel19_0_r0_5,kernel19_0_r0_6,kernel19_0_r0_7,kernel19_0_r0_8,kernel19_0_r0_9,kernel19_0_r0_10,kernel19_0_r0_11,kernel19_0_r0_12,kernel19_0_r0_13,kernel19_0_r0_14,kernel19_0_r0_15]
noncomputable def kernel19_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel19_0_r0,kernel19_0_r1,kernel19_0_r2,kernel19_0_r3,kernel19_0_r4,kernel19_0_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders12
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
noncomputable def hk12_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_2 j i k)
noncomputable def hk12_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_3 j i k)
noncomputable def hk12_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_4 j i k)
noncomputable def hk12_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_5 j i k)
noncomputable def hk12_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_6 j i k)
noncomputable def hk12_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_7 j i k)
noncomputable def hk12_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_8 j i k)
noncomputable def hk12_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_9 j i k)
noncomputable def hk12_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_10 j i k)
noncomputable def hk12_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_11 j i k)
noncomputable def hk12_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_12 j i k)
noncomputable def hk12_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power12 j i k).conj.mul (mpower0_13 j i k)
lemma ha12_1_0_eq (j : Fin 7) : ha12_1_0 j = atomKernel12_0 j := by fin_cases j <;> decide +kernel
noncomputable def hk12_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_2 j i k)
noncomputable def hk12_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_3 j i k)
noncomputable def hk12_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_4 j i k)
noncomputable def hk12_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_5 j i k)
noncomputable def hk12_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_6 j i k)
noncomputable def hk12_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_7 j i k)
noncomputable def hk12_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_8 j i k)
noncomputable def hk12_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_9 j i k)
noncomputable def hk12_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_10 j i k)
noncomputable def hk12_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_11 j i k)
noncomputable def hk12_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_12 j i k)
noncomputable def hk12_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel12_0 j i k).mul (mpower1_13 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders13
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
lemma ha13_1_0_eq (j : Fin 7) : ha13_1_0 j = atomKernel13_0 j := by fin_cases j <;> decide +kernel
noncomputable def hk13_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_2 j i k)
noncomputable def hk13_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_3 j i k)
noncomputable def hk13_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_4 j i k)
noncomputable def hk13_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_5 j i k)
noncomputable def hk13_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_6 j i k)
noncomputable def hk13_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_7 j i k)
noncomputable def hk13_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_8 j i k)
noncomputable def hk13_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_9 j i k)
noncomputable def hk13_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_10 j i k)
noncomputable def hk13_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_11 j i k)
noncomputable def hk13_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel13_0 j i k).mul (mpower1_12 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders15
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
lemma ha15_1_0_eq (j : Fin 7) : ha15_1_0 j = atomKernel15_0 j := by fin_cases j <;> decide +kernel
noncomputable def hk15_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_2 j i k)
noncomputable def hk15_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_3 j i k)
noncomputable def hk15_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_4 j i k)
noncomputable def hk15_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_5 j i k)
noncomputable def hk15_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_6 j i k)
noncomputable def hk15_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_7 j i k)
noncomputable def hk15_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_8 j i k)
noncomputable def hk15_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_9 j i k)
noncomputable def hk15_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_10 j i k)
noncomputable def hk15_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_11 j i k)
noncomputable def hk15_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_12 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders16
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
noncomputable def hk16_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_2 j i k)
noncomputable def hk16_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_3 j i k)
noncomputable def hk16_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_4 j i k)
noncomputable def hk16_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_5 j i k)
noncomputable def hk16_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_6 j i k)
noncomputable def hk16_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_7 j i k)
noncomputable def hk16_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_8 j i k)
noncomputable def hk16_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_9 j i k)
noncomputable def hk16_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_10 j i k)
noncomputable def hk16_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_11 j i k)
noncomputable def hk16_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_12 j i k)
noncomputable def hk16_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_13 j i k)
lemma ha16_1_0_eq (j : Fin 7) : ha16_1_0 j = atomKernel16_0 j := by fin_cases j <;> decide +kernel
noncomputable def hk16_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_2 j i k)
noncomputable def hk16_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_3 j i k)
noncomputable def hk16_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_4 j i k)
noncomputable def hk16_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_5 j i k)
noncomputable def hk16_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_6 j i k)
noncomputable def hk16_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_7 j i k)
noncomputable def hk16_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_8 j i k)
noncomputable def hk16_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_9 j i k)
noncomputable def hk16_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_10 j i k)
noncomputable def hk16_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_11 j i k)
noncomputable def hk16_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_12 j i k)
noncomputable def hk16_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_13 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders19
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
noncomputable def hk19_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_2 j i k)
noncomputable def hk19_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_3 j i k)
noncomputable def hk19_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_4 j i k)
noncomputable def hk19_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_5 j i k)
noncomputable def hk19_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_6 j i k)
noncomputable def hk19_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_7 j i k)
noncomputable def hk19_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_8 j i k)
noncomputable def hk19_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_9 j i k)
noncomputable def hk19_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_10 j i k)
noncomputable def hk19_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_11 j i k)
noncomputable def hk19_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_12 j i k)
noncomputable def hk19_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power19 j i k).conj.mul (mpower0_13 j i k)
lemma ha19_1_0_eq (j : Fin 7) : ha19_1_0 j = atomKernel19_0 j := by fin_cases j <;> decide +kernel
noncomputable def hk19_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_2 j i k)
noncomputable def hk19_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_3 j i k)
noncomputable def hk19_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_4 j i k)
noncomputable def hk19_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_5 j i k)
noncomputable def hk19_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_6 j i k)
noncomputable def hk19_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_7 j i k)
noncomputable def hk19_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_8 j i k)
noncomputable def hk19_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_9 j i k)
noncomputable def hk19_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_10 j i k)
noncomputable def hk19_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_11 j i k)
noncomputable def hk19_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_12 j i k)
noncomputable def hk19_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel19_0 j i k).mul (mpower1_13 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_KernelValues30
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
noncomputable def kernel21_0_r0 : Fin 16 → Fin 16 → CBox := ![kernel21_0_r0_0,kernel21_0_r0_1,kernel21_0_r0_2,kernel21_0_r0_3,kernel21_0_r0_4,kernel21_0_r0_5,kernel21_0_r0_6,kernel21_0_r0_7,kernel21_0_r0_8,kernel21_0_r0_9,kernel21_0_r0_10,kernel21_0_r0_11,kernel21_0_r0_12,kernel21_0_r0_13,kernel21_0_r0_14,kernel21_0_r0_15]
noncomputable def kernel21_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel21_0_r0,kernel21_0_r1,kernel21_0_r2,kernel21_0_r3,kernel21_0_r4,kernel21_0_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders21
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
lemma ha21_1_0_eq (j : Fin 7) : ha21_1_0 j = atomKernel21_0 j := by fin_cases j <;> decide +kernel
noncomputable def hk21_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_2 j i k)
noncomputable def hk21_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_3 j i k)
noncomputable def hk21_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_4 j i k)
noncomputable def hk21_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_5 j i k)
noncomputable def hk21_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_6 j i k)
noncomputable def hk21_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_7 j i k)
noncomputable def hk21_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_8 j i k)
noncomputable def hk21_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_9 j i k)
noncomputable def hk21_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_10 j i k)
noncomputable def hk21_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_11 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders24
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
lemma ha24_1_0_eq (j : Fin 7) : ha24_1_0 j = atomKernel24_0 j := by fin_cases j <;> decide +kernel
noncomputable def hk24_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_2 j i k)
noncomputable def hk24_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_3 j i k)
noncomputable def hk24_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_4 j i k)
noncomputable def hk24_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_5 j i k)
noncomputable def hk24_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_6 j i k)
noncomputable def hk24_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_7 j i k)
noncomputable def hk24_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_8 j i k)
noncomputable def hk24_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_9 j i k)
noncomputable def hk24_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_10 j i k)
noncomputable def hk24_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel24_0 j i k).mul (mpower1_11 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders25
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
noncomputable def hk25_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_2 j i k)
noncomputable def hk25_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_3 j i k)
noncomputable def hk25_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_4 j i k)
noncomputable def hk25_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_5 j i k)
noncomputable def hk25_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_6 j i k)
noncomputable def hk25_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_7 j i k)
noncomputable def hk25_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_8 j i k)
noncomputable def hk25_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_9 j i k)
noncomputable def hk25_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_10 j i k)
noncomputable def hk25_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_11 j i k)
noncomputable def hk25_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_12 j i k)
lemma ha25_1_0_eq (j : Fin 7) : ha25_1_0 j = atomKernel25_0 j := by fin_cases j <;> decide +kernel
noncomputable def hk25_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_2 j i k)
noncomputable def hk25_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_3 j i k)
noncomputable def hk25_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_4 j i k)
noncomputable def hk25_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_5 j i k)
noncomputable def hk25_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_6 j i k)
noncomputable def hk25_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_7 j i k)
noncomputable def hk25_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_8 j i k)
noncomputable def hk25_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_9 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders27
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
lemma ha27_1_0_eq (j : Fin 7) : ha27_1_0 j = atomKernel27_0 j := by fin_cases j <;> decide +kernel
noncomputable def hk27_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_2 j i k)
noncomputable def hk27_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_3 j i k)
noncomputable def hk27_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_4 j i k)
noncomputable def hk27_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_5 j i k)
noncomputable def hk27_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_6 j i k)
noncomputable def hk27_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_7 j i k)
noncomputable def hk27_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_8 j i k)
noncomputable def hk27_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel27_0 j i k).mul (mpower1_9 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders28
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
noncomputable def hk28_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_2 j i k)
noncomputable def hk28_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_3 j i k)
noncomputable def hk28_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_4 j i k)
noncomputable def hk28_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_5 j i k)
noncomputable def hk28_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_6 j i k)
noncomputable def hk28_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_7 j i k)
noncomputable def hk28_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_8 j i k)
noncomputable def hk28_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_9 j i k)
noncomputable def hk28_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_10 j i k)
noncomputable def hk28_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_11 j i k)
noncomputable def hk28_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_12 j i k)
noncomputable def hk28_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_13 j i k)
lemma ha28_1_0_eq (j : Fin 7) : ha28_1_0 j = atomKernel28_0 j := by fin_cases j <;> decide +kernel
noncomputable def hk28_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_2 j i k)
noncomputable def hk28_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_3 j i k)
noncomputable def hk28_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_4 j i k)
noncomputable def hk28_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_5 j i k)
noncomputable def hk28_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_6 j i k)
noncomputable def hk28_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_7 j i k)
noncomputable def hk28_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_8 j i k)
noncomputable def hk28_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_9 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders3
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
noncomputable def hk3_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_2 j i k)
noncomputable def hk3_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_3 j i k)
noncomputable def hk3_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_4 j i k)
noncomputable def hk3_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_5 j i k)
noncomputable def hk3_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_6 j i k)
noncomputable def hk3_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_7 j i k)
noncomputable def hk3_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_8 j i k)
noncomputable def hk3_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_9 j i k)
noncomputable def hk3_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_10 j i k)
noncomputable def hk3_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_11 j i k)
noncomputable def hk3_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_12 j i k)
noncomputable def hk3_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power3 j i k).conj.mul (mpower0_13 j i k)
lemma ha3_1_0_eq (j : Fin 7) : ha3_1_0 j = atomKernel3_0 j := by fin_cases j <;> decide +kernel
noncomputable def hk3_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_2 j i k)
noncomputable def hk3_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_3 j i k)
noncomputable def hk3_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_4 j i k)
noncomputable def hk3_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_5 j i k)
noncomputable def hk3_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_6 j i k)
noncomputable def hk3_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_7 j i k)
noncomputable def hk3_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_8 j i k)
noncomputable def hk3_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_9 j i k)
noncomputable def hk3_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_10 j i k)
noncomputable def hk3_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_11 j i k)
noncomputable def hk3_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_12 j i k)
noncomputable def hk3_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel3_0 j i k).mul (mpower1_13 j i k)
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
noncomputable def kernel33_0_r2 : Fin 16 → Fin 16 → CBox := ![kernel33_0_r2_0,kernel33_0_r2_1,kernel33_0_r2_2,kernel33_0_r2_3,kernel33_0_r2_4,kernel33_0_r2_5,kernel33_0_r2_6,kernel33_0_r2_7,kernel33_0_r2_8,kernel33_0_r2_9,kernel33_0_r2_10,kernel33_0_r2_11,kernel33_0_r2_12,kernel33_0_r2_13,kernel33_0_r2_14,kernel33_0_r2_15]
noncomputable def kernel33_0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![kernel33_0_r0,kernel33_0_r1,kernel33_0_r2,kernel33_0_r3,kernel33_0_r4,kernel33_0_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders31
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
noncomputable def hk31_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_2 j i k)
noncomputable def hk31_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_3 j i k)
noncomputable def hk31_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_4 j i k)
noncomputable def hk31_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_5 j i k)
noncomputable def hk31_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_6 j i k)
noncomputable def hk31_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_7 j i k)
noncomputable def hk31_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_8 j i k)
noncomputable def hk31_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_9 j i k)
noncomputable def hk31_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_10 j i k)
noncomputable def hk31_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_11 j i k)
noncomputable def hk31_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_12 j i k)
noncomputable def hk31_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_13 j i k)
lemma ha31_1_0_eq (j : Fin 7) : ha31_1_0 j = atomKernel31_0 j := by fin_cases j <;> decide +kernel
noncomputable def hk31_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_2 j i k)
noncomputable def hk31_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_3 j i k)
noncomputable def hk31_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_4 j i k)
noncomputable def hk31_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_5 j i k)
noncomputable def hk31_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_6 j i k)
noncomputable def hk31_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_7 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders33
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
noncomputable def hk33_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_2 j i k)
noncomputable def hk33_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_3 j i k)
noncomputable def hk33_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_4 j i k)
noncomputable def hk33_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_5 j i k)
noncomputable def hk33_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_6 j i k)
noncomputable def hk33_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_7 j i k)
noncomputable def hk33_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_8 j i k)
noncomputable def hk33_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_9 j i k)
noncomputable def hk33_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_10 j i k)
noncomputable def hk33_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_11 j i k)
noncomputable def hk33_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_12 j i k)
noncomputable def hk33_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power33 j i k).conj.mul (mpower0_13 j i k)
lemma ha33_1_0_eq (j : Fin 7) : ha33_1_0 j = atomKernel33_0 j := by fin_cases j <;> decide +kernel
noncomputable def hk33_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_2 j i k)
noncomputable def hk33_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_3 j i k)
noncomputable def hk33_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_4 j i k)
noncomputable def hk33_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_5 j i k)
noncomputable def hk33_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_6 j i k)
noncomputable def hk33_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel33_0 j i k).mul (mpower1_7 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders36
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
noncomputable def hk36_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_2 j i k)
noncomputable def hk36_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_3 j i k)
noncomputable def hk36_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_4 j i k)
noncomputable def hk36_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_5 j i k)
noncomputable def hk36_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_6 j i k)
noncomputable def hk36_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_7 j i k)
noncomputable def hk36_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_8 j i k)
noncomputable def hk36_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_9 j i k)
noncomputable def hk36_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_10 j i k)
noncomputable def hk36_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_11 j i k)
noncomputable def hk36_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_12 j i k)
noncomputable def hk36_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power36 j i k).conj.mul (mpower0_13 j i k)
lemma ha36_1_0_eq (j : Fin 7) : ha36_1_0 j = atomKernel36_0 j := by fin_cases j <;> decide +kernel
noncomputable def hk36_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_2 j i k)
noncomputable def hk36_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_3 j i k)
noncomputable def hk36_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_4 j i k)
noncomputable def hk36_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel36_0 j i k).mul (mpower1_5 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders37
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
noncomputable def hk37_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_2 j i k)
noncomputable def hk37_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_3 j i k)
noncomputable def hk37_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_4 j i k)
noncomputable def hk37_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_5 j i k)
noncomputable def hk37_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_6 j i k)
noncomputable def hk37_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_7 j i k)
noncomputable def hk37_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_8 j i k)
noncomputable def hk37_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_9 j i k)
noncomputable def hk37_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_10 j i k)
noncomputable def hk37_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_11 j i k)
noncomputable def hk37_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_12 j i k)
lemma ha37_1_0_eq (j : Fin 7) : ha37_1_0 j = atomKernel37_0 j := by fin_cases j <;> decide +kernel
noncomputable def hk37_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_2 j i k)
noncomputable def hk37_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_3 j i k)
noncomputable def hk37_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_4 j i k)
noncomputable def hk37_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_5 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders39
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
noncomputable def hk39_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_2 j i k)
noncomputable def hk39_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_3 j i k)
noncomputable def hk39_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_4 j i k)
noncomputable def hk39_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_5 j i k)
noncomputable def hk39_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_6 j i k)
noncomputable def hk39_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_7 j i k)
noncomputable def hk39_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_8 j i k)
noncomputable def hk39_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_9 j i k)
noncomputable def hk39_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_10 j i k)
noncomputable def hk39_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_11 j i k)
noncomputable def hk39_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power39 j i k).conj.mul (mpower0_12 j i k)
lemma ha39_1_0_eq (j : Fin 7) : ha39_1_0 j = atomKernel39_0 j := by fin_cases j <;> decide +kernel
noncomputable def hk39_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_2 j i k)
noncomputable def hk39_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_3 j i k)
noncomputable def hk39_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_4 j i k)
noncomputable def hk39_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel39_0 j i k).mul (mpower1_5 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders4
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
lemma ha4_1_0_eq (j : Fin 7) : ha4_1_0 j = atomKernel4_0 j := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders40
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
lemma ha40_1_0_eq (j : Fin 7) : ha40_1_0 j = atomKernel40_0 j := by fin_cases j <;> decide +kernel
noncomputable def hk40_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_2 j i k)
noncomputable def hk40_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_3 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders7
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
lemma ha7_1_0_eq (j : Fin 7) : ha7_1_0 j = atomKernel7_0 j := by fin_cases j <;> decide +kernel
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders9
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
lemma ha9_1_0_eq (j : Fin 7) : ha9_1_0 j = atomKernel9_0 j := by fin_cases j <;> decide +kernel
noncomputable def hk9_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_2 j i k)
noncomputable def hk9_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_3 j i k)
noncomputable def hk9_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_4 j i k)
noncomputable def hk9_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_5 j i k)
noncomputable def hk9_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_6 j i k)
noncomputable def hk9_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_7 j i k)
noncomputable def hk9_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_8 j i k)
noncomputable def hk9_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_9 j i k)
noncomputable def hk9_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_10 j i k)
noncomputable def hk9_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_11 j i k)
noncomputable def hk9_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_12 j i k)
noncomputable def hk9_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_13 j i k)
noncomputable def hk9_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_14 j i k)
noncomputable def hk9_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel9_0 j i k).mul (mpower1_15 j i k)
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity0Panel0
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
noncomputable def density0_r0 : Fin 16 → Fin 16 → CBox := ![density0_r0_0,density0_r0_1,density0_r0_2,density0_r0_3,density0_r0_4,density0_r0_5,density0_r0_6,density0_r0_7,density0_r0_8,density0_r0_9,density0_r0_10,density0_r0_11,density0_r0_12,density0_r0_13,density0_r0_14,density0_r0_15]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity0Panel1
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
noncomputable def density0_r1 : Fin 16 → Fin 16 → CBox := ![density0_r1_0,density0_r1_1,density0_r1_2,density0_r1_3,density0_r1_4,density0_r1_5,density0_r1_6,density0_r1_7,density0_r1_8,density0_r1_9,density0_r1_10,density0_r1_11,density0_r1_12,density0_r1_13,density0_r1_14,density0_r1_15]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity0Panel2
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
noncomputable def density0_r2 : Fin 16 → Fin 16 → CBox := ![density0_r2_0,density0_r2_1,density0_r2_2,density0_r2_3,density0_r2_4,density0_r2_5,density0_r2_6,density0_r2_7,density0_r2_8,density0_r2_9,density0_r2_10,density0_r2_11,density0_r2_12,density0_r2_13,density0_r2_14,density0_r2_15]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity0Panel3
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
noncomputable def density0_r3 : Fin 16 → Fin 16 → CBox := ![density0_r3_0,density0_r3_1,density0_r3_2,density0_r3_3,density0_r3_4,density0_r3_5,density0_r3_6,density0_r3_7,density0_r3_8,density0_r3_9,density0_r3_10,density0_r3_11,density0_r3_12,density0_r3_13,density0_r3_14,density0_r3_15]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity0Panel4
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
noncomputable def density0_r4 : Fin 16 → Fin 16 → CBox := ![density0_r4_0,density0_r4_1,density0_r4_2,density0_r4_3,density0_r4_4,density0_r4_5,density0_r4_6,density0_r4_7,density0_r4_8,density0_r4_9,density0_r4_10,density0_r4_11,density0_r4_12,density0_r4_13,density0_r4_14,density0_r4_15]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity0Panel5
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
noncomputable def density0_r5 : Fin 16 → Fin 16 → CBox := ![density0_r5_0,density0_r5_1,density0_r5_2,density0_r5_3,density0_r5_4,density0_r5_5,density0_r5_6,density0_r5_7,density0_r5_8,density0_r5_9,density0_r5_10,density0_r5_11,density0_r5_12,density0_r5_13,density0_r5_14,density0_r5_15]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity1Panel0
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
noncomputable def density1_r0 : Fin 16 → Fin 16 → CBox := ![density1_r0_0,density1_r0_1,density1_r0_2,density1_r0_3,density1_r0_4,density1_r0_5,density1_r0_6,density1_r0_7,density1_r0_8,density1_r0_9,density1_r0_10,density1_r0_11,density1_r0_12,density1_r0_13,density1_r0_14,density1_r0_15]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity1Panel1
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
noncomputable def density1_r1 : Fin 16 → Fin 16 → CBox := ![density1_r1_0,density1_r1_1,density1_r1_2,density1_r1_3,density1_r1_4,density1_r1_5,density1_r1_6,density1_r1_7,density1_r1_8,density1_r1_9,density1_r1_10,density1_r1_11,density1_r1_12,density1_r1_13,density1_r1_14,density1_r1_15]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity1Panel2
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
noncomputable def density1_r2 : Fin 16 → Fin 16 → CBox := ![density1_r2_0,density1_r2_1,density1_r2_2,density1_r2_3,density1_r2_4,density1_r2_5,density1_r2_6,density1_r2_7,density1_r2_8,density1_r2_9,density1_r2_10,density1_r2_11,density1_r2_12,density1_r2_13,density1_r2_14,density1_r2_15]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity1Panel3
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
noncomputable def density1_r3 : Fin 16 → Fin 16 → CBox := ![density1_r3_0,density1_r3_1,density1_r3_2,density1_r3_3,density1_r3_4,density1_r3_5,density1_r3_6,density1_r3_7,density1_r3_8,density1_r3_9,density1_r3_10,density1_r3_11,density1_r3_12,density1_r3_13,density1_r3_14,density1_r3_15]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity1Panel4
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
noncomputable def density1_r4 : Fin 16 → Fin 16 → CBox := ![density1_r4_0,density1_r4_1,density1_r4_2,density1_r4_3,density1_r4_4,density1_r4_5,density1_r4_6,density1_r4_7,density1_r4_8,density1_r4_9,density1_r4_10,density1_r4_11,density1_r4_12,density1_r4_13,density1_r4_14,density1_r4_15]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensity1Panel5
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
noncomputable def density1_r5 : Fin 16 → Fin 16 → CBox := ![density1_r5_0,density1_r5_1,density1_r5_2,density1_r5_3,density1_r5_4,density1_r5_5,density1_r5_6,density1_r5_7,density1_r5_8,density1_r5_9,density1_r5_10,density1_r5_11,density1_r5_12,density1_r5_13,density1_r5_14,density1_r5_15]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensityValues
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
noncomputable def density0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![density0_r0,density0_r1,density0_r2,density0_r3,density0_r4,density0_r5]
noncomputable def density1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![density1_r0,density1_r1,density1_r2,density1_r3,density1_r4,density1_r5]
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments0_0
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
namespace hm0_1_0_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_0
namespace hm0_1_0_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_1
namespace hm0_1_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_2
namespace hm0_1_0_3
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_3
namespace hm0_1_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_4
namespace hm0_1_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_5
namespace hm0_1_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_6
namespace hm0_1_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments0_1
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
namespace hm0_1_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_8
namespace hm0_1_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_9
namespace hm0_1_0_10
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_10
namespace hm0_1_0_11
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_11
namespace hm0_1_0_12
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_12
namespace hm0_1_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_13
namespace hm0_1_0_14
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_14
namespace hm0_1_0_15
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_15
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments0_2
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
namespace hm0_1_0_16
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_16
namespace hm0_1_0_17
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_17
namespace hm0_1_0_18
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_18
namespace hm0_1_0_19
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_19
namespace hm0_1_0_20
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_20
namespace hm0_1_0_21
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_21
namespace hm0_1_0_22
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_22
namespace hm0_1_0_23
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_23
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments0_3
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
namespace hm0_1_0_24
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_24
namespace hm0_1_0_25
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_25
namespace hm0_1_0_26
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_26
namespace hm0_1_0_27
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_27
namespace hm0_1_0_28
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_1_0_28
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments0_4
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
namespace hm0_0_1_0
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_0
namespace hm0_0_1_1
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_1
namespace hm0_0_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_2
namespace hm0_0_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_3
namespace hm0_0_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_4
namespace hm0_0_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_5
namespace hm0_0_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_6
namespace hm0_0_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments0_5
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
namespace hm0_0_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_8
namespace hm0_0_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_9
namespace hm0_0_1_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_10
namespace hm0_0_1_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_11
namespace hm0_0_1_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_12
namespace hm0_0_1_13
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_13
namespace hm0_0_1_14
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_14
namespace hm0_0_1_15
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_15
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments0_6
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
namespace hm0_0_1_16
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_16
namespace hm0_0_1_17
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_17
namespace hm0_0_1_18
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_18
namespace hm0_0_1_19
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_19
namespace hm0_0_1_20
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_20
namespace hm0_0_1_21
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_21
namespace hm0_0_1_22
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_22
namespace hm0_0_1_23
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_23
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments0_7
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
namespace hm0_0_1_24
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_24
namespace hm0_0_1_25
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_25
namespace hm0_0_1_26
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_26
namespace hm0_0_1_27
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_27
namespace hm0_0_1_28
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm0_0_1_28
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock12_0
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
namespace hm12_0_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_0_0_2
namespace hm12_1_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_1_0_2
namespace hm12_0_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_0_0_3
namespace hm12_1_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_1_0_3
namespace hm12_0_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_0_0_4
namespace hm12_1_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_1_0_4
namespace hm12_0_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_0_0_5
namespace hm12_1_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_1_0_5
namespace hm12_0_0_6
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_0_0_6
namespace hm12_1_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_1_0_6
namespace hm12_0_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_0_0_7
namespace hm12_1_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock12_1
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
namespace hm12_0_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_0_0_8
namespace hm12_1_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_1_0_8
namespace hm12_0_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_0_0_9
namespace hm12_1_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_1_0_9
namespace hm12_0_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_0_0_10
namespace hm12_1_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_1_0_10
namespace hm12_0_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_0_0_11
namespace hm12_1_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_1_0_11
namespace hm12_0_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_0_0_12
namespace hm12_1_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_1_0_12
namespace hm12_0_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_0_0_13
namespace hm12_1_0_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_1_0_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock12_10
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
namespace hm12_0_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_0_1_2
namespace hm12_1_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_1_1_2
namespace hm12_0_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_0_1_3
namespace hm12_1_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_1_1_3
namespace hm12_0_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_0_1_4
namespace hm12_1_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_1_1_4
namespace hm12_0_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_0_1_5
namespace hm12_1_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_1_1_5
namespace hm12_0_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_0_1_6
namespace hm12_1_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_1_1_6
namespace hm12_0_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_0_1_7
namespace hm12_1_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock12_11
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
namespace hm12_0_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_0_1_8
namespace hm12_1_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_1_1_8
namespace hm12_0_1_9
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_0_1_9
namespace hm12_1_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_1_1_9
namespace hm12_0_1_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_0_1_10
namespace hm12_1_1_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_1_1_10
namespace hm12_0_1_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_0_1_11
namespace hm12_1_1_11
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_1_1_11
namespace hm12_0_1_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_0_1_12
namespace hm12_1_1_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_1_1_12
namespace hm12_0_1_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_0_1_13
namespace hm12_1_1_13
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm12_1_1_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock13_0
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
namespace hm13_0_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_0_0_2
namespace hm13_1_0_2
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_1_0_2
namespace hm13_0_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_0_0_3
namespace hm13_1_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_1_0_3
namespace hm13_0_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_0_0_4
namespace hm13_1_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_1_0_4
namespace hm13_0_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_0_0_5
namespace hm13_1_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_1_0_5
namespace hm13_0_0_6
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_0_0_6
namespace hm13_1_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_1_0_6
namespace hm13_0_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_0_0_7
namespace hm13_1_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock13_1
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
namespace hm13_0_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_0_0_8
namespace hm13_1_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_1_0_8
namespace hm13_0_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_0_0_9
namespace hm13_1_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_1_0_9
namespace hm13_0_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_0_0_10
namespace hm13_1_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_1_0_10
namespace hm13_0_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_0_0_11
namespace hm13_1_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_1_0_11
namespace hm13_0_0_12
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_0_0_12
namespace hm13_1_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_1_0_12
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock13_10
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
namespace hm13_0_1_2
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_0_1_2
namespace hm13_1_1_2
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_1_1_2
namespace hm13_0_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_0_1_3
namespace hm13_1_1_3
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_1_1_3
namespace hm13_0_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_0_1_4
namespace hm13_1_1_4
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_1_1_4
namespace hm13_0_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_0_1_5
namespace hm13_1_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_1_1_5
namespace hm13_0_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_0_1_6
namespace hm13_1_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_1_1_6
namespace hm13_0_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_0_1_7
namespace hm13_1_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock13_11
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
namespace hm13_0_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_0_1_8
namespace hm13_1_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_1_1_8
namespace hm13_0_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_0_1_9
namespace hm13_1_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_1_1_9
namespace hm13_0_1_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_0_1_10
namespace hm13_1_1_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_1_1_10
namespace hm13_0_1_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_0_1_11
namespace hm13_1_1_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_1_1_11
namespace hm13_0_1_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_0_1_12
namespace hm13_1_1_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm13_1_1_12
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock15_0
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
namespace hm15_0_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_0_0_2
namespace hm15_1_0_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_1_0_2
namespace hm15_0_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_0_0_3
namespace hm15_1_0_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_1_0_3
namespace hm15_0_0_4
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_0_0_4
namespace hm15_1_0_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_1_0_4
namespace hm15_0_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_0_0_5
namespace hm15_1_0_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_1_0_5
namespace hm15_0_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_0_0_6
namespace hm15_1_0_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_1_0_6
namespace hm15_0_0_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_0_0_7
namespace hm15_1_0_7
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock15_1
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
namespace hm15_0_0_8
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_0_0_8
namespace hm15_1_0_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_1_0_8
namespace hm15_0_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_0_0_9
namespace hm15_1_0_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_1_0_9
namespace hm15_0_0_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_0_0_10
namespace hm15_1_0_10
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_1_0_10
namespace hm15_0_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_0_0_11
namespace hm15_1_0_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_1_0_11
namespace hm15_0_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_0_0_12
namespace hm15_1_0_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_1_0_12
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock15_10
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
namespace hm15_0_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_0_1_2
namespace hm15_1_1_2
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_1_1_2
namespace hm15_0_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_0_1_3
namespace hm15_1_1_3
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_1_1_3
namespace hm15_0_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_0_1_4
namespace hm15_1_1_4
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_1_1_4
namespace hm15_0_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_0_1_5
namespace hm15_1_1_5
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_1_1_5
namespace hm15_0_1_6
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_0_1_6
namespace hm15_1_1_6
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_1_1_6
namespace hm15_0_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_0_1_7
namespace hm15_1_1_7
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock15_11
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
namespace hm15_0_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_0_1_8
namespace hm15_1_1_8
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_1_1_8
namespace hm15_0_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_0_1_9
namespace hm15_1_1_9
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_1_1_9
namespace hm15_0_1_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_0_1_10
namespace hm15_1_1_10
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_1_1_10
namespace hm15_0_1_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_0_1_11
namespace hm15_1_1_11
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_1_1_11
namespace hm15_0_1_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_0_1_12
namespace hm15_1_1_12
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm15_1_1_12
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock16_0
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
namespace hm16_1_0_3
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
end hm16_1_0_3
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock16_1
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
namespace hm16_0_0_10
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_0_0_10
namespace hm16_0_0_11
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
end hm16_0_0_11
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock16_11
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
namespace hm16_0_1_12
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
end hm16_0_1_12
end SharpPlanar.CachedData

end OAI
end


