-- Prove2me | Definitions.Def_OAIQ098D253
-- name    : OAIQ098D253
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T16:09:52.524778+00:00
-- url     : https://prove2.me/theorems/304b7235-dfb0-4bc0-840f-664c3e443658
-- title:
--   Definitions bundle OAIQ098D253 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3119 declarations of OpenAI's Lean: 3119 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.tm1_57_0.s1_15`, `OAI.SharpPlanar.CachedData.tm1_57_0.s1_2`, `OAI.SharpPlanar.CachedData.tm1_57_0.s1_3`, `OAI.SharpPlanar.CachedData.tm1_57_0.s1_4`, `OAI.SharpPlanar.CachedData.tm1_57_0.s1_5`, `OAI.SharpPlanar.CachedData.tm1_57_0.s1_6`, `OAI.SharpPlanar.CachedData.tm1_57_0.s1_7`, `OAI.SharpPlanar.CachedData.tm1_57_0.s1_8`, `OAI.SharpPlanar.CachedData.tm1_57_0.s1_9`, `OAI.SharpPlanar.CachedData.tm1_57_0.s2`, `OAI.SharpPlanar.CachedData.tm1_57_0.s2_0`, `OAI.SharpPlanar.CachedData.tm1_57_0.s2_1`, `OAI.SharpPlanar.CachedData.tm1_57_0.s2_10`, `OAI.SharpPlanar.CachedData.tm1_57_0.s2_11`, `OAI.SharpPlanar.CachedData.tm1_57_0.s2_12`, `OAI.SharpPlanar.CachedData.tm1_57_0.s2_13`, `OAI.SharpPlanar.CachedData.tm1_57_0.s2_14`, `OAI.SharpPlanar.CachedData.tm1_57_0.s2_15`, `OAI.SharpPlanar.CachedData.tm1_57_0.s2_2`, `OAI.SharpPlanar.CachedData.tm1_57_0.s2_3`, `OAI.SharpPlanar.CachedData.tm1_57_0.s2_4`, `OAI.SharpPlanar.CachedData.tm1_57_0.s2_5`, `OAI.SharpPlanar.CachedData.tm1_57_0.s2_6`, `OAI.SharpPlanar.CachedData.tm1_57_0.s2_7`, `OAI.SharpPlanar.CachedData.tm1_57_0.s2_8`, `OAI.SharpPlanar.CachedData.tm1_57_0.s2_9`, `OAI.SharpPlanar.CachedData.tm1_57_0.s3`, `OAI.SharpPlanar.CachedData.tm1_57_0.s3_0`, `OAI.SharpPlanar.CachedData.tm1_57_0.s3_1`, `OAI.SharpPlanar.CachedData.tm1_57_0.s3_10`, `OAI.SharpPlanar.CachedData.tm1_57_0.s3_11`, `OAI.SharpPlanar.CachedData.tm1_57_0.s3_12`, `OAI.SharpPlanar.CachedData.tm1_57_0.s3_13`, `OAI.SharpPlanar.CachedData.tm1_57_0.s3_14`, `OAI.SharpPlanar.CachedData.tm1_57_0.s3_15`, `OAI.SharpPlanar.CachedData.tm1_57_0.s3_2`, `OAI.SharpPlanar.CachedData.tm1_57_0.s3_3`, `OAI.SharpPlanar.CachedData.tm1_57_0.s3_4`, `OAI.SharpPlanar.CachedData.tm1_57_0.s3_5`, `OAI.SharpPlanar.CachedData.tm1_57_0.s3_6` and 3079 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_Certificate_TableMoments57`, `PlanarPacking_Certificate_TableMoments60`, `PlanarPacking_Certificate_TableMoments61`, `PlanarPacking_Certificate_TableMoments63`, `PlanarPacking_Certificate_TableMoments64`, `PlanarPacking_Certificate_TableMoments67`, `PlanarPacking_Certificate_TableMoments69`, `PlanarPacking_Certificate_TableMoments7`, `PlanarPacking_Certificate_TableMoments72`, `PlanarPacking_Certificate_TableMoments73`, `PlanarPacking_Certificate_TableMoments75`, `PlanarPacking_Certificate_TableMoments76`, `PlanarPacking_Certificate_TableMoments79`, `PlanarPacking_Certificate_TableMoments81`, `PlanarPacking_Certificate_TableMoments84`.
--
--   **Imports.** It imports the bundle `OAIQ098D003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098D274` and `OAIQ098D275`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098D003

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
open IntegerIntervals

namespace tm1_57_0
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-31480982213),(-31480982197)⟩,⟨(-17197999408),(-17197999390)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-54731742702),(-54731742685)⟩,⟨473063432,473063450⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-12631159352),(-12631159334)⟩,⟨20214769715,20214769731⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨3627475367,3627475383⟩,⟨2774503560,2774503576⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨128661443,128661460⟩,⟨(-412822594),(-412822578)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-19629148),(-19629131)⟩,⟨9600728,9600744⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨639708,639724⟩,⟨11132,11150⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-11615),(-11599)⟩,⟨(-2907),(-2891)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨141,157⟩,⟨46,62⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),6⟩,⟨(-13),11⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨2754239307984552112615,2754239307995115649433⟩,⟨3960480894914546929614,3960480894925110470670⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨8420645925039695158804,8420645925067462886943⟩,⟨2525362008147580590748,2525362008175348311945⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨2269704782362951003273,2269704782393342237098⟩,⟨(-5265302883908670145141),(-5265302883878278921394)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-3452062545662209011987),(-3452062545637857941068)⟩,⟨474430312686205651031,474430312710556725442⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨928551518084440757150,928551518107080057705⟩,⟨1493522747313044644873,1493522747335683944779⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨262266577015026564672,262266577025903153796⟩,⟨(-412646754811507994122),(-412646754800631404929)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-79194453639507491261),(-79194453636625187488)⟩,⟨5004646585733783547,5004646588616087326⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨6500360870508215327,6500360870969911440⟩,⟨5367607051465658888,5367607051927354999⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-169910170658653801),(-169910170610032318)⟩,⟨(-636660709466364559),(-636660709417743076)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-13060753879523791),(-13060753875808167)⟩,⟨40695247617510876,40695247621226501⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨2100987822585256,2100987822824704⟩,⟨(-1556642211377372),(-1556642211137926)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-171535685137089),(-171535685121529)⟩,⟨(-24564658573198),(-24564658557639)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨5298794767546,5298794768721⟩,⟨13315017862113,13315017863287⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨1449227560653,1449227560787⟩,⟨(-811738756132),(-811738755996)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-39457161915),(-39457161883)⟩,⟨(-275128949896),(-275128949861)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-33202476161),(-33202476141)⟩,⟨(-34639010847),(-34639010828)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
end tm1_57_0

namespace tm1_57_1
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-48029343030),(-48029343012)⟩,⟨140841727636,140841727654⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨41289785892,41289785914⟩,⟨223785995968,223785995989⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨92456517424,92456517442⟩,⟨36918230107,36918230128⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨8654767355,8654767373⟩,⟨(-17143699782),(-17143699762)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-1824290641),(-1824290623)⟩,⟨(-197746577),(-197746556)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨57458192,57458212⟩,⟨74116567,74116587⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-550275),(-550256)⟩,⟨(-2727325),(-2727304)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-803),(-783)⟩,⟨52784,52804⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨64,83⟩,⟨(-727),(-706)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-12),12⟩,⟨(-5),21⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨13786098284009390379852,13786098284049562048136⟩,⟨(-10702604666796009296285),(-10702604666755837640003)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨7472315144689043388367,7472315144795079478393⟩,⟨(-30979632062961906755336),(-30979632062855870633487)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-19615789543619227180952),(-19615789543502239387638)⟩,⟨(-7111942473342761772849),(-7111942473225773945710)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨2562690145749370640311,2562690145844292110036⟩,⟨12502793833601380590265,12502793833696302047175⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨5250817915781876849911,5250817915871454142420⟩,⟨(-3821811989671036264307),(-3821811989581458969432)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-1613247258725154570245),(-1613247258681364971875)⟩,⟨(-849182867200327924976),(-849182867156538326818)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨46072658186770316219,46072658198604469912⟩,⟨295617937462046202763,295617937473880356433⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨17849156652508142738,17849156654444441158⟩,⟨(-26773998665508683088),(-26773998663572384661)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-2371967823590954850),(-2371967823382484542)⟩,⟨931859389100859533,931859389309329843⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨164651760177482326,164651760193770564⟩,⟨30908333604270400,30908333620558641⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-7257887209103037),(-7257887208030613)⟩,⟨(-7428099229386242),(-7428099228313822)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨2969208586551,2969208657578⟩,⟨696794649877173,696794649948202⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨50142835462989,50142835468390⟩,⟨(-29666397044677),(-29666397039273)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-4248776808085),(-4248776807521)⟩,⟨(-5327337446449),(-5327337445885)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-1092804222400),(-1092804222304)⟩,⟨350097226956,350097227056⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-118134617519),(-118134617489)⟩,⟨159840128599,159840128629⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨1317431996086481355869,1317431996170728068350⟩,⟨(-6782096714209253245167),(-6782096714125006525521)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨1385363621810223642739717,1385363621810223668849960⟩,⟨2618534409747494763187201,2618534409747494789352828⟩⟩
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
open IntegerIntervals

namespace tm1_60_0
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-2981759600),(-2981759583)⟩,⟨(-3094791248),(-3094791232)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-6097008633),(-6097008616)⟩,⟨(-1706699498),(-1706699482)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-1837858594),(-1837858578)⟩,⟨1803158971,1803158987⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨304273896,304273912⟩,⟨326626760,326626777⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨13683607,13683623⟩,⟨(-34505288),(-34505272)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-1408215),(-1408198)⟩,⟨759561,759577⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨38383,38400⟩,⟨(-6080),(-6064)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-596),(-579)⟩,⟨38,54⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-4),17⟩,⟨(-14),3⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),15⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-2456899056635747207337),(-2456899056621197330839)⟩,⟨1189310656933914537494,1189310656948464410075⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-2015025067480367296696),(-2015025067442706311968)⟩,⟨4413510841948446984692,4413510841986107970694⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨2631387715677196399714,2631387715717167904745⟩,⟨1454017010026995632859,1454017010066967143586⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-177402595703801644498),(-177402595673360923324)⟩,⟨(-1686594295237043343971),(-1686594295206602624450)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-643645964852121356352),(-643645964825592549707)⟩,⟨448742270018136751796,448742270044665558722⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨179877569408185830881,179877569419939094740⟩,⟨79052556350101964751,79052556361855228587⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-9157808077837078592),(-9157808075016691494)⟩,⟨(-26726812040517785565),(-26726812037697398462)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-763627288757402910),(-763627288355441186)⟩,⟨2508498057364185017,2508498057766146743⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨124469071223828872,124469071260910582⟩,⟨(-126093621952588652),(-126093621915506945)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-9242042382412195),(-9242042379958663)⟩,⟨3481577948788173,3481577951241708⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨515316922260166,515316922396139⟩,⟨64669918015240,64669918151214⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-21286216109850),(-21286216102225)⟩,⟨(-20862153847797),(-20862153840175)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-300220693419),(-300220692907)⟩,⟨2147178331051,2147178331559⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨225543657088,225543657148⟩,⟨(-19909597595),(-19909597537)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨7405997493,7405997516⟩,⟨(-34425490885),(-34425490865)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-2523018233),(-2523018216)⟩,⟨(-5283126799),(-5283126781)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-415252185662349381129),(-415252185634988183019)⟩,⟨978949693317668991977,978949693345030190362⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-125388360359965745951553),(-125388360359965741170984)⟩,⟨(-449256745696531990030317),(-449256745696531985241758)⟩⟩
end tm1_60_0

namespace tm1_60_1
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-10540779375),(-10540779357)⟩,⟨14376761528,14376761545⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-2605158885),(-2605158868)⟩,⟨26193493980,26193493997⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨8773897184,8773897201⟩,⟨6215784899,6215784918⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨1114025759,1114025780⟩,⟨(-1510560725),(-1510560706)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-154854049),(-154854030)⟩,⟨(-28741867),(-28741846)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨4418134,4418153⟩,⟨5255448,5255468⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-61624),(-61606)⟩,⟨(-157386),(-157365)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨776,795⟩,⟨2466,2486⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-20),0⟩,⟨(-36),(-15)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨4763231858754947166744,4763231858810278228594⟩,⟨8650806226563259048075,8650806226618590122298⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨16373995128883052823093,16373995129026866353688⟩,⟨6418932322700080610512,6418932322843894132753⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨4715437025043454510414,4715437025197315316355⟩,⟨(-9871318545205913673163),(-9871318545052052886977)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-6120860795498885298914),(-6120860795380234530609)⟩,⟨1053088239356894710743,1053088239475545485158⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨1825555795825085525314,1825555795930041370443⟩,⟨2249485503436436277802,2249485503541392121925⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨239090145589853843521,239090145637166164468⟩,⟨(-692348326689462117382),(-692348326642149796385)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-97177179151828702460),(-97177179140250781986)⟩,⟨43570156922138151155,43570156933716071641⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨9820273460957162052,9820273462642616450⟩,⟨1923363217960211928,1923363219645666326⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-538888259024402324),(-538888258865441818)⟩,⟨(-423031062669582310),(-423031062510621803)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨18048147877742281,18048147888495775⟩,⟨34238449410616192,34238449421369689⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-23059878511791),(-23059877902930)⟩,⟨(-2062245323081392),(-2062245322472526)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-70493865862038),(-70493865827274)⟩,⟨96901740623605,96901740658369⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨8812041769799,8812041772113⟩,⟨(-145695987241),(-145695984929)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-230398187968),(-230398187743)⟩,⟨(-899731226957),(-899731226733)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-145232994054),(-145232994009)⟩,⟨(-6439921310),(-6439921265)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-19799519164),(-19799519143)⟩,⟨14004850501,14004850520⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨3618095221275824758543,3618095221382051103598⟩,⟨1308958030225323557986,1308958030331549901282⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-1598733213752612475870032),(-1598733213752612457675503)⟩,⟨537139080148334212654297,537139080148334230817943⟩⟩
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
open IntegerIntervals

namespace tm1_61_0
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨2097263838,2097263854⟩,⟨(-299522845),(-299522829)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨2398218012,2398218028⟩,⟨(-1940591828),(-1940591811)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-211401816),(-211401800)⟩,⟨(-1207955029),(-1207955013)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-202711314),(-202711298)⟩,⟨34823259,34823276⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨9837970,9837986⟩,⟨13098347,13098364⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨10676,10693⟩,⟨(-669660),(-669644)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-4656),(-4640)⟩,⟨14558,14574⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨63,79⟩,⟨(-211),(-193)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-10),12⟩,⟨(-7),16⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨1363913510206759156413,1363913510222947779395⟩,⟨(-1799149154964255650321),(-1799149154948067026684)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-197352898656953223889),(-197352898615264998671)⟩,⟨(-3974791231307677443345),(-3974791231265989210378)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-2424108128196581752026),(-2424108128152786093664)⟩,⟨(-33876714092696681618),(-33876714048901022280)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨772410623570319766213,772410623603113867410⟩,⟨1087688206519989660993,1087688206552783761292⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨245185250563452568762,245185250591424032861⟩,⟨(-547208537105101060992),(-547208537077129596816)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-143180488020718327756),(-143180488008655537022)⟩,⟨23067733446633193967,23067733458695984713⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨16202112250123024555,16202112252923641133⟩,⟨11778468768782011026,11778468771582627607⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-624782370634408095),(-624782370250493789)⟩,⟨(-1663984460056198503),(-1663984459672284196)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-8999916457529562),(-8999916423640727)⟩,⟨114056242940937426,114056242974826260⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨2712056324142581,2712056326279744⟩,⟨(-5422773258489713),(-5422773256352552)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-238026783270486),(-238026783157851)⟩,⟨187721692471715,187721692584349⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨16550131278100,16550131284113⟩,⟨(-1001865950702),(-1001865944688)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-775205608320),(-775205607933)⟩,⟨(-856834971746),(-856834971360)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-63532571388),(-63532571339)⟩,⟨97695815172,97695815221⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨11623298397,11623298416⟩,⟨13330267595,13330267618⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨2854692421,2854692438⟩,⟨532165891,532165908⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-61260218468531258744),(-61260218438911001904)⟩,⟨(-872341065625591787953),(-872341065595971529683)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨261122257147891153063397,261122257147891157800282⟩,⟨285054174948792627038693,285054174948792631779896⟩⟩
end tm1_61_0

namespace tm1_61_1
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-2707692034),(-2707692018)⟩,⟨(-8360594411),(-8360594394)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-9670586645),(-9670586629)⟩,⟨(-8425086403),(-8425086385)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-4807565881),(-4807565864)⟩,⟨1764737159,1764737179⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨300969283,300969300⟩,⟨810714758,810714774⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨46485427,46485445⟩,⟨(-51670979),(-51670957)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-2822995),(-2822975)⟩,⟨538185,538203⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨66182,66205⟩,⟨6139,6159⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-957),(-939)⟩,⟨(-110),(-92)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-2),22⟩,⟨(-13),9⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-6759052742262636795630),(-6759052742201073831378)⟩,⟨(-4586186111841136978474),(-4586186111779574018190)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-14347593571070793177509),(-14347593570911601731264)⟩,⟨1501856962091735232104,1501856962250926648617⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨398543451021429958847,398543451190008986448⟩,⟨8812597716693010483862,8812597716861589509967⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨3789282578210495298236,3789282578338315982693⟩,⟨(-3083582158757882973600),(-3083582158630062286441)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-2080858718946862754672),(-2080858718836203224525)⟩,⟨(-755690626693694184165),(-755690626583034654176)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨129171512995092437012,129171513043648437255⟩,⟨524952422896668104167,524952422945224104339⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨38640876759803555398,38640876771299657586⟩,⟨(-64865030176660367832),(-64865030165164265637)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-6073889095189013771),(-6073889093579335210)⟩,⟨3018612058608398408,3018612060218076972⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨442099764608903621,442099764754167580⟩,⟨(-15295788644408811),(-15295788499144849)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-22408076279098204),(-22408076269731912)⟩,⟨(-7900133737209492),(-7900133727843203)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨866647595130821,866647595635132⟩,⟨835379056919198,835379057423510⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-13689265766957),(-13689265739555)⟩,⟨(-65237416348358),(-65237416320948)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-2953110651231),(-2953110649486)⟩,⟨3652307698183,3652307699930⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨437639540835,437639541007⟩,⟨192274886384,192274886553⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨46257613077,46257613114⟩,⟨(-56493160571),(-56493160534)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨170903498,170903519⟩,⟨(-12027569160),(-12027569139)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-3139586660037980844233),(-3139586659923042410884)⟩,⟨392013227375284527503,392013227490222955403⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨980306246123575911010104,980306246123575929023618⟩,⟨(-996444848325414141980070),(-996444848325414123981600)⟩⟩
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
open IntegerIntervals

namespace tm1_63_0
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-229835544),(-229835528)⟩,⟨(-460700325),(-460700309)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-622573625),(-622573609)⟩,⟨(-385914070),(-385914054)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-238861383),(-238861366)⟩,⟨142700322,142700338⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨23967581,23967597⟩,⟨36520324,36520341⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨1401152,1401168⟩,⟨(-2868568),(-2868551)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-101142),(-101124)⟩,⟨59690,59707⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨2230,2248⟩,⟨(-777),(-761)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-33),(-16)⟩,⟨3,20⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-12),16⟩,⟨(-16),15⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-447526913626506199337),(-447526913606465542582)⟩,⟨(-1478262659859188798015),(-1478262659839148138244)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-2260858967824488985016),(-2260858967773407431912)⟩,⟨(-1434678477321628579306),(-1434678477270547025470)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-894526552400500962226),(-894526552347922047811)⟩,⟨1298225252751066623762,1298225252803645535123⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨823438950103639431982,823438950141703926348⟩,⟨(-59094649023166983257),(-59094648985102488117)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-214632803449004498138),(-214632803417903182259)⟩,⟨(-276798270101314933669),(-276798270070213617913)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-20638010701662570613),(-20638010688953124042)⟩,⟨76300833913604986000,76300833926314432576⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨8344365678658419170,8344365681420743646⟩,⟨(-5645824680999301944),(-5645824678236977464)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-813370721304681967),(-813370720954341080)⟩,⟨79209662858530124,79209663208871014⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨46258406740663619,46258406768979248⟩,⟨11803729058857173,11803729087172801⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-1959530996549473),(-1959530994927241)⟩,⟨(-1178810188030347),(-1178810186408113)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨65115440071468,65115440148786⟩,⟨80245808000774,80245808078094⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-821608187193),(-821608183451)⟩,⟨(-5067344358341),(-5067344354597)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-200741245238),(-200741245013)⟩,⟨259766006858,259766007084⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨29155740625,29155740656⟩,⟨10161642015,10161642050⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨2394965641,2394965658⟩,⟨(-3764450966),(-3764450949)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-90342263),(-90342247)⟩,⟨(-708646099),(-708646083)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-501194823323656821814),(-501194823288870310460)⟩,⟨(-313310647382774939968),(-313310647347988428385)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨263948478700801107002126,263948478700801113175406⟩,⟨(-29066362752939977014835),(-29066362752939970845143)⟩⟩
end tm1_63_0

namespace tm1_63_1
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-1720518556),(-1720518539)⟩,⟨1265293076,1265293092⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-1132634396),(-1132634380)⟩,⟨2826719508,2826719525⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨763566416,763566435⟩,⟨875782277,875782295⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨132344095,132344117⟩,⟨(-127325370),(-127325350)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-13087130),(-13087109)⟩,⟨(-3488023),(-3488003)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨338829,338847⟩,⟨372959,372980⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-5360),(-5341)⟩,⟨(-8807),(-8787)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨63,87⟩,⟨94,114⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-16),15⟩,⟨(-16),13⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-5255870456151347288423),(-5255870456075135663480)⟩,⟨1897469424491796078417,1897469424568007693386⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-4744775962514386365235),(-4744775962319327046256)⟩,⟨8467283370632581657929,8467283370827640976337⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨4907905903667400587806,4907905903869783645408⟩,⟨2969829354356399127846,2969829354558782196343⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-413495098324167868250),(-413495098175811891222)⟩,⟨(-2994592490457622675494),(-2994592490309266701368)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-961432503380882436936),(-961432503257849359225)⟩,⟨864621251289088597698,864621251412121675842⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨289703028499104360653,289703028550258489701⟩,⟨53521385906024814758,53521385957178943797⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-24054930771667498524),(-24054930760329865999)⟩,⟨(-29378123315792457806),(-29378123304454825281)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨616472241811230564,616472243279959071⟩,⟨3056567556396050204,3056567557864778711⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨25136767330961408,25136767452320363⟩,⟨(-182845111791099130),(-182845111669740171)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-3628173429542006),(-3628173422433330)⟩,⟨8192876221321827,8192876228430507⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨280643037527740,280643037873875⟩,⟨(-299311141234711),(-299311140888577)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-19671111838602),(-19671111821562)⟩,⟨6237260439687,6237260456726⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨1169391782767,1169391783764⟩,⟨642677833127,642677834126⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨21767857567,21767857664⟩,⟨(-124756177880),(-124756177785)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-16972353108),(-16972353084)⟩,⟨(-7156452082),(-7156452056)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-2829727466),(-2829727448)⟩,⟨865721440,865721459⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-1033563629333153434542),(-1033563629198298037747)⟩,⟨1871939299277648148397,1871939299412503544837⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-154521883879393366773987),(-154521883879393343335386)⟩,⟨(-947666941016891700422791),(-947666941016891676969348)⟩⟩
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
open IntegerIntervals

namespace tm1_64_0
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨250474206,250474222⟩,⟨40987910,40987926⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨328994056,328994072⟩,⟨(-138408445),(-138408429)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨8529313,8529330⟩,⟨(-132271531),(-132271515)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-20135005),(-20134989)⟩,⟨9938,9954⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨757112,757130⟩,⟨1189207,1189223⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-1104),(-1088)⟩,⟨(-49195),(-49178)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-135),(-118)⟩,⟨915,932⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-12),4⟩,⟨(-17),0⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-16),16⟩,⟨(-15),16⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨884962180934163481601,884962180956461357923⟩,⟨921314444352066547462,921314444374364424158⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨2187945770860398680554,2187945770916943504339⟩,⟨192211485299932479763,192211485356477300132⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨143020602392177516848,143020602449789342543⟩,⟨(-1263329857120061452625),(-1263329857062449627919)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-541862946130775815278),(-541862946089764511083)⟩,⟨358025928450265115403,358025928491276420065⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨249501786188596893750,249501786221394696671⟩,⟨97097520763974203270,97097520796772006165⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-17745589376608195606),(-17745589363561038614)⟩,⟨(-55601960743524489114),(-55601960730477332130)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-2548334924344357211),(-2548334921600571452)⟩,⟨6677403644409622488,6677403647153408247⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨405176121172815474,405176121507547153⟩,⟨(-378288389238760462),(-378288388904028783)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-27782623037269928),(-27782623011381980)⟩,⟨13410623097949733,13410623123837679⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨1375565751894831,1375565753308481⟩,⟨(-285463409389563),(-285463407975914)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-60071784932033),(-60071784867961)⟩,⟨(-5847524613512),(-5847524549438)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨2398021420670,2398021423628⟩,⟨1553256808400,1553256811355⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-37508434165),(-37508433990)⟩,⟨(-170948812048),(-170948811873)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-13376635737),(-13376635710)⟩,⟨8583524241,8583524268⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨794193049,794193066⟩,⟨2095577908,2095577928⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨310433587,310433603⟩,⟨170822802,170822818⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨483942030214086717946,483942030251822831057⟩,⟨42671632827152765294,42671632864888877806⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-184198641176833867217303),(-184198641176833865009666)⟩,⟨120447707247693073737731,120447707247693075942046⟩⟩
end tm1_64_0

namespace tm1_64_1
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-9626042),(-9626025)⟩,⟨(-1052786535),(-1052786519)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-803257579),(-803257562)⟩,⟨(-1247627955),(-1247627939)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-549884773),(-549884755)⟩,⟨63032491,63032510⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨15634204,15634222⟩,⟨83190826,83190842⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨4331730,4331748⟩,⟨(-4123670),(-4123651)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-205706),(-205687)⟩,⟨47387,47409⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨4028,4050⟩,⟨(-334),(-315)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-53),(-34)⟩,⟨(-1),22⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-15),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨3160635994978246169707,3160635995063041611771⟩,⟨(-3372160003683110474845),(-3372160003598315033238)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨262193879953127450162,262193880169047818563⟩,⟨(-7957150775198324183416),(-7957150774982403801313)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-4619377009309235828379),(-4619377009087482962050)⟩,⟨(-247700788894081692824),(-247700788672328823963)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨1438133467197571330837,1438133467357408708329⟩,⟨1893943168000772022969,1893943168160609398996⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨290438574606978376922,290438574736718012583⟩,⟨(-944650056494494315712),(-944650056364754680009)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-201157035564837855767),(-201157035512326945546)⟩,⟨82775969380284649407,82775969432795559658⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨25933969569730322019,25933969580991232162⟩,⟨7271569362794047258,7271569374054957398⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-1593023213796120040),(-1593023212392916117)⟩,⟨(-1391050661797131295),(-1391050660393927373)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨63638693027153309,63638693138100393⟩,⟨100860174564801994,100860174675749079⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-1779808019543192),(-1779808013348919)⟩,⟨(-5208744187837753),(-5208744181643481)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨9297601188626,9297601475446⟩,⟨239441365141245,239441365428065⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨4771983983820,4771983997260⟩,⟨(-10446488180337),(-10446488166896)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-662841476016),(-662841475260)⟩,⟨258135583006,258135583760⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨43623477583,43623477656⟩,⟨48441116130,48441116206⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨7983065835,7983065859⟩,⟨(-4675726413),(-4675726388)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨479717093,479717110⟩,⟨(-1387134520),(-1387134503)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨59211781760046401194,59211781906269427727⟩,⟨(-1756494347910724597343),(-1756494347764501568413)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨469527403819598140060661,469527403819598148436541⟩,⟨642529219593501199950852,642529219593501208338799⟩⟩
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
open IntegerIntervals

namespace tm1_67_0
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨27160324,27160340⟩,⟨13670622,13670638⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨41023413,41023429⟩,⟨(-4770066),(-4770050)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨4275874,4275890⟩,⟨(-13680917),(-13680901)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-1944845),(-1944829)⟩,⟨(-334593),(-334577)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨57036,57053⟩,⟨107327,107343⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-224),(-208)⟩,⟨(-3624),(-3608)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-6),12⟩,⟨47,63⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-15),11⟩,⟨(-16),11⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-593149903929707593157),(-593149903898994784169)⟩,⟨413140929532616961439,413140929563329769797⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-270554248944422251068),(-270554248867722686205)⟩,⟨1181604731638389272903,1181604731715088839056⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨651903120832785976698,651903120908582725316⟩,⟨140443180551212315517,140443180627009064904⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-165004044374584139060),(-165004044323281536082)⟩,⟨(-269806606291749691783),(-269806606240447089041)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-37952322804872416451),(-37952322766397386783)⟩,⟨113436674856454665864,113436674894929695543⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨21113683364176121326,21113683378297631542⟩,⟨(-10357259450918032355),(-10357259436796522136)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-2541115156016665920),(-2541115153326165556)⟩,⟨(-261652040367798216),(-261652037677297849)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨157482675914565749,157482676206725213⟩,⟨72165289018853859,72165289311013326⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-6906830365167307),(-6906830345367960)⟩,⟨(-4668161067712433),(-4668161047913083)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨249611530473061,249611531409285⟩,⟨209997494534572,209997495470798⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-7823478973738),(-7823478937240)⟩,⟨(-9150303021107),(-9150302984608)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨173371431841,173371433298⟩,⟨461555403474,461555404932⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨7960290286,7960290369⟩,⟨(-25311226512),(-25311226428)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-2145522050),(-2145522029)⟩,⟨315382450,315382473⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨2002802,2002819⟩,⟨283990285,283990301⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨29437883,29437899⟩,⟨31665934,31665950⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-66005668866625309786),(-66005668818273359570)⟩,⟨261377949534608425251,261377949582960375670⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-50703812686091728855655),(-50703812686091727345355)⟩,⟨(-114579564570950762330427),(-114579564570950760817800)⟩⟩
end tm1_67_0

namespace tm1_67_1
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨36667027,36667043⟩,⟨(-120684774),(-120684758)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-49021663),(-49021646)⟩,⟨(-164544309),(-164544292)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-59386676),(-59386657)⟩,⟨(-7427757),(-7427740)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨122976,122997⟩,⟨8294344,8294362⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨400184,400202⟩,⟨(-325097),(-325076)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-15013),(-14996)⟩,⟨4040,4060⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨229,249⟩,⟨(-71),(-51)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-16),11⟩,⟨(-11),16⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨1605222989142916638699,1605222989259712628057⟩,⟨2064564889478477794286,2064564889595273785432⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨4330222107856215593380,4330222108149094593028⟩,⟨745119174464606396207,745119174757485390277⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨369872611013211547572,369872611304949787919⟩,⟨(-2397864627372911313189),(-2397864627081173075091)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-946113168466904550194),(-946113168266971981097)⟩,⟨667509454623903151651,667509454823835721526⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨427745862573728738296,427745862725910098773⟩,⟨109250335297569700678,109250335449751061143⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-44858611240870913232),(-44858611184043988114)⟩,⟨(-75278040058823428951),(-75278040001996503845)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-111059705263937016),(-111059694223552748)⟩,⟨9624402139305164295,9624402150345548559⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨212857972553612565,212857973778130727⟩,⟨(-625585640095774085),(-625585638871255920)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-14918075337231601),(-14918075252393921)⟩,⟨28560134872671345,28560134957509030⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨694894368655522,694894372757094⟩,⟨(-1072429049519932),(-1072429045418359)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-31787294462948),(-31787294299615)⟩,⟨35684761377481,35684761540812⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨1733799365113,1733799371714⟩,⟨(-959582128566),(-959582121962)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-106629497548),(-106629497213)⟩,⟨(-16048449509),(-16048449174)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨2700759601,2700759640⟩,⟨8473834684,8473834725⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨1154554131,1154554151⟩,⟨(-203694721),(-203694701)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨108635345,108635362⟩,⟨(-142384433),(-142384416)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨957029889301397712262,957029889488515728688⟩,⟨187054587559138118740,187054587746256134287⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-404228966189135581234894),(-404228966189135575487803)⟩,⟨204607777006453655254449,204607777006453660992879⟩⟩
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
open IntegerIntervals

namespace tm1_69_0
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨1071172,1071189⟩,⟨(-7311506),(-7311490)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-4273348),(-4273332)⟩,⟨(-8827672),(-8827656)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-3248317),(-3248301)⟩,⟨198953,198970⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨99234,99250⟩,⟨407864,407880⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨13625,13643⟩,⟨(-19450),(-19432)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-529),(-513)⟩,⟨356,372⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-5),11⟩,⟨(-16),3⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-16),15⟩,⟨(-16),16⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-9799731526375134222),(-9799731488354020599)⟩,⟨494413206954851076045,494413206992872190847⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨544105044774141270708,544105044868128975523⟩,⟨607587073289444726309,607587073383432432203⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨311907800917360627460,311907801008374764797⟩,⟨(-301421730436346398604),(-301421730345332262060)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-195787392251532298341),(-195787392191961387952)⟩,⟨229438166454758833,229438226025669389⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨47951877197142790437,47951877239949791674⟩,⟨50907906928096833379,50907906970903834593⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-377810308747827538),(-377810293855781140)⟩,⟨(-12833184188165776401),(-12833184173273730003)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-563211449321313964),(-563211446664473198)⟩,⟨1158182986592328051,1158182989249168819⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨51098320477070268,51098320744054084⟩,⟨(-61382144806215489),(-61382144539231670)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-2422647674787408),(-2422647658218422)⟩,⟨2510239439701827,2510239456270812⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨86703687079495,86703687791302⟩,⟨(-87765942036170),(-87765941324361)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-3094943047946),(-3094943022842)⟩,⟨2710610540537,2710610565633⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨137205404607,137205405522⟩,⟨(-67583649669),(-67583648757)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-7485421490),(-7485421437)⟩,⟨(-970277488),(-970277431)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨216461145,216461165⟩,⟨532576291,532576308⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨68589383,68589399⟩,⟨(-20740308),(-20740291)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨5199942,5199958⟩,⟨(-9278842),(-9278826)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨116247556127369720531,116247556184575395160⟩,⟨139996989445360435942,139996989502566110839⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-84080907169614754745181),(-84080907169614752886938)⟩,⟨(-18388753132265186962759),(-18388753132265185104976)⟩⟩
end tm1_69_0

namespace tm1_69_1
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-30642709),(-30642693)⟩,⟨793046,793062⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-33072958),(-33072941)⟩,⟨23842757,23842776⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨3225287,3225304⟩,⟨13199638,13199656⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨1608280,1608299⟩,⟨(-725609),(-725592)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-92061),(-92042)⟩,⟨(-40892),(-40871)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨1972,1989⟩,⟨1872,1891⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-41),(-19)⟩,⟨(-32),(-14)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨1788118456033418442301,1788118456178006638394⟩,⟨(-58442732991135093723),(-58442732846546902004)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨2091228066568452535130,2091228066927343673506⟩,⟨(-2089644741723969107891),(-2089644741365077972826)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-1161762430324979885492),(-1161762429974678570882)⟩,⟨(-1067959143631598258366),(-1067959143281296940814)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨47775057508428649149,47775057740572940203⟩,⟨715152883956117453758,715152884188261744173⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨174506145568047806692,174506145737351794017⟩,⟨(-190147872811426382633),(-190147872642122395226)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-47541273531570250943),(-47541273471648095473)⟩,⟨5284800406376473104,5284800466298628577⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨4538005083119325358,4538005094020402309⟩,⟨1716669256611938279,1716669267513015230⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-252686870055524263),(-252686868936655982)⟩,⟨(-170146656450882944),(-170146655332014663)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨10694423100735219,10694423171722698⟩,⟨8210660312716923,8210660383704404⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-383268645873362),(-383268642755333)⟩,⟨(-294361019241380),(-294361016123353)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨12321190508548,12321190620837⟩,⟨10717134153168,10717134265456⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-348991861472),(-348991857352)⟩,⟨(-505990683148),(-505990679034)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨808795998,808796194⟩,⟨30661943286,30661943482⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨2011625906,2011625933⟩,⟨(-1229519329),(-1229519299)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-131643687),(-131643669)⟩,⟨(-264895409),(-264895392)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-41527042),(-41527026)⟩,⟨(-14722682),(-14722666)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨482769943860683814105,482769944081891356242⟩,⟨(-447367059609307839898),(-447367059388100298644)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-50614112430915902772616),(-50614112430915895714908)⟩,⟨307071262991005851227447,307071262991005858287445⟩⟩
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
open IntegerIntervals

namespace tm1_7_0
noncomputable def s0_0 : CBox := ⟨⟨253259,253275⟩,⟨92356,92372⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨443656,443672⟩,⟨354000,354016⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨113218,113234⟩,⟨458271,458287⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-165438),(-165422)⟩,⟨176504,176520⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-76619),(-76601)⟩,⟨(-43822),(-43805)⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨15010,15026⟩,⟨(-21060),(-21044)⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨3519,3538⟩,⟨5953,5970⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-1908),(-1890)⟩,⟨(-330),(-312)⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨540,557⟩,⟨(-290),(-274)⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-137),(-121)⟩,⟨195,211⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-7),10⟩,⟨(-131),(-114)⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨40,57⟩,⟨45,61⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-58),(-42)⟩,⟨4,21⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),0⟩,⟨(-44),(-28)⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨12,30⟩,⟨(-22),(-6)⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨0,16⟩,⟨(-13),5⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-29842441108189),(-29842441108173)⟩,⟨(-23809893744636),(-23809893744620)⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-61016959934273),(-61016959934257)⟩,⟨(-52830624466894),(-52830624466878)⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-46880990583492),(-46880990583475)⟩,⟨(-48319125155599),(-48319125155581)⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-19921134928780),(-19921134928764)⟩,⟨(-27716847525317),(-27716847525301)⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-4549351477984),(-4549351477968)⟩,⟨(-10937288979541),(-10937288979523)⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-161671938576),(-161671938557)⟩,⟨(-3026719601070),(-3026719601054)⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨254456205461,254456205479⟩,⟨(-553760814565),(-553760814549)⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨90557041563,90557041579⟩,⟨(-48516410941),(-48516410923)⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨14837926003,14837926021⟩,⟨4962642809,4962642826⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨660508776,660508793⟩,⟨2247460888,2247460908⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-264841168),(-264841151)⟩,⟨266298922,266298938⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-65798879),(-65798863)⟩,⟨(-21912926),(-21912910)⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-2866782),(-2866765)⟩,⟨(-15194519),(-15194502)⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨2798700,2798716⟩,⟨(-3137190),(-3137174)⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨1291180,1291197⟩,⟨(-223335),(-223318)⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨308643,308659⟩,⟨57257,57273⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨18945342775227063330,18945342775227063568⟩,⟨(-74131559685337354907),(-74131559685337354669)⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨34913292722659182231,34913292722659182804⟩,⟨(-180393964466184914073),(-180393964466184913498)⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨15738555874556192577,15738555874556193234⟩,⟨(-195190204271537945118),(-195190204271537944460)⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-9956046983702312783),(-9956046983702312262)⟩,⟨(-139452972745469851572),(-139452972745469851050)⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-18474436065565740325),(-18474436065565740010)⟩,⟨(-70875998046653409911),(-70875998046653409597)⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-13207578290320114809),(-13207578290320114657)⟩,⟨(-26436939668078015614),(-26436939668078015462)⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-6084103335548195290),(-6084103335548195225)⟩,⟨(-7460562675742264172),(-7460562675742264108)⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-2080433746981580648),(-2080433746981580619)⟩,⟨(-1667433824224418628),(-1667433824224418594)⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-579068203199500033),(-579068203199500011)⟩,⟨(-318903480023409892),(-318903480023409869)⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-142145865856677952),(-142145865856677931)⟩,⟨(-59347670147329247),(-59347670147329226)⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-33018978224735412),(-33018978224735389)⟩,⟨(-12566929797521682),(-12566929797521661)⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-7698784112142086),(-7698784112142064)⟩,⟨(-3253394782911908),(-3253394782911886)⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-1898276867767155),(-1898276867767138)⟩,⟨(-984032705142410),(-984032705142390)⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-517410493504977),(-517410493504957)⟩,⟨(-329038011266352),(-329038011266331)⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-154665560121917),(-154665560121900)⟩,⟨(-114644954729214),(-114644954729196)⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-35758141957334),(-35758141957317)⟩,⟨(-28738519961448),(-28738519961432)⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-477341842518198269347397),(-477341842518195941263276)⟩,⟨255213546259776223319449,255213546259778551377587⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-1175563634939259222495854),(-1175563634939254654962198)⟩,⟨751846972562846233935802,751846972562850801397127⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-1287915403629603743251473),(-1287915403629599938175416)⟩,⟨1139437233652618339369198,1139437233652622144364134⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-890205933472472552825041),(-890205933472470709606719)⟩,⟨1257454727373558639512253,1257454727373560482676898⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-345742208506007096247177),(-345742208506006587192977)⟩,⟨1054562702262225222463446,1054562702262225731499910⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨24491415603009551230519,24491415603009631393237⟩,⟨675170833100512341140064,675170833100512421308235⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨146488520384367782551882,146488520384367790440902⟩,⟨327028406643724986920996,327028406643724994821660⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨123256710630596025333753,123256710630596026177252⟩,⟨115716835599032402230865,115716835599032403082173⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨67789561611312247119273,67789561611312247378868⟩,⟨25731988450929116948421,25731988450929117209953⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨29084787604907445600450,29084787604907445711499⟩,⟨(-318589427396204005408),(-318589427396203894262)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨10594334266936153708024,10594334266936153756704⟩,⟨(-3927882133701608252516),(-3927882133701608204027)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨3489076489349736861927,3489076489349736883191⟩,⟨(-2689128468550076597327),(-2689128468550076576203)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨1095593398759669553771,1095593398759669563220⟩,⟨(-1392965703236720635496),(-1392965703236720626118)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨341613210795002060062,341613210795002064349⟩,⟨(-656753992845291894838),(-656753992845291890579)⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨105913471156057704044,105913471156057705905⟩,⟨(-284952439141265423099),(-284952439141265421247)⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨24162934319129496846,24162934319129497378⟩,⟨(-79654696736642931440),(-79654696736642930908)⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨64066069572137660864766842,64066069572139855378898601⟩,⟨51374979236429402400843133,51374979236431596915665239⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨189218795345102896478846664,189218795345110545003760126⟩,⟨127206493722286698923386068,127206493722294347447879551⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨294463160154277905343728531,294463160154294146653434371⟩,⟨135097600784575505145996201,135097600784591746448752220⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨347097077855149044226945546,347097077855177816940114215⟩,⟨69698771999014781811231590,69698771999043554507202804⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨322614902875239221151860554,322614902875280164736948715⟩,⟨(-32385764512362906972717883),(-32385764512321963413358085)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨232390255945723587969114921,232390255945783679968350583⟩,⟨(-115356183065683887631456849),(-115356183065623795652564152)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨120691597450359354858332172,120691597450435722094688245⟩,⟨(-143523966538070097215884275),(-143523966537993729987333196)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨32499735898236470053550060,32499735898300068055939984⟩,⟨(-121350263167997104437947923),(-121350263167933506434649111)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-13807373186983748869612715),(-13807373186949171314999136)⟩,⟨(-78020790596666748687365765),(-78020790596632171128689140)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-26322202884510619628688128),(-26322202884496741809111034)⟩,⟨(-39496991725684406104266899),(-39496991725670528281434427)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-22273923052518834407829092),(-22273923052512821379325234)⟩,⟨(-15591607695278597257891500),(-15591607695272584228329732)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-14385643165761233578513103),(-14385643165759245989169218)⟩,⟨(-4252323788017718707722135),(-4252323788015731118247063)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-8033151745340587145234034),(-8033151745340026817662968)⟩,⟨(-125487761229991458448956),(-125487761229431131012954)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-4084285936383943295769092),(-4084285936383791020525497)⟩,⟨835313985919677241641780,835313985919829516737915⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-1856537074928884980659427),(-1856537074928842372317938)⟩,⟨691393800742326492423285,691393800742369100671514⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-529000973958667377689157),(-529000973958658092604987)⟩,⟨247524135334299527379868,247524135334308812433586⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨52701758708274214236020009,52701758708274214911350794⟩,⟨(-36040918465630727027092319),(-36040918465630726410357993)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨108316072506824878568969358,108316072506824880565784505⟩,⟨(-139310866791354167279516499),(-139310866791354165410300965)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-20324433112656376251745668),(-20324433112656373109319759)⟩,⟨(-271448278452934885164734457),(-271448278452934882091509427)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-480164784868499513830598240),(-480164784868499509775134257)⟩,⟨(-308192045627285994806216850),(-308192045627285990637584985)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-1257361876383912357209505879),(-1257361876383912351980057906)⟩,⟨(-87588728049222834397572968),(-87588728049222828831575450)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-2051787071176218418116839692),(-2051787071176218411674134064)⟩,⟨446058113924397624889120300,446058113924397631839302631⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-2444587155791724427508257109),(-2444587155791724419272430884)⟩,⟨1164593723531015831029579919,1164593723531015839734716330⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-2234765059500315894446500787),(-2234765059500315880481953111)⟩,⟨1796781851045265970251458597,1796781851045265984396646814⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-1572773968114536807488355750),(-1572773968114536767402162035)⟩,⟨2089233046417633616072965726,2089233046417633656155001990⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-795941513778915732193087268),(-795941513778915571133278982)⟩,⟨1972726962106253339269020772,1972726962106253500255376482⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-182521019375212017420552251),(-182521019375211495871520023)⟩,⟨1575095501941839349023493353,1575095501941839870495980811⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨165429868680278483105384965,165429868680279919863314144⟩,⟨1095306531129228460268190220,1095306531129229896980075036⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨285357906315753046463419448,285357906315756265109131374⟩,⟨679152631599213100232988878,679152631599216318866732670⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨263688893418086228753454768,263688893418090839362713301⟩,⟨379846069732316760614146434,379846069732321371222880450⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨174197692242091457864147492,174197692242095613664745533⟩,⟨184688921830304503745613764,184688921830308659547690806⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨59878831175708937544461978,59878831175710599895327485⟩,⟨54411795446081656959509774,54411795446083319311096092⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-1403779395047116952141350967),(-1403779395047055461788425864)⟩,⟨1739325854574024317489353925,1739325854574085808020993779⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨4738944808926609579855782876,4738944808926609584030349446⟩,⟨9065007400112829898284524614,9065007400112829902616551541⟩⟩
end tm1_7_0

namespace tm1_7_1
noncomputable def s0_0 : CBox := ⟨⟨(-1602514),(-1602494)⟩,⟨(-1647866),(-1647849)⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-2132978),(-2132957)⟩,⟨(-4360381),(-4360362)⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨749916,749940⟩,⟨(-3990792),(-3990770)⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨1923224,1923251⟩,⟨(-838507),(-838479)⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨481531,481562⟩,⟨604764,604792⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-188253),(-188227)⟩,⟨130448,130479⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-14066),(-14036)⟩,⟨(-60465),(-60434)⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨15842,15873⟩,⟨7288,7317⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-5477),(-5449)⟩,⟨1417,1447⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨1501,1531⟩,⟨(-1664),(-1635)⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-175),(-144)⟩,⟨1090,1117⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-419),(-393)⟩,⟨(-552),(-528)⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨446,466⟩,⟨(-102),(-76)⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨47,69⟩,⟨312,336⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-169),(-151)⟩,⟨115,135⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-78),(-62)⟩,⟨(-1),18⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨24709644233849,24709644233866⟩,⟨271139596376791,271139596376807⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨32401996370761,32401996370783⟩,⟨576759216641390,576759216641409⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-9704366244513),(-9704366244491)⟩,⟨485187264361867,485187264361888⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-37432996844826),(-37432996844801)⟩,⟨245754481166528,245754481166551⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-30740186032015),(-30740186031992)⟩,⟨81833455505200,81833455505225⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-14194221447510),(-14194221447484)⟩,⟨17738452599240,17738452599261⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-4202720832921),(-4202720832894)⟩,⟨1983618496366,1983618496394⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-785611896560),(-785611896534)⟩,⟨(-138916587530),(-138916587504)⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-71442727289),(-71442727261)⟩,⟨(-101030382596),(-101030382566)⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨5777742676,5777742707⟩,⟨(-17946074298),(-17946074269)⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨2993508566,2993508595⟩,⟨(-686734967),(-686734936)⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨378760600,378760630⟩,⟨432541559,432541588⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-40147621),(-40147594)⟩,⟨123223221,123223244⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-33192548),(-33192523)⟩,⟨12648916,12648938⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-10661974),(-10661952)⟩,⟨(-3190072),(-3190052)⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-2148632),(-2148613)⟩,⟨(-1589883),(-1589865)⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-432575597595732175382),(-432575597595732173639)⟩,⟨113562548020812854168,113562548020812855915⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-1023126030408995784269),(-1023126030408995779926)⟩,⟨338851225465843995473,338851225465843999821⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-1047191311535638334697),(-1047191311535638329697)⟩,⟨491153994405633996267,491153994405634001273⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-687520731225250232743),(-687520731225250228782)⟩,⟨472467140513690119970,472467140513690123940⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-308127085091913725341),(-308127085091913722989)⟩,⟨317969733050053673235,317969733050053675594⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-93729538930473378914),(-93729538930473377824)⟩,⟨155359053745476809524,155359053745476810618⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-17823227334956735634),(-17823227334956735213)⟩,⟨57448166136063084265,57448166136063084688⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-1127782841366761497),(-1127782841366761342)⟩,⟨16938696153060102659,16938696153060102816⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨558345654252371117,558345654252371188⟩,⟨4255889023034377679,4255889023034377753⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨265612333385412048,265612333385412103⟩,⟨984600495783953225,984600495783953283⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨74948512666091279,74948512666091335⟩,⟨226166425542426879,226166425542426938⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨17317339690979042,17317339690979101⟩,⟨54638479729960979,54638479729961038⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨3663881488187095,3663881488187144⟩,⟨14415685182263105,14415685182263152⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨760647903433719,760647903433755⟩,⟨4246130757727834,4246130757727872⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨160005525601341,160005525601371⟩,⟨1355555910965700,1355555910965725⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨27536810410424,27536810410444⟩,⟨325379261304319,325379261304337⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨1905393724221466650759355,1905393724221479203255523⟩,⟨1818549586367480714283230,1818549586367493266884238⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨5292538258737474582229423,5292538258737501658180148⟩,⟨4288224622097484612606554,4288224622097511688798439⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨7332185067066551592290146,7332185067066574007529709⟩,⟨4193279955437849149414176,4193279955437871564870812⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨7339457301168044699298726,7339457301168054843012485⟩,⟨2110572685325296229241664,2110572685325306373033266⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨5563411058101093735812067,5563411058101096326182302⟩,⟨(-172022844464554430422946),(-172022844464551840112455)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨3167755357602504709819073,3167755357602505080822243⟩,⟨(-1331861129607617478721123),(-1331861129607617107835369)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨1291686555825169682175054,1291686555825169717392317⟩,⟨(-1326840420400163148157277),(-1326840420400163113027245)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨312100260889743427261082,312100260889743432826719⟩,⟨(-832165558389757988178036),(-832165558389757982634994)⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-19580846778023185497634),(-19580846778023183743888)⟩,⟨(-387540452305225536335160),(-387540452305225534580991)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-67873806162744119565219),(-67873806162744118803554)⟩,⟨(-143185448548137243676879),(-143185448548137242911297)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-45122352678281521892717),(-45122352678281521551650)⟩,⟨(-43416843103228281660694),(-43416843103228281317066)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-22352495549108260474548),(-22352495549108260318653)⟩,⟨(-10740448076588299493005),(-10740448076588299336263)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-9939086339413250899088),(-9939086339413250827043)⟩,⟨(-1867324629338041186217),(-1867324629338041113972)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-4269922547626013613343),(-4269922547626013580204)⟩,⟨54634333625571934133,54634333625571967310⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-1748318664024457197023),(-1748318664024457182581)⟩,⟨254875911286252101952,254875911286252116396⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-474935185939888261584),(-474935185939888257512)⟩,⟨101391986346689378961,101391986346689383032⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨164687874671331298455838944,164687874671340265077796469⟩,⟨(-298224743354907607320817433),(-298224743354898640693727025)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨385028572019983294382006101,385028572020014226204454005⟩,⟨(-866800257391232039383844636),(-866800257391201107537231001)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨337009854595972549164414708,337009854596036783625229549⟩,⟨(-1312452283357704264601050032),(-1312452283357640030079712590)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨18138302989579003927756040,18138302989688316103541020⟩,⟨(-1492399894402995168658318335),(-1492399894402885856377344520)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-401987228194544236526431938),(-401987228194371800422644473)⟩,⟨(-1321141117305907697330000540),(-1321141117305735261109804438)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-692136134446188653012072603),(-692136134445898839306505238)⟩,⟨(-878676282459429543394299851),(-878676282459139729625951189)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-726989733954481224305574407),(-726989733954135896257138464)⟩,⟨(-378637533547988311701325389),(-378637533547642983641842490)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-557143206281880861538746979),(-557143206281612558377819212)⟩,⟨(-16182716323688012715593616),(-16182716323419709574815605)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-325722681608606647593638427),(-325722681608469662596256872)⟩,⟨146224260506016991871778126,146224260506153976843400877⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-143558752694538969878458261),(-143558752694465898489120450)⟩,⟨163032929469633730547421182,163032929469706801925915860⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-41651762607252401410178175),(-41651762607222426022925733)⟩,⟨119236704012937768764333880,119236704012967744149915892⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-12769107255857708200430),(-12769107246700861868765)⟩,⟨70642794722308655775598295,70642794722317812623188363⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨10673182869266812607373826,10673182869269199711847110⟩,⟨36765449934381583890297873,36765449934383970996381034⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨9765434250260500760670404,9765434250261104700208346⟩,⟨17514029715935301584945810,17514029715935905525633639⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨5952829108652596672772999,5952829108652788945664970⟩,⟨7521326207099447727555531,7521326207099640000967956⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨1941921579190953682397700,1941921579191000955627355⟩,⟨2068696663082741540345741,2068696663082788813713461⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-140221209035459723370724822),(-140221209035459721082737722)⟩,⟨(-183573583916150822195914669),(-183573583916150819739842370)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-525884728592999543399139846),(-525884728592999536464825060)⟩,⟨(-364594525824317095958752235),(-364594525824317088694085844)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-982732299410880063401389036),(-982732299410880052009586093)⟩,⟨132368602256209001618975285,132368602256209013053308067⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-1013304072310068741717343431),(-1013304072310068726267492990)⟩,⟨1832174939836449088121917648,1832174939836449102896863006⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨15638326521013533078907283,15638326521013553870206322⟩,⟨4667220987048662927488067902,4667220987048662946769397145⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨2291332180858142781584706652,2291332180858142807875298306⟩,⟨7515761747501254578607405877,7515761747501254602780873920⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨5241605375306816149481567707,5241605375306816184779138957⟩,⟨8811800628666014521642667775,8811800628666014555363020484⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨7735495537730886689180626760,7735495537730886746427185171⟩,⟨7815550382740434397943242043,7815550382740434454714018147⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨8763622145490165989733614605,8763622145490166146892696867⟩,⟨5143476495293544996707038129,5143476495293545154045990312⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨8099740764654855447927616106,8099740764654856052966078571⟩,⟨2132704581227067731860915114,2132704581227068337287474795⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨6321411207941505284663813415,6321411207941507252364023962⟩,⟨(-137178116830869704943551005),(-137178116830867736906208601)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨4273083484638236123236168981,4273083484638242513461625546⟩,⟨(-1308103459468954041301598746),(-1308103459468947650943703811)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨2553444137075440997140774449,2553444137075454875567289519⟩,⟨(-1578416986062619529380777398),(-1578416986062605650938818255)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨1364105815055077005782136996,1364105815055096425095739918⟩,⟨(-1321787247026981262750357195),(-1321787247026961843453613904)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨632153824221426041226475001,632153824221443256642702324⟩,⟨(-836774478835469320351693974),(-836774478835452104951274209)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨180163072274898054078917130,180163072274904879208401047⟩,⟨(-282630613822208742256863179),(-282630613822201917133235974)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨7147613136854623667973654536,7147613136854891743740636148⟩,⟨4340775680407569977352556569,4340775680407838052374919562⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨32212805902528216815616367009,32212805902528216832663432487⟩,⟨(-19040580849561774497104660124),(-19040580849561774480641562371)⟩⟩
end tm1_7_1

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
open IntegerIntervals

namespace tm1_72_0
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨384791,384807⟩,⟨(-797316),(-797300)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-189520),(-189504)⟩,⟨(-1119178),(-1119162)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-346635),(-346619)⟩,⟨(-62644),(-62628)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨2709,2725⟩,⟨41125,41141⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨1300,1318⟩,⟨(-1590),(-1573)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-45),(-29)⟩,⟨20,37⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-12),16⟩,⟨(-16),8⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-275452287821076010136),(-275452287768705750699)⟩,⟨(-49199231144035744513),(-49199231091665485627)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-373421969295796555370),(-373421969168297965181)⟩,⟨251371181378000370372,251371181505498959758⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨140901335427204492352,140901335546973536485⟩,⟨178706082909641087487,178706083029410131998⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨3447938543998567834,3447938618554588476⟩,⟨(-95330993414324478596),(-95330993339768458032)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-21779518280518379596),(-21779518230262479554)⟩,⟨22459668161777484661,22459668212033384717⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨5107075656836951790,5107075672973316068⟩,⟨(-894068662746158963),(-894068646609794686)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-453082422915899349),(-453082420306900380)⟩,⟨(-88877855950273397),(-88877853341274431)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨23876561512969199,23876561746394097⟩,⟨7566788931636699,7566789165061598⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-918263580443022),(-918263567747065)⟩,⟨(-227929267056384),(-227929254360429)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨28555736236156,28555736708493⟩,⟨3292499122249,3292499594586⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-822161915430),(-822161901099)⟩,⟨(-40557254849),(-40557240516)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨26025185345,26025185803⟩,⟨4768190662,4768191121⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-911358513),(-911358478)⟩,⟨(-695069276),(-695069241)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-3130536),(-3130519)⟩,⟨78435038,78435055⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨9065135,9065152⟩,⟨564350,564366⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨957465,957481⟩,⟨(-876250),(-876234)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-86937920355939902545),(-86937920282032937837)⟩,⟨51171850581353006418,51171850655259970951⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨18075369051480715984443,18075369051480716666024⟩,⟨(-45544292906122318243591),(-45544292906122317561971)⟩⟩
end tm1_72_0

namespace tm1_72_1
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-3531079),(-3531063)⟩,⟨(-1008906),(-1008890)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-4446081),(-4446064)⟩,⟨1580371,1580388⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-495),(-477)⟩,⟨1470586,1470604⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨167816,167833⟩,⟨(-43041),(-43024)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-7661),(-7642)⟩,⟨(-4173),(-4152)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨142,160⟩,⟨123,142⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-16),10⟩,⟨(-16),13⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-125465159657437535440),(-125465159458282127082)⟩,⟨1004514139141412094008,1004514139340567504514⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨983744339933315427327,983744340420161429737⟩,⟨1301688822804404790216,1301688823291250795267⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨618686100462456329741,618686100923415798019⟩,⟨(-550103526678354879977),(-550103526217395413141)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-349024306833353377099),(-349024306542833416927)⟩,⟨10248652323998072053,10248652614518032524⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨88488181101172748454,88488181299916976479⟩,⟨74129114211879357111,74129114410623585100⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-4861928295453375909),(-4861928230533227030)⟩,⟨(-18691757695776242706),(-18691757630856093828)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-178620804401284210),(-178620793698218317)⟩,⟨1729973945374681458,1729973956077747350⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨19488067084952029,19488068063013528⟩,⟨(-93511416789501859),(-93511415811440360)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-476115493040608),(-476115438656093)⟩,⟨3624977961522179,3624978015906696⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-1059939103374),(-1059937034690)⟩,⟨(-112579649678488),(-112579647609804)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨281221320953,281221385028⟩,⟨3254811048086,3254811112160⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨3742422131,3742424165⟩,⟨(-106253875336),(-106253873304)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-2217828683),(-2217828591)⟩,⟨4095133102,4095133196⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨319478668,319478691⟩,⟨(-39383116),(-39383094)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-3944200),(-3944182)⟩,⟨(-37284812),(-37284794)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-4248627),(-4248611)⟩,⟨(-3294484),(-3294468)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨201901269513500187100,201901269798980664677⟩,⟨303904237031172425199,303904237316652903379⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-167855700265763829092977),(-167855700265763826503097)⟩,⟨(-56718623667473242612921),(-56718623667473240023474)⟩⟩
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
open IntegerIntervals

namespace tm1_73_0
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨207751,207767⟩,⟨383805,383822⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨498036,498052⟩,⟨240762,240778⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨118365,118381⟩,⟨(-119061),(-119045)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-16561),(-16544)⟩,⟨(-9386),(-9370)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨286,302⟩,⟨851,867⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-11),5⟩,⟨(-26),(-10)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-16),16⟩,⟨(-12),16⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨221468821005882200832,221468821064151328967⟩,⟨(-67184272144036059746),(-67184272085766932065)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨177257291561228061697,177257291702369559091⟩,⟨(-323914467544957193737),(-323914467403815696344)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-168102785573357358194),(-168102785442106340264)⟩,⟨(-73711521923195970447),(-73711521791944952220)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨34312042065320477249,34312042145671947376⟩,⟨66769626355968407872,66769626436319877937⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨5496164246243490599,5496164299265458865⟩,⟨(-23292015997059743271),(-23292015944037775002)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-2819398279515117364),(-2819398262938857894)⟩,⟨2597519596278900755,2597519612855160226⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨300176605700997214,300176608294726814⟩,⟨(-132554504333206725),(-132554501739477122)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-16018886021638089),(-16018885798385438)⟩,⟨5765772428156211,5765772651408858⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨550425637230953,550425648851500⟩,⟨(-269160228781462),(-269160217160914)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-14298246018157),(-14298245606068)⟩,⟨10426356116985,10426356529074⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨355209467353,355209479243⟩,⟨(-325289254358),(-325289242465)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-11715395166),(-11715394802)⟩,⟨8957334364,8957334730⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨596720422,596720452⟩,⟨(-134170359),(-134170333)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-30771800),(-30771781)⟩,⟨(-26217310),(-26217294)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-2954860),(-2954844)⟩,⟨3476520,3476536⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨71449,71465⟩,⟨639776,639792⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨44649471536155045134,44649471616728440307⟩,⟨(-69810363239877844863),(-69810363159304449728)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨3715781017305418282288,3715781017305418816118⟩,⟨40440990295055608201062,40440990295055608735432⟩⟩
end tm1_73_0

namespace tm1_73_1
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨1421834,1421850⟩,⟨(-1120669),(-1120653)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨627799,627816⟩,⟨(-2212214),(-2212198)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-576859),(-576841)⟩,⟨(-398143),(-398126)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-25951),(-25931)⟩,⟨75617,75633⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨3329,3350⟩,⟨(-1930),(-1912)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-88),(-72)⟩,⟨19,37⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-13),16⟩,⟨(-16),15⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-284766976455078794336),(-284766976233491069316)⟩,⟨(-787386277294358778288),(-787386277072771051775)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-1207420981648030600147),(-1207420981109092198256)⟩,⟨(-577353196491344400913),(-577353195952405999308)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-231546006819215362519),(-231546006314070515300)⟩,⟨626300705680800520989,626300706185945367191⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨235646935066985675047,235646935380081249111⟩,⟨(-141315721215754318649),(-141315720902658744376)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-87182215902404774096),(-87182215692728921506)⟩,⟨(-13984742146881047911),(-13984741937205195319)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨10494699392586901913,10494699459273844575⟩,⟨9683375308259330709,9683375374946273367⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-599699147369876890),(-599699136730011256)⟩,⟨(-1080721816709339835),(-1080721806069474195)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨28057405636029816,28057406571416281⟩,⟨58549051450480107,58549052385866573⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-1272565342641401),(-1272565292866352)⟩,⟨(-1996524190675250),(-1996524140900200)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨47455637823563,47455639628275⟩,⟨50511646323813,50511648128526⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-1469461794440),(-1469461741280)⟩,⟨(-1222482961326),(-1222482908167)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨42456680398,42456682007⟩,⟨41339654589,41339656199⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-913343676),(-913343602)⟩,⟨(-2311132541),(-2311132466)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-85671343),(-85671321)⟩,⟨141917733,141917754⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨16184080,16184097⟩,⟨9633005,9633022⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨2561796,2561812⟩,⟨(-740340),(-740323)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-260891235774096592227),(-260891235462970553444)⟩,⟨(-147513329353398198770),(-147513329042272159920)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨145335744318200505957132,145335744318200507987476⟩,⟨(-21011522394352803508046),(-21011522394352801479952)⟩⟩
end tm1_73_1

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
open IntegerIntervals

namespace tm1_75_0
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨72590,72606⟩,⟨(-77333),(-77317)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨15162,15178⟩,⟨(-130521),(-130505)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-34844),(-34828)⟩,⟨(-15546),(-15530)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-445),(-429)⟩,⟨4022,4038⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨116,132⟩,⟨(-135),(-119)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-10),8⟩,⟨(-4),16⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨51859301957461828460,51859302029596965088⟩,⟨(-149593210042641468751),(-149593209970506331899)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-109049032060953698597),(-109049031887987903453)⟩,⟨(-223236103562992602547),(-223236103390026806892)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-100777584702707817261),(-100777584545078094726)⟩,⟨64072116784509990434,64072116942139712792⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨46366610358629740774,46366610451967718224⟩,⟨3477944994298553533,3477945087636531018⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-10470646776736284476),(-10470646717708003345)⟩,⟨(-9304746509411507063),(-9304746450383225939)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨650407845203474608,650407862699639328⟩,⟨1993414271563948968,1993414289060113690⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-10543157770727390),(-10543155206559896)⟩,⟨(-165511528691034924),(-165511526126867431)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨621855933728084,621856138012713⟩,⟨7846850045620344,7846850249904971⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-71034426294006),(-71034416555275)⟩,⟨(-247137131672093),(-247137121933363)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨3500007016879,3500007330663⟩,⟨5726205499307,5726205813089⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-112690324389),(-112690316195)⟩,⟨(-120526020645),(-120526012452)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨3123005499,3123005734⟩,⟨3355382254,3355382488⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-67117404),(-67117382)⟩,⟨(-160770118),(-160770094)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-4824310),(-4824293)⟩,⟨9576996,9577013⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨1052101,1052117⟩,⟨467761,467778⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨144460,144476⟩,⟨(-64908),(-64892)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-20238488720832840933),(-20238488624937575393)⟩,⟨(-52124748378594387027),(-52124748282699121390)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨23922674892674597297496,23922674892674597903093⟩,⟨14349888490558340686039,14349888490558341291736⟩⟩
end tm1_75_0

namespace tm1_75_1
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-367418),(-367402)⟩,⟨(-242052),(-242036)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-545264),(-545247)⟩,⟨31681,31699⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-38037),(-38021)⟩,⟨154631,154649⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨16975,16991⟩,⟨(-1322),(-1306)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-639),(-622)⟩,⟨(-423),(-403)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨1,22⟩,⟨(-2),19⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-550304448567111710726),(-550304448292794134388)⟩,⟨(-158965424209658183250),(-158965423935340607840)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-786315644054965327564),(-786315643394513717544)⟩,⟨438887558915341164609,438887559575792772856⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨254321913956659267802,254321914563313951027⟩,⟨352183475368382616432,352183475975037300343⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨1598284168710771049,1598284532392266851⟩,⟨(-170166220963441523187),(-170166220599760027523)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-31433001336182193077),(-31433001102770273662)⟩,⟨41016676498165617898,41016676731577537327⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨7203976554799036334,7203976625180506943⟩,⟨(-3015524813679587618),(-3015524743298117006)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-617192068258472158),(-617192057740968551)⟩,⟨95979737890386539,95979748407890145⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨29528501260622359,29528502116441182⟩,⟨(-5383951296081223),(-5383950440262403)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-918040530494967),(-918040488785099)⟩,⟨379962621747156,379962663457027⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨20557053495959,20557054869987⟩,⟨(-16376332839077),(-16376331465052)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-413577657025),(-413577620420)⟩,⟨507637981110,507638017717⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨11514388973,11514389982⟩,⟨(-14374629438),(-14374628429)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-603200539),(-603200489)⟩,⟨370340994,370341046⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨41953238,41953255⟩,⟨13167106,13167126⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨1179505,1179521⟩,⟨(-4604129),(-4604113)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-366258),(-366240)⟩,⟨(-544289),(-544273)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-184252913455198273779),(-184252913085145740121)⟩,⟨83338583443605828492,83338583813658361794⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨47325780089108675115646,47325780089108677416738⟩,⟨(-89079928642132867794992),(-89079928642132865494135)⟩⟩
end tm1_75_1

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
open IntegerIntervals

namespace tm1_76_0
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨9965,9981⟩,⟨51321,51337⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨47543,47560⟩,⟨42883,42899⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨15520,15536⟩,⟨(-9469),(-9453)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-1452),(-1436)⟩,⟨(-1200),(-1183)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨11,28⟩,⟨68,84⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-14),7⟩,⟨(-16),8⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨17958657312084799913,17958657392345215130⟩,⟨129716788202779379885,129716788283039795415⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨163600647794544671700,163600647986021576207⟩,⟨121522710610208460066,121522710801685364684⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨47430430503596866536,47430430676345821526⟩,⟨(-83842240014956729757),(-83842239842207774937)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-33179963256297407440),(-33179963155694203996)⟩,⟨15439054846291371629,15439054946894575104⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨10527881156877695428,10527881219164423541⟩,⟨2011464907173749084,2011464969460477197⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-1201417607944538409),(-1201417589967506031)⟩,⟨(-981171931250666445),(-981171913273634066)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨73486504064682031,73486506614543925⟩,⟨92250641316998450,92250643866860345⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-3574836280888844),(-3574836085443936)⟩,⟨(-3985918900829326),(-3985918705384414)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨138178335065058,138178343981995⟩,⟨93148067009362,93148075926300⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-3975987094804),(-3975986820944)⟩,⟨(-1133127866324),(-1133127592465)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨96565350506,96565357307⟩,⟨2759674259,2759681061⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-2556021109),(-2556020922)⟩,⟨31593837,31594025⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨88762777,88762801⟩,⟨27743357,27743380⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-2343364),(-2343347)⟩,⟨(-5001705),(-5001688)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-504820),(-504804)⟩,⟨282384,282401⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-16207),(-16191)⟩,⟨76859,76875⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨34201046977848191555,34201047082532815856⟩,⟨30659160560069221334,30659160664753845685⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-23062633143016560205848),(-23062633143016559856446)⟩,⟨(-1637234213454486510820),(-1637234213454486161629)⟩⟩
end tm1_76_0

namespace tm1_76_1
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨202735,202752⟩,⟨(-77077),(-77061)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨141411,141429⟩,⟨(-225521),(-225503)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-50383),(-50366)⟩,⟨(-56799),(-56780)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-3811),(-3791)⟩,⟨6873,6893⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨295,312⟩,⟨(-153),(-132)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-19),7⟩,⟨(-8),15⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨465240501684135677500,465240501989352154985⟩,⟨(-89504769418375426511),(-89504769113158950097)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨407392111089591298033,407392111820722562412⟩,⟨(-616161709697781420759),(-616161708966650156622)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-314640838696906614889),(-314640838032071453990)⟩,⟨(-154214082553995223062),(-154214081889160061574)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨64325742334908577833,64325742726889112721⟩,⟨117473519299901793994,117473519691882328779⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨4583447089925394810,4583447336213609538⟩,⟨(-39272670669411678831),(-39272670423123464105)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-3280154386850379757),(-3280154314537736809)⟩,⟨4755427071002489177,4755427143315132128⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨320950613435786870,320950623894075409⟩,⟨(-307051187523908959),(-307051177065620418)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-13743481538104514),(-13743480719363181)⟩,⟨15096833069340443,15096833888081775⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨297701352661217,297701390849339⟩,⟨(-570904883751632),(-570904845563512)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-2477685394948),(-2477684195815)⟩,⟨15999803042938,15999804242072⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-40833658318),(-40833627932)⟩,⟨(-381167690683),(-381167660297)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨1618128030,1618128832⟩,⟨10142114875,10142115676⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨55645261,55645303⟩,⟨(-373700384),(-373700340)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-18683893),(-18683873)⟩,⟨12800136,12800154⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨1496839,1496856⟩,⟨1860137,1860154⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨325156,325172⟩,⟨12225,12241⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨103988051905198740710,103988052309045531752⟩,⟨(-129536132599929950130),(-129536132196083159226)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-1581547398573032133346),(-1581547398573030806753)⟩,⟨83587197757875196197000,83587197757875197524547⟩⟩
end tm1_76_1

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
open IntegerIntervals

namespace tm1_79_0
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-711),(-695)⟩,⟨6217,6233⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨3887,3903⟩,⟨6300,6318⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨1872,1889⟩,⟨(-601),(-585)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-127),(-111)⟩,⟨(-151),(-135)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-3),13⟩,⟨(-3),14⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),13⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-74084339875234999256),(-74084339764683016905)⟩,⟨(-1438765164727521009),(-1438765054175538831)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-78888616913057545784),(-78888616653281828429)⟩,⟨80181731960530273672,80181732220305990908⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨41237695545851290658,41237695773248799599⟩,⟨29260435397046483399,29260435624443992429⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-6867496887690326211),(-6867496761694405051)⟩,⟨(-16474718131128733301),(-16474718005132812151)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-706292104901232585),(-706292031697393257)⟩,⟨4752900845468089835,4752900918671929162⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨325860574534985278,325860594043729455⟩,⟨(-537565029468103617),(-537565009959359438)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-25455839478210126),(-25455836969437264)⟩,⟨34000276614734894,34000279123507758⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨741831562509160,741831733771266⟩,⟨(-1515508451524986),(-1515508280262884)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-3230878848768),(-3230871999399)⟩,⟨45301692251660,45301699101028⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-363125427263),(-363125245072)⟩,⟨(-897093972485),(-897093790294)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨13530552925,13530556826⟩,⟨13917756286,13917760186⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-358802630),(-358802530)⟩,⟨(-261083003),(-261082903)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨9573136,9573157⟩,⟨10426593,10426612⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-7830),(-7814)⟩,⟨(-755011),(-754995)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-72487),(-72470)⟩,⟨11196,11212⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-4827),(-4811)⟩,⟨8278,8294⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-19834651208206093817),(-19834651071685962748)⟩,⟨15962758177358058825,15962758313878189858⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨3044008949786747664684,3044008949786748088936⟩,⟨(-12806156258019557611479),(-12806156258019557187163)⟩⟩
end tm1_79_0

namespace tm1_79_1
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨25933,25949⟩,⟨(-1541),(-1524)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨23022,23040⟩,⟨(-20483),(-20467)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-3835),(-3818)⟩,⟨(-7293),(-7276)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-496),(-480)⟩,⟨592,608⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨16,34⟩,⟨(-20),(-2)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-16),14⟩,⟨(-16),16⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨8864489600195979260,8864490020605454623⟩,⟨267929276490928496975,267929276911337972986⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨305807432951312983497,305807433943222513089⟩,⟨269615551421101971281,269615552413011501225⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨97386096253577037351,97386097128701069360⟩,⟨(-156018440776716042030),(-156018439901592010345)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-58513380129387965255),(-58513379638503988486)⟩,⟨29017829096869923280,29017829587753900103⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨17673124840297579839,17673125129723801466⟩,⟨1327980012712138484,1327980302138360113⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-2093228275651269311),(-2093228197187632357)⟩,⟨(-1047744992506912891),(-1047744914043275938)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨136163747375994003,136163757664194367⟩,⟨83899030878022394,83899041166222757⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-6033915112425886),(-6033914395104632)⟩,⟨(-2231103916287093),(-2231103198965841)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨175314039805295,175314069134011⟩,⟨(-7211558983451),(-7211529654736)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-3310302675253),(-3310301877645)⟩,⟨1844958306591,1844959104205⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨47486175309,47486192695⟩,⟨(-60638766907),(-60638749517)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-828423592),(-828423187)⟩,⟨1578506375,1578506781⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨35842576,35842605⟩,⟨(-44963689),(-44963660)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-3049618),(-3049602)⟩,⟨532391,532409⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨95481,95500⟩,⟨287259,287275⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨37201,37217⟩,⟨13852,13868⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨61542472853839294054,61542473380048050827⟩,⟨68484352292274368810,68484352818483125706⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-46814947472334486902345),(-46814947472334485290305)⟩,⟨(-8587340666924063581221),(-8587340666924061969505)⟩⟩
end tm1_79_1

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
open IntegerIntervals

namespace tm1_81_0
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨1484,1500⟩,⟨(-326),(-310)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨1104,1120⟩,⟨(-1374),(-1358)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-286),(-270)⟩,⟨(-359),(-342)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-25),(-9)⟩,⟨29,45⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-9),15⟩,⟨(-16),5⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-30584456252661912721),(-30584456115801492964)⟩,⟨40425364233897329048,40425364370757748821⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨13366927141838485610,13366927460207911229⟩,⟨74497425573507839234,74497425891877265007⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨30780176393477765674,30780176666625587324⟩,⟨(-11638792478019647415),(-11638792204871825800)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-10927307863195604912),(-10927307716779185107)⟩,⟨(-1723781160563603665),(-1723781014147183853)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨2251277442325709786,2251277523871637056⟩,⟨1692031155313509508,1692031236859436779⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-193030408215424316),(-193030387606434387)⟩,⟨(-285409909367432628),(-285409888758442704)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨11689759726429434,11689762209273895⟩,⟨18070907263615446,18070909746459908⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-586590251402874),(-586590094496623)⟩,⟨(-517570728316138),(-517570571409885)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨18531396589539,18531402337495⟩,⟨4677549876475,4677555624432⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-351321820255),(-351321681332)⟩,⟨109496840064,109496978987⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨4736193741,4736196435⟩,⟨(-4690069507),(-4690066812)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-70285998),(-70285927)⟩,⟨118989985,118990053⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨2459595,2459614⟩,⟨(-3201806),(-3201788)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-194278),(-194261)⟩,⟨49256,49272⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨7860,7876⟩,⟨16745,16761⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨2295,2311⟩,⟨495,511⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨784117967964499872,784118131230274367⟩,⟨17164065922295965306,17164066085561739824⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-5862838644329701088367),(-5862838644329700964236)⟩,⟨(-6883431223679655274952),(-6883431223679655150714)⟩⟩
end tm1_81_0

namespace tm1_81_1
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-2348),(-2331)⟩,⟨(-5875),(-5857)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-6397),(-6381)⟩,⟨(-3583),(-3566)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-1250),(-1232)⟩,⟨1389,1410⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨148,167⟩,⟨36,55⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-16),5⟩,⟨(-17),8⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨151856347819468580928,151856348339923866007⟩,⟨102823644781725157982,102823645302180442971⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨266956077732574974107,266956078948204487863⟩,⟨(-63132193604668328162),(-63132192389038814978)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-48868384288193668877),(-48868383237026192422)⟩,⟨(-109258025636805249723),(-109258024585637773136)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-3680731784421275898),(-3680731214004887369)⟩,⟨40309273817590495759,40309274388006884260⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨5622701152307595078,5622701474694286503⟩,⟨(-8732713267849962523),(-8732712945463271094)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-1001228237672261080),(-1001228154790632424)⟩,⟨802133665803820035,802133748685448689⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨63793160802180427,63793170983042342⟩,⟨(-49973768286881516),(-49973758106019603)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-1737835057865428),(-1737834400741534)⟩,⟨2423756672401666,2423757329525565⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨9940893892621,9940918502565⟩,⟨(-73163358276377),(-73163333666435)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨595255232300,595255840416⟩,⟨1312204953856,1312205561978⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-20969435741),(-20969423746)⟩,⟨(-16114755490),(-16114743496)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨513927764,513928022⟩,⟨209977543,209977801⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-14392504),(-14392483)⟩,⟨(-7863516),(-7863491)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨328136,328153⟩,⟨753317,753336⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨62767,62785⟩,⟨(-43562),(-43546)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨437,453⟩,⟨(-9767),(-9751)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨61824474705914643993,61824475334881344429⟩,⟨(-6205917020480636623),(-6205916391513936278)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-23755364507429611727611),(-23755364507429611255578)⟩,⟨22463387972788812326589,22463387972788812798240⟩⟩
end tm1_81_1

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
open IntegerIntervals

namespace tm1_84_0
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨175,191⟩,⟨10,26⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨159,175⟩,⟨(-123),(-107)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-28),(-11)⟩,⟨(-52),(-36)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-8),8⟩,⟨(-1),16⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-13),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-19886218308413472405),(-19886218119898115356)⟩,⟨(-20669966047147154795),(-20669965858631797737)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-41744996013230278399),(-41744995581266245769)⟩,⟨1618914367984666780,1618914799948699335⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨4410099881768672600,4410100241404890786⟩,⟨16708250689839078965,16708251049475297161⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨1069243546890965349,1069243730352347737⟩,⟨(-5293456455783529707),(-5293456272322147324)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-720320693248725610),(-720320597337850582)⟩,⟨1039649598511330233,1039649694422205262⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨104134953063980800,104134975452433287⟩,⟨(-93592070139448883),(-93592047750996391)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-5260270097980647),(-5260267651944002)⟩,⟨5726276901273385,5726279347310029⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨82454262835938,82454400534985⟩,⟨(-233212102600277),(-233211964901229)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨1411970275379,1411974697753⟩,⟨5031714474150,5031718896524⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-70952221527),(-70952128947)⟩,⟨(-49324543794),(-49324451215)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨1343099712,1343101261⟩,⟨(-11254284),(-11252734)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-22202146),(-22202105)⟩,⟨9241702,9241744⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨569567,569584⟩,⟨(-233548),(-233532)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-26982),(-26966)⟩,⟨(-4934),(-4917)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨184,200⟩,⟨2332,2348⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨239,255⟩,⟨139,155⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-9462205517777418146),(-9462205303699989381)⟩,⟨(-1114116978258117322),(-1114116764180688565)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨4407218032765321678117,4407218032765321753669⟩,⟨(-2659837205652775122351),(-2659837205652775046881)⟩⟩
end tm1_84_0

namespace tm1_84_1
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-66),(-48)⟩,⟨(-762),(-745)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-602),(-585)⟩,⟨(-614),(-596)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-175),(-158)⟩,⟨106,123⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨5,24⟩,⟨(-3),14⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),13⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s5_0 : CBox := ⟨⟨(-70902584616972914283),(-70902583900084304323)⟩,⟨75769339983824601220,75769340700713211173⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨14127870534313883628,14127872183660865485⟩,⟨150750015789150923977,150750017438497906123⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨59714201514983972513,59714202898942389424⟩,⟨(-19597877578972682072),(-19597876195014265210)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-19580198264066006101),(-19580197549377619466)⟩,⟨(-2638716837930510152),(-2638716123242123502)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨4015693819846168369,4015694198985844369⟩,⟨2371990888447773999,2371991267587450000⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-378530997009684601),(-378530906983235808)⟩,⟨(-358355667419915417),(-358355577393466624)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨23254549380334918,23254559408807089⟩,⟨17782276407610461,17782286436082634⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-916143534593251),(-916142957997269)⟩,⟨(-223302934595655),(-223302357999671)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨18705460128791,18705479060368⟩,⟨(-7593448898656),(-7593429967077)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-157403746761),(-157403341584)⟩,⟨299492419626,299492824803⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-761052927),(-761046046)⟩,⟨(-5274151636),(-5274144756)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨49665782,49665921⟩,⟨82855497,82855633⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-1294212),(-1294192)⟩,⟨(-2139395),(-2139377)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-2059),(-2042)⟩,⟨112385,112402⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨9382,9399⟩,⟨(-2400),(-2381)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨417,433⟩,⟨(-1124),(-1108)⟩⟩
noncomputable def ans : CBox := ⟨⟨(-2163531842619188744),(-2163531018507032963)⟩,⟨34385658041903899692,34385658866016055514⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-10432299519928471445614),(-10432299519928471158857)⟩,⟨(-15415132520922724436169),(-15415132520922724149113)⟩⟩
end tm1_84_1

end SharpPlanar.CachedData

end OAI
end


