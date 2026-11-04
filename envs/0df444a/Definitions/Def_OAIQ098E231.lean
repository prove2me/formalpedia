-- Prove2me | Definitions.Def_OAIQ098E231
-- name    : OAIQ098E231
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T05:23:24.299332+00:00
-- url     : https://prove2.me/theorems/b35b7676-ab76-47b5-a9a4-257015c0b2e0
-- title:
--   Definitions bundle OAIQ098E231 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4398 declarations of OpenAI's Lean: 4398 definitions. The definitions and types are `OAI.SharpPlanar.CachedData.tm0_69_0.s1_1`, `OAI.SharpPlanar.CachedData.tm0_69_0.s1_10`, `OAI.SharpPlanar.CachedData.tm0_69_0.s1_11`, `OAI.SharpPlanar.CachedData.tm0_69_0.s1_12`, `OAI.SharpPlanar.CachedData.tm0_69_0.s1_13`, `OAI.SharpPlanar.CachedData.tm0_69_0.s1_14`, `OAI.SharpPlanar.CachedData.tm0_69_0.s1_15`, `OAI.SharpPlanar.CachedData.tm0_69_0.s1_2`, `OAI.SharpPlanar.CachedData.tm0_69_0.s1_3`, `OAI.SharpPlanar.CachedData.tm0_69_0.s1_4`, `OAI.SharpPlanar.CachedData.tm0_69_0.s1_5`, `OAI.SharpPlanar.CachedData.tm0_69_0.s1_6`, `OAI.SharpPlanar.CachedData.tm0_69_0.s1_7`, `OAI.SharpPlanar.CachedData.tm0_69_0.s1_8`, `OAI.SharpPlanar.CachedData.tm0_69_0.s1_9`, `OAI.SharpPlanar.CachedData.tm0_69_0.s2`, `OAI.SharpPlanar.CachedData.tm0_69_0.s2_0`, `OAI.SharpPlanar.CachedData.tm0_69_0.s2_1`, `OAI.SharpPlanar.CachedData.tm0_69_0.s2_10`, `OAI.SharpPlanar.CachedData.tm0_69_0.s2_11`, `OAI.SharpPlanar.CachedData.tm0_69_0.s2_12`, `OAI.SharpPlanar.CachedData.tm0_69_0.s2_13`, `OAI.SharpPlanar.CachedData.tm0_69_0.s2_14`, `OAI.SharpPlanar.CachedData.tm0_69_0.s2_15`, `OAI.SharpPlanar.CachedData.tm0_69_0.s2_2`, `OAI.SharpPlanar.CachedData.tm0_69_0.s2_3`, `OAI.SharpPlanar.CachedData.tm0_69_0.s2_4`, `OAI.SharpPlanar.CachedData.tm0_69_0.s2_5`, `OAI.SharpPlanar.CachedData.tm0_69_0.s2_6`, `OAI.SharpPlanar.CachedData.tm0_69_0.s2_7`, `OAI.SharpPlanar.CachedData.tm0_69_0.s2_8`, `OAI.SharpPlanar.CachedData.tm0_69_0.s2_9`, `OAI.SharpPlanar.CachedData.tm0_69_0.s3`, `OAI.SharpPlanar.CachedData.tm0_69_0.s3_0`, `OAI.SharpPlanar.CachedData.tm0_69_0.s3_1`, `OAI.SharpPlanar.CachedData.tm0_69_0.s3_10`, `OAI.SharpPlanar.CachedData.tm0_69_0.s3_11`, `OAI.SharpPlanar.CachedData.tm0_69_0.s3_12`, `OAI.SharpPlanar.CachedData.tm0_69_0.s3_13`, `OAI.SharpPlanar.CachedData.tm0_69_0.s3_14` and 4358 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_Certificate_TableMoments100`, `PlanarPacking_Certificate_TableMoments12`, `PlanarPacking_Certificate_TableMoments13`, `PlanarPacking_Certificate_TableMoments15`, `PlanarPacking_Certificate_TableMoments69`, `PlanarPacking_Certificate_TableMoments7`, `PlanarPacking_Certificate_TableMoments72`, `PlanarPacking_Certificate_TableMoments73`, `PlanarPacking_Certificate_TableMoments75`, `PlanarPacking_Certificate_TableMoments76`, `PlanarPacking_Certificate_TableMoments79`, `PlanarPacking_Certificate_TableMoments81`, `PlanarPacking_Certificate_TableMoments84`, `PlanarPacking_Certificate_TableMoments85`, `PlanarPacking_Certificate_TableMoments87`, `PlanarPacking_Certificate_TableMoments88`, `PlanarPacking_Certificate_TableMoments9`, `PlanarPacking_Certificate_TableMoments91`, `PlanarPacking_Certificate_TableMoments93`, `PlanarPacking_Certificate_TableMoments96`, `PlanarPacking_Certificate_TableMoments97`, `PlanarPacking_Certificate_TableMoments99`, `PlanarPacking_TaylorControl`.
--
--   **Imports.** It imports the bundle `OAIQ098E017` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098E240`; the statements `OAI.SharpPlanar.CachedData.tm0_69_1.KContains_e`, `OAI.SharpPlanar.CachedData.tm0_85_1.KContains_e` and `OAI.SharpPlanar.CachedData.tm0_93_1.KContains_e`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098E017

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
open IntegerIntervals IntegerBasis IntegerGrid

namespace tm1_100_0
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
noncomputable def s4_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-1237980616975413484),(-1237979576851227206)⟩,⟨600692256590729051,600693296714915325⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-317399098476123208),(-317396897856192097)⟩,⟨1727617888105895938,1727620088725827052⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨546262530031957344,546264093070805026⟩,⟨(-121297202390759513),(-121295639351911831)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-119012753548686522),(-119012139679212757)⟩,⟨8792083597858250,8792697467332012⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨17986125669496756,17986355236750319⟩,⟨(-1815596620918358),(-1815367053664796)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-1088630725589818),(-1088595549784805)⟩,⟨460815590745950,460850766550966⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨15251650544217,15253937346639⟩,⟨(-31666640797270),(-31664353994851)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨331845680701,331915268114⟩,⟨437155082242,437224669659⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-4854153355),(-4853044499)⟩,⟨2214656646,2215765501⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-11402756),(-11391954)⟩,⟨(-37426091),(-37415285)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨267727,267824⟩,⟨(-19475),(-19380)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-915),(-897)⟩,⟨1989,2006⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-14),2⟩,⟨(-33),(-17)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-5),14⟩,⟨(-5),16⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-185202810898904109),(-185201863440069159)⟩,⟨369069836260841333,369070783719676284⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-50682812905282127207),(-50682812905282121594)⟩,⟨(-250083866366234734530),(-250083866366234728913)⟩⟩
noncomputable def realAnswer : RBox := ⟨(-50868015716281031316),(-50868014768622190753)⟩
end tm1_100_0

namespace tm1_100_1
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
noncomputable def s4_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨2405173553429667067,2405177508797595364⟩,⟨4358547957794293629,4358551913162221931⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨6314209821521014855,6314218223480602015⟩,⟨806371660286111761,806380062245698914⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-557180530742908053),(-557174516890515167)⟩,⟨(-1956649582885052847),(-1956643569032659964)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨60343969011839168,60346359516203961⟩,⟨432120786850597647,432123177354962443⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-11426973305529426),(-11426066285318660)⟩,⟨(-65630852365797198),(-65629945345586431)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨2032513146989755,2032654501848874⟩,⟨3901032457491107,3901173812350229⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-123833244299365),(-123823875364668)⟩,⟨(-46543909034703),(-46534540100007)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨1531520549579,1531811723488⟩,⟨(-1425103036372),(-1424811862462)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨10583337442,10588080856⟩,⟨17676954148,17681697563⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-139937637),(-139890443)⟩,⟨62219607,62266805⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-218788),(-218409)⟩,⟨(-1042436),(-1042059)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨8450,8472⟩,⟨2426,2446⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-116),(-97)⟩,⟨29,46⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-6),16⟩,⟨(-14),4⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨1368838343630085267,1368841980250792821⟩,⟨596435508477284243,596439145097991797⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-893542471514708745095),(-893542471514708723740)⟩,⟨229976043481712641271,229976043481712662610⟩⟩
noncomputable def realAnswer : RBox := ⟨(-892173633171178659828),(-892173629534357930919)⟩
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
open IntegerIntervals IntegerBasis IntegerGrid

namespace tm1_12_0
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
noncomputable def s1_0 : CBox := ⟨⟨(-740),(-724)⟩,⟨(-56),(-40)⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-1235),(-1219)⟩,⟨(-188),(-172)⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-635),(-619)⟩,⟨(-217),(-200)⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-149),(-133)⟩,⟨(-107),(-91)⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-22),(-6)⟩,⟨(-30),(-13)⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-11),15⟩,⟨(-16),0⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-8750189190681),(-8750189190665)⟩,⟨(-51938917789034),(-51938917789018)⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-27640243043800),(-27640243043784)⟩,⟨(-105078780966657),(-105078780966640)⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-35528021171572),(-35528021171556)⟩,⟨(-77880478811825),(-77880478811808)⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-24025594866626),(-24025594866610)⟩,⟨(-30748983264856),(-30748983264839)⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-9197576426981),(-9197576426964)⟩,⟨(-6633734743500),(-6633734743483)⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-2116759603228),(-2116759603212)⟩,⟨(-683410272420),(-683410272403)⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-312852955235),(-312852955219)⟩,⟨2077181227,2077181244⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-32410898521),(-32410898504)⟩,⟨9955510079,9955510096⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-2658470712),(-2658470696)⟩,⟨1528608586,1528608602⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-201536006),(-201535989)⟩,⟨151294814,151294832⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-16403059),(-16403042)⟩,⟨12443805,12443821⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-1570722),(-1570705)⟩,⟨959365,959382⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-184590),(-184574)⟩,⟨73544,73561⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-27725),(-27708)⟩,⟨5410,5427⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-5401),(-5385)⟩,⟨202,218⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-1001),(-985)⟩,⟨(-57),(-41)⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-11254227537985040963),(-11254227537983568069)⟩,⟨(-270385025629104899731),(-270385025629103426837)⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-106006857913059431991),(-106006857913056759844)⟩,⟨(-625158181736703041470),(-625158181736700369307)⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-262393603318656474676),(-262393603318654944764)⟩,⟨(-590474726484651460678),(-590474726484649930743)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-309027975744617015380),(-309027975744616536130)⟩,⟨(-308347674285326542106),(-308347674285326062837)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-206783878079884912640),(-206783878079884808854)⟩,⟨(-66081580104693010550),(-66081580104692906761)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-81420323923378687662),(-81420323923378677328)⟩,⟨20856802121153026366,20856802121153036702⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-17091444037404431817),(-17091444037404431207)⟩,⟨20073808417954129954,20073808417954130559⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-463400768840438026),(-463400768840437948)⟩,⟨6912478009149761030,6912478009149761111⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨853370214526322112,853370214526322139⟩,⟨1335244541104259674,1335244541104259705⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨306367459668055797,306367459668055818⟩,⟨126857292614223945,126857292614223962⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨66507585308310637,66507585308310654⟩,⟨(-11325978612444742),(-11325978612444725)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨11261050464569049,11261050464569065⟩,⟨(-8747114694393526),(-8747114694393510)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨1612442782754047,1612442782754063⟩,⟨(-2909961331552898),(-2909961331552882)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨176980118075084,176980118075101⟩,⟨(-873095186707094),(-873095186707077)⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-937912145926),(-937912145910)⟩,⟨(-266906416007773),(-266906416007757)⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-6483471697897),(-6483471697881)⟩,⟨(-61711254285995),(-61711254285979)⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨1461205298185024808481167,1461205298185088663628796⟩,⟨(-1891509326835518536490941),(-1891509326835454681357008)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨3139418600026983791687369,3139418600027191255239667⟩,⟨(-5396816539376474865567746),(-5396816539376267401944312)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨2117899486411432943498956,2117899486411805759039806⟩,⟨(-7570181752661103337708384),(-7570181752660730521824557)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-675363654916295341048082),(-675363654915800732668992)⟩,⟨(-7150686555466174247670288),(-7150686555465679638700378)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-2790757095517477639766309),(-2790757095516720972869611)⟩,⟨(-4394260272996193540036263),(-4394260272995436872810486)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-2837583027110929958228665),(-2837583027110066825954950)⟩,⟨(-1327863386361379470364053),(-1327863386360516338095909)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-1594442293946445719986378),(-1594442293945879843408210)⟩,⟨333944102120778977214618,333944102121344853674957⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-473244098835532438782247),(-473244098835165883512494)⟩,⟨591592020660542957034033,591592020660909512269866⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨7655778430166219608992,7655778430317497853252⟩,⟨323604761672522963310033,323604761672674241565328⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨83415714249662689448006,83415714249703709704700⟩,⟨99658238476955907169696,99658238476996927434488⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨48563539854561037551046,48563539854573229861789⟩,⟨12547125640991337474769,12547125641003529785781⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨18248229199597349993095,18248229199599609081978⟩,⟨(-5584640172629471252613),(-5584640172627212164590)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨5312470528536566942867,5312470528537007990211⟩,⟨(-5083150285296941061819),(-5083150285296500014845)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨1231894307259805595191,1231894307259921118865⟩,⟨(-2645501483537634951034),(-2645501483537519427421)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨198502370183638169687,198502370183667774650⟩,⟨(-1130068164530424066869),(-1130068164530394461904)⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨11588945687193485317,11588945687199553749⟩,⟨(-306402139002791261254),(-306402139002785192818)⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨24296283405897847732835653,24296283405897848046772041⟩,⟨4533907018224456591757323,4533907018224456858259461⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨64644005230662438961557898,64644005230662439858797089⟩,⟨(-10717998588730472848182304),(-10717998588730472101982015)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨51857031361673739478351203,51857031361673740820304286⟩,⟨(-76877238203192728497822941),(-76877238203192727377261349)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-75944220949170628768454138),(-75944220949170626841613146)⟩,⟨(-154192854023574659809995126),(-154192854023574658027999040)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-293798848236879055867580647),(-293798848236879052621598879)⟩,⟨(-144042291742698006405561498),(-144042291742698003178540004)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-454774869177657761105810485),(-454774869177657756605739939)⟩,⟨4081603576749317357220262,4081603576749321929992495⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-429555376509424942448176738),(-429555376509424937319549930)⟩,⟨203751115439623946021200207,203751115439623951229065665⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-249430251606825585430849725),(-249430251606825579931970982)⟩,⟨311339536976804186249796676,311339536976804191758596811⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-55920062292975317527538140),(-55920062292975310947817141)⟩,⟨278391809336078285279566409,278391809336078291843167776⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨51751247325381313570831680,51751247325381327442923071⟩,⟨171565645674940505996470252,171565645674940519858816231⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨73336550802208834920378521,73336550802208877264590391⟩,⟨73859766913911415672578469,73859766913911458017211233⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨54625951661502843409688557,54625951661502926438478705⟩,⟨18154586055931906450251179,18154586055931989480955752⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨30997725509916447369725047,30997725509916563319934528⟩,⟨(-3200475172205552412691518),(-3200475172205436461283800)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨14898662169002780514709606,14898662169002937215151248⟩,⟨(-7240983641335261607660504),(-7240983641335104907038545)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨6191250117038360466192058,6191250117038491787955735⟩,⟨(-5210787917888199295821743),(-5210787917888067974085105)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨1644214222731608317488142,1644214222731658211179565⟩,⟨(-1786526966229727283007557),(-1786526966229677389337136)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-197778321539544213388091804),(-197778321539543459910341517)⟩,⟨106003713703763964293525253,106003713703764717697471186⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-1002020921293390775333123593),(-1002020921293390771841143722)⟩,⟨3696060367052002023557072506,3696060367052002027063737350⟩⟩
noncomputable def realAnswer : RBox := ⟨(-1199799242832934988821215397),(-1199799242832934231651485239)⟩
end tm1_12_0

namespace tm1_12_1
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
noncomputable def s1_0 : CBox := ⟨⟨3352,3368⟩,⟨3994,4012⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨5165,5184⟩,⟨7186,7206⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨2111,2132⟩,⟨4256,4278⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨225,248⟩,⟨1226,1247⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-55),(-29)⟩,⟨172,191⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-23),(-1)⟩,⟨(-2),23⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-240574403505207),(-240574403505190)⟩,⟨192101869675816,192101869675832⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-458321056367005),(-458321056366988)⟩,⟨442745523141978,442745523141998⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-295346498085762),(-295346498085742)⟩,⟨410165406747938,410165406747956⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-85714351569152),(-85714351569132)⟩,⟨216332114420493,216332114420516⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-5441521973685),(-5441521973661)⟩,⟨68275295992848,68275295992869⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨3390710924206,3390710924231⟩,⟨13213067004691,13213067004713⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨1087819355349,1087819355373⟩,⟨1621037516473,1621037516500⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨169604494433,169604494457⟩,⟨133076331417,133076331442⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨18180166936,18180166960⟩,⟨8052260490,8052260516⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨1605981747,1605981769⟩,⟨443912285,443912308⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨134724137,134724162⟩,⟨32948341,32948364⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨11981663,11981689⟩,⟨3933376,3933398⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨1234364,1234384⟩,⟨620133,620154⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨159928,159945⟩,⟨117744,117761⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨27280,27302⟩,⟨26806,26826⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨4629,4646⟩,⟨5339,5357⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-1232743681534769455646),(-1232743681534763212195)⟩,⟨463057383255712335934,463057383255718579335⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-2732566682097904762588),(-2732566682097893949125)⟩,⟨1453252608451593528253,1453252608451604341568⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-2332319515902760837514),(-2332319515902753644401)⟩,⟨2151456137095950416550,2151456137095957609523⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-937741685805637351013),(-937741685805634519572)⟩,⟨1949131965077395727929,1949131965077398559323⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨41508647562942850452,41508647562943379928⟩,⟨1087262654719426725125,1087262654719427254615⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨245433159273504888124,245433159273504933645⟩,⟨349561754986515275709,349561754986515321249⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨128833307397812368714,128833307397812372408⟩,⟨43860123026670641444,43860123026670645143⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨34443687379359729863,34443687379359730269⟩,⟨(-11701902594335271031),(-11701902594335270626)⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨4708981154115323652,4708981154115323760⟩,⟨(-7040277107070685604),(-7040277107070685492)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-69320166638470666),(-69320166638470620)⟩,⟨(-1803003314807416100),(-1803003314807416054)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-216296631000026450),(-216296631000026422)⟩,⟨(-304492487982022066),(-304492487982022040)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-72404890838883822),(-72404890838883798)⟩,⟨(-34504172920271587),(-34504172920271564)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-18967052552062796),(-18967052552062775)⟩,⟨(-486460736945655),(-486460736945633)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-4919292397814638),(-4919292397814616)⟩,⟨1479792344820581,1479792344820597⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-1358131397774499),(-1358131397774482)⟩,⟨749104020136030,749104020136049⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-296825087387264),(-296825087387246)⟩,⟨207244066504031,207244066504047⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-8765502439124537854467484),(-8765502439124277769792027)⟩,⟨(-4634968634106478504718861),(-4634968634106218420218891)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-24369472202986593479465187),(-24369472202985764636062965)⟩,⟨(-8978866975300890137209137),(-8978866975300061294709105)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-32728165066160325271319529),(-32728165066158900434443383)⟩,⟨(-3085881738514442334831350),(-3085881738513017500106935)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-29091645995541140074489311),(-29091645995539012901375987)⟩,⟨8370517129629286381167065,8370517129631413551763951⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-16046666924609454621120808),(-16046666924606012162781099)⟩,⟨15285258346356133237187242,15285258346359575694647803⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-3094782423272755171036170),(-3094782423269180189407837)⟩,⟨13139560704996025806885127,13139560704999600788899453⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨2936381390333164205046273,2936381390335605044221595⟩,⟨6481559982855129825406797,6481559982857570665132031⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨3035538921840619059143307,3035538921842321783547219⟩,⟨1437283510882454006242493,1437283510884156730700543⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨1404519231424406922137185,1404519231425025387875270⟩,⟨(-389148502678308370868343),(-389148502677689905215735)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨341963677567390639512623,341963677567602953229555⟩,⟨(-486084574426837742317054),(-486084574426625428624062)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-5040013112672567094083),(-5040013112617484831985)⟩,⟨(-232786261988755456560994),(-232786261988700374293922)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-49528198405763782324462),(-49528198405754171398375)⟩,⟨(-74928742553674018814394),(-74928742553664407883240)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-30575494434757543235978),(-30575494434755120984050)⟩,⟨(-17078631702260430914946),(-17078631702258008662076)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-13917489995115701842276),(-13917489995115135668643)⟩,⟨(-1804722926022307123752),(-1804722926021740950199)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-5501141881096964836536),(-5501141881096830604276)⟩,⟨770226163629985830721,770226163630120062822⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-1432247824330462921656),(-1432247824330436604806)⟩,⟨409283606302571694910,409283606302598011702⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨11769523686183150872974238,11769523686183151821233662⟩,⟨(-88644117261386889847160639),(-88644117261386888712412832)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-51615219912648653998634933),(-51615219912648651339436923)⟩,⟨(-231934628791934713590403610),(-231934628791934710343939164)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-290702059209357786834983767),(-290702059209357782542925334)⟩,⟨(-171999642759742450340670989),(-171999642759742445279816410)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-546288184240294419119239090),(-546288184240294412236367558)⟩,⟨315043921840860955338360594,315043921840860962678293104⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-452582279598606084784432242),(-452582279598606072216515217)⟩,⟨1123610270028040299913042235,1123610270028040312476392754⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨154349848801774383687558078,154349848801774401786768834⟩,⟨1694260149047432335736748447,1694260149047432353508168453⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨917332671938860475777149046,917332671938860497049537046⟩,⟨1548005001656406317152694568,1548005001656406338146998823⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨1285395837295915952040263235,1285395837295915974766401543⟩,⟨828184352993489874959057945,828184352993489897678116825⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨1098954950069032083111805156,1098954950069032109211562206⟩,⟨92167742981840733316460542,92167742981840759493611074⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨644232775693832225656575553,644232775693832284158225830⟩,⟨(-286920729927776098081094823),(-286920729927776039549845282)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨251697700682526755897454345,251697700682526924305423935⟩,⟨(-329790658638737841357324445),(-329790658638737672955849065)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨40121894817112142157233796,40121894817112450399150277⟩,⟨(-228650122611873511999554890),(-228650122611873203767270736)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-32486313945429363309400450),(-32486313945428849323816280)⟩,⟨(-122729364012368562390160646),(-122729364012368048408293580)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-39266098562346399497093573),(-39266098562345722428936840)⟩,⟨(-55562077625396501890048619),(-55562077625395824821919997)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-25488536000449686818411077),(-25488536000449137777805522)⟩,⟨(-21623696364028824173642665),(-21623696364028275132612006)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-8447015626373190089344068),(-8447015626372985006208761)⟩,⟨(-5460183804097348730077873),(-5460183804097143646769211)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨475081481440853721511509712,475081481440856937589461566⟩,⟨680796250642126713049242128,680796250642129929371206804⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨13527996127887396555248352713,13527996127887396568634384538⟩,⟨2913507023100322759733893015,2913507023100322773040723109⟩⟩
noncomputable def realAnswer : RBox := ⟨14003077609328250276659862425,14003077609328253506323846104⟩
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
open IntegerIntervals IntegerBasis IntegerGrid

namespace tm1_13_0
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
noncomputable def s1_0 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-16),6⟩,⟨(-16),0⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-12),16⟩,⟨(-16),0⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),15⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨2605893980324,2605893980340⟩,⟨(-1649988585938),(-1649988585922)⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨4875192233736,4875192233752⟩,⟨(-3790017550015),(-3790017549998)⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨3048486943644,3048486943660⟩,⟨(-3423266537092),(-3423266537076)⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨876326786382,876326786398⟩,⟨(-1700115461186),(-1700115461170)⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨85506072256,85506072273⟩,⟨(-487321873228),(-487321873211)⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-13376678020),(-13376678003)⟩,⟨(-83064259497),(-83064259480)⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-4788690914),(-4788690896)⟩,⟨(-8798572922),(-8798572904)⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-650088513),(-650088497)⟩,⟨(-623524240),(-623524224)⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-57489873),(-57489855)⟩,⟨(-33679197),(-33679180)⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-4086573),(-4086556)⟩,⟨(-1749285),(-1749268)⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-271456),(-271438)⟩,⟨(-116161),(-116144)⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-18864),(-18847)⟩,⟨(-10745),(-10729)⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-1506),(-1489)⟩,⟨(-1282),(-1265)⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-158),(-142)⟩,⟨(-200),(-184)⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-28),(-11)⟩,⟨(-46),(-29)⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨59107914184859020371,59107914184859348521⟩,⟨2857365850255043502,2857365850255371655⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨135529682463390992329,135529682463391581991⟩,⟨(-11894646134605019076),(-11894646134604429415)⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨125119519217323630524,125119519217323960235⟩,⟨(-46574548168472746670),(-46574548168472416965)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨62298479423424101113,62298479423424193783⟩,⟨(-58243900508999344909),(-58243900508999252245)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨11997589800809510416,11997589800809529413⟩,⟨(-37530710687741305365),(-37530710687741286366)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-4008510617563759098),(-4008510617563757367)⟩,⟨(-13355010233865137396),(-13355010233865135661)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-3209278855017422847),(-3209278855017422736)⟩,⟨(-2285804406673230932),(-2285804406673230822)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-919392542075229009),(-919392542075228980)⟩,⟨62440017278609260,62440017278609288⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-135755087217421767),(-135755087217421750)⟩,⟨127064499011572543,127064499011572559⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-5495738299172704),(-5495738299172687)⟩,⟨33719100899217707,33719100899217723⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨2620039663137770,2620039663137786⟩,⟨5515607116947899,5515607116947915⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨943773344277869,943773344277886⟩,⟨641682101293196,641682101293213⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨235516000631800,235516000631816⟩,⟨38218164787934,38218164787952⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨57567026354051,57567026354067⟩,⟨(-9849438186009),(-9849438185993)⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨15188131449531,15188131449547⟩,⟨(-6230759919635),(-6230759919618)⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨3242398570451,3242398570468⟩,⟨(-1765644688230),(-1765644688214)⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨335041943696238054090867,335041943696263978454664⟩,⟨1129577969846265601337692,1129577969846291525799235⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨1263277774149152522233417,1263277774149243303774512⟩,⟨2765611132855700336831872,2765611132855791118589601⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨2409591141390835009635268,2409591141391020813532500⟩,⟨2856154472303984079019193,2856154472304169883070970⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨2927844385164337167473819,2927844385164623368110391⟩,⟨1510707802943754411741645,1510707802944040612344945⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨2277914844986004086412205,2277914844986303757376469⟩,⟨(-67526957518602611088380),(-67526957518302940284447)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨1041004712619648337591083,1041004712619976878416083⟩,⟨(-771643557759999965177282),(-771643557759671424431355)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨151473413050259671365244,151473413050517528786723⟩,⟨(-612508533463687792077221),(-612508533463429934643300)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-130171094139160057589522),(-130171094139045431142387)⟩,⟨(-239763836928692868164523),(-239763836928578241696783)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-102276872303489525073926),(-102276872303436491299752)⟩,⟨(-34215287398519933809417),(-34215287398466900034390)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-36776114638595727460281),(-36776114638582734964464)⟩,⟨15661551934366151955821,15661551934379144449260⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-6798653090599636135718),(-6798653090596298210069)⟩,⟨12529231691575916608093,12529231691579254533334⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨494108482280944466380,494108482281596012153⟩,⟨5009982175329799443743,5009982175330450989654⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨1031120070384361052857,1031120070384463822762⟩,⟨1494344090042631341850,1494344090042734111858⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨577114888480846911702,577114888480873007013⟩,⟨364937914022274446832,364937914022300542162⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨248343272250836543958,248343272250843213855⟩,⟨71459639645602652315,71459639645609322210⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨67110838146574302061,67110838146575659909⟩,⟨8973290805473340625,8973290805474698473⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-19606806482230513773721531),(-19606806482230513490443861)⟩,⟨5786123296707244553738185,5786123296707244796488131⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-43001324347670023149220431),(-43001324347670022292627458)⟩,⟨32245996263889399886054083,32245996263889400651821475⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-7387013752360833983882969),(-7387013752360832643808858)⟩,⟨74398198644455397707002638,74398198644455398982557969⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨112068717890266260526891980,112068717890266262315423538⟩,⟨75639681941016556661019511,75639681941016558469490962⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨248732455684833582044205419,248732455684833585022003445⟩,⟨(-23613251133312725258604333),(-23613251133312722183157382)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨277275918770633035019198398,277275918770633039306217018⟩,⟨(-187863885636936608425254702),(-187863885636936604053289545)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨161222278298407893174942386,161222278298407898207127844⟩,⟨(-294491099004639460778291121),(-294491099004639455740483780)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨1239522050977471559918302,1239522050977476330703968⟩,⟨(-268912051011014781098573628),(-268912051011014776353170952)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-90245413784908280211516840),(-90245413784908275009081574)⟩,⟨(-158233751769866796334602753),(-158233751769866791142166691)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-95078833037391051864787870),(-95078833037391042030711149)⟩,⟨(-53856693532656455940612034),(-53856693532656446104134672)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-60370435695068930675850868),(-60370435695068910556452481)⟩,⟨1073163063188143655708591,1073163063188163778061715⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-27550228289355023421303063),(-27550228289354973827812598)⟩,⟨16017792940400772358829584,16017792940400821952654236⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-9142162533255741662719619),(-9142162533255664798459006)⟩,⟨13802967788033168510978238,13802967788033245374938913⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-1750700430924558174099384),(-1750700430924483563177460)⟩,⟨8330568106881821814410533,8330568106881896425057769⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨243022343595643120820609,243022343595692564532210⟩,⟨4054981087661281863088094,4054981087661331306654926⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨235996573937433093501650,235996573937452544108204⟩,⟨1180848457012939089742130,1180848457012958540315902⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨76169653719426930635926048,76169653719427261638469218⟩,⟨(-124644840601904711205165313),(-124644840601904380205610819)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-637416186602891221496443004),(-637416186602891217218656278)⟩,⟨(-3104999625689209902987020949),(-3104999625689209898659830851)⟩⟩
noncomputable def realAnswer : RBox := ⟨(-561246532883464290960516956),(-561246532883463955480187060)⟩
end tm1_13_0

namespace tm1_13_1
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
noncomputable def s1_0 : CBox := ⟨⟨(-25),(-8)⟩,⟨26,43⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-39),(-16)⟩,⟨44,61⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-30),(-9)⟩,⟨13,33⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-16),1⟩,⟨(-7),16⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-16),15⟩,⟨(-16),16⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-15826122038583),(-15826122038567)⟩,⟨(-8633758996931),(-8633758996914)⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-33369379467925),(-33369379467905)⟩,⟨(-14073159419638),(-14073159419621)⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-26475635012842),(-26475635012821)⟩,⟨(-5611656367222),(-5611656367202)⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-11387407291940),(-11387407291918)⟩,⟨618476287899,618476287919⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-2783966969705),(-2783966969684)⟩,⟨1084482549410,1084482549430⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-386825061433),(-386825061412)⟩,⟨341291887100,341291887122⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-29313214271),(-29313214244)⟩,⟨55190684755,55190684778⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-897361667),(-897361642)⟩,⟨5655234324,5655234344⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨43875166,43875189⟩,⟨429672508,429672527⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨7337468,7337488⟩,⟨28453048,28453072⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨544393,544418⟩,⟨1912530,1912556⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨27686,27705⟩,⟨146035,146055⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨278,297⟩,⟨13664,13688⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-296),(-277)⟩,⟨1673,1692⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-104),(-86)⟩,⟨272,291⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-30),(-13)⟩,⟨39,56⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-76646409973311273397),(-76646409973309835648)⟩,⟨(-277568966371039339419),(-277568966371037901663)⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-263692243373396868532),(-263692243373394400784)⟩,⟨(-609455469630037617702),(-609455469630035149927)⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-413883000914232642570),(-413883000914231200804)⟩,⟨(-508425735838709131716),(-508425735838707689919)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-374154123174791392893),(-374154123174790843875)⟩,⟨(-196301548624226065063),(-196301548624225516034)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-197316884994794742859),(-197316884994794645896)⟩,⟨7503741149304899729,7503741149304996691⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-56275305843943305142),(-56275305843943297538)⟩,⟨43038164322111413304,43038164322111420908⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-4869461939525747980),(-4869461939525747378)⟩,⟨19743351267246521069,19743351267246521671⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨2156846959261402900,2156846959261402980⟩,⟨4330113967353858957,4330113967353859033⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨912862531359831905,912862531359831940⟩,⟨392423634419707536,392423634419707571⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨179161269577539348,179161269577539371⟩,⟨(-49448908313252475),(-49448908313252451)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨21212874889979971,21212874889979995⟩,⟨(-26312764337059583),(-26312764337059561)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨841878128344260,841878128344282⟩,⟨(-6362956379166018),(-6362956379165995)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-427220535516946),(-427220535516926)⟩,⟨(-1291773726234056),(-1291773726234031)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-206898845173367),(-206898845173349)⟩,⟨(-265704601247067),(-265704601247047)⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-74117855184516),(-74117855184497)⟩,⟨(-60056480683688),(-60056480683668)⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-18165359754184),(-18165359754168)⟩,⟨(-11574570205230),(-11574570205214)⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨4380361146213842113640858,4380361146213960732196752⟩,⟨(-2168565335237223819000567),(-2168565335237105200756911)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨10421515899353041911629968,10421515899353447391498711⟩,⟨(-7165473335981819556033050),(-7165473335981414076795052)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨64529910776131637309080,64529910776147779608931⟩,⟨14614224472500339693377,14614224472516481993382⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨21954094157375475238177,21954094157378188391670⟩,⟨(-8905534492976620182046),(-8905534492973907029731)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨5361489551123894881143,5361489551124457765185⟩,⟨(-6784484101669627465518),(-6784484101669064581818)⟩⟩
noncomputable def ans : CBox := ⟨⟨(-489847203140189991420600793),(-489847203140188582997024353)⟩,⟨(-226419006015177702743824675),(-226419006015176294336723987)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-11086270778196342944556195840),(-11086270778196342928075453840)⟩,⟨2885201720612346506430830249,2885201720612346522715432740⟩⟩
noncomputable def realAnswer : RBox := ⟨(-11576117981336532936076796633),(-11576117981336531510972478193)⟩
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
open IntegerIntervals IntegerBasis IntegerGrid

namespace tm1_15_0
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
end tm1_15_0

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
open IntegerIntervals IntegerBasis IntegerGrid
namespace tm0_69_0
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
noncomputable def s4_0 : CBox := ⟨⟨4405346,4405362⟩,⟨(-22061260),(-22061244)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-11541610),(-11541593)⟩,⟨(-26936917),(-26936901)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-9415330),(-9415313)⟩,⟨299989,300005⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨281359,281376⟩,⟨1141274,1141292⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨34850,34867⟩,⟨(-54953),(-54936)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-1339),(-1322)⟩,⟨1101,1120⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨5,25⟩,⟨(-28),(-7)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-1085839799955651238726),(-1085839798731241580207)⟩,⟨16628926392024693952719,16628926393249103613013⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨13751932685325300269097,13751932688045346107452⟩,⟨24958855676414400829913,24958855679134446670145⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨15771242475991833093315,15771242478429718204612⟩,⟨(-876683958489359469954),(-876683956051474359803)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-556371517931530705946),(-556371516646291155914)⟩,⟨(-4437149791742093466741),(-4437149790456853916478)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-583964517464567760834),(-583964517039507880965)⟩,⟨446343457141020993908,446343457566080873745⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨74547147515277158506,74547147601868785071⟩,⟨(-399938043371653367),(-399937956780026808)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-4687391285073162991),(-4687391274219892521)⟩,⟨(-1471843213657693538),(-1471843202804423071)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨213086622400253455,213086623267513638⟩,⟨76989169921946229,76989170789206415⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-7888864536403690),(-7888864489688004)⟩,⟨(-1759137163037109),(-1759137116321424)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨251674998307070,251675000160397⟩,⟨11013281630561,11013283483890⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-7879839567290),(-7879839504401)⟩,⟨343238068343,343238131236⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨286952515351,286952517581⟩,⟨29471182248,29471184478⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-11591825077),(-11591824966)⟩,⟨(-8367432832),(-8367432723)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-94678559),(-94678532)⟩,⟨1084615038,1084615059⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨132335642,132335660⟩,⟨23301791,23301808⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨16383620,16383636⟩,⟨(-11042565),(-11042549)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
end tm0_69_0

namespace tm0_69_1
noncomputable def s0_0 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-75),75⟩,⟨(-75),75⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-88),88⟩,⟨(-88),88⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-89),89⟩,⟨(-89),89⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-74),74⟩,⟨(-74),74⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-47),47⟩,⟨(-47),47⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-21),21⟩,⟨(-21),21⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-28),28⟩,⟨(-28),28⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-38),38⟩,⟨(-38),38⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-65),65⟩,⟨(-65),65⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-79),79⟩,⟨(-79),79⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-45),45⟩,⟨(-45),45⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-31),31⟩,⟨(-31),31⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-27),27⟩,⟨(-27),27⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-93289004),(-93288985)⟩,⟨(-2402660),(-2402643)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-101995313),(-101995292)⟩,⟨66618641,66618660⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨8210977,8210997⟩,⟨38463573,38463594⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨4497199,4497222⟩,⟨(-2045399),(-2045378)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-257142),(-257117)⟩,⟨(-100254),(-100232)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨5805,5830⟩,⟨4616,4642⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-102),(-76)⟩,⟨(-70),(-43)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨60285029029825152926743,60285029034481319787417⟩,⟨767132176650696119492,767132181306862973469⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨87621977620780674077716,87621977631166480126084⟩,⟨(-54715095399175484396081),(-54715095388789678353753)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-6553556433048012604342),(-6553556423665185046854)⟩,⟨(-57110917475529416643193),(-57110917466146589081365)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-16077883775138253071221),(-16077883770134133634480)⟩,⟨3081375287258362550836,3081375292262481986683⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨1797461190894450407546,1797461192574099597414⟩,⟨2030301433305104441972,2030301434984753631954⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-23880466091157922342),(-23880465742944242398)⟩,⟨(-276641057243219089880),(-276641056895005409930)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-3923863273548992183),(-3923863229035139825)⟩,⟨18083977654463723565,18083977698977575924⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨209882333760022266,209882337393670628⟩,⟨(-838125651260382017),(-838125647626733653)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-3326129109063658),(-3326128908941726)⟩,⟨31054295443072724,31054295643194655⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-79379619294843),(-79379611176830)⟩,⟨(-983438444739808),(-983438436621795)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨5577011081319,5577011362749⟩,⟨30802004012249,30802004293679⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-50720108899),(-50720098770)⟩,⟨(-1158092838867),(-1158092828744)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-26307132478),(-26307132024)⟩,⟨51795849106,51795849558⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨4452192042,4452192090⟩,⟨(-336775233),(-336775190)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨3729422,3729442⟩,⟨(-554680452),(-554680431)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-56569205),(-56569187)⟩,⟨(-59143453),(-59143436)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨21174238297713089474598,21174238302963945943170⟩,⟨(-17701094847029816397218),(-17701094841778959930177)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨38704909505994508487871,38704909505994513884942⟩,⟨(-234819201110769185749223),(-234819201110769180350401)⟩⟩
noncomputable def realAnswer : RBox := ⟨59879147803707497962469,59879147808958559828112⟩
end tm0_69_1

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
open IntegerIntervals IntegerBasis IntegerGrid
namespace tm0_7_0
noncomputable def s0_0 : CBox := ⟨⟨1539434,1539451⟩,⟨339993,340009⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨2847185,2847204⟩,⟨1681589,1681608⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨1060896,1060917⟩,⟨2533390,2533409⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-783327),(-783305)⟩,⟨1187262,1187280⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-501375),(-501352)⟩,⟨(-180817),(-180795)⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨72970,72997⟩,⟨(-144213),(-144193)⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨26266,26291⟩,⟨35621,35644⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-12162),(-12137)⟩,⟨(-1605),(-1584)⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨3402,3425⟩,⟨(-1695),(-1669)⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-848),(-827)⟩,⟨1155,1179⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨43,67⟩,⟨(-692),(-671)⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨241,261⟩,⟨307,327⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-284),(-261)⟩,⟨39,59⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-36),(-16)⟩,⟨(-205),(-186)⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨92,111⟩,⟨(-78),(-59)⟩⟩
noncomputable def s1_0 : CBox := ⟨⟨(-240893496939230),(-240893496939213)⟩,⟨(-43274226767668),(-43274226767652)⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-510123911851399),(-510123911851380)⟩,⟨(-119285153681734),(-119285153681716)⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-420858353187185),(-420858353187164)⟩,⟨(-149631040516078),(-149631040516060)⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-200542529638357),(-200542529638339)⟩,⟨(-117097303410945),(-117097303410923)⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-56605662673762),(-56605662673740)⟩,⟨(-59563331873121),(-59563331873101)⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-7430392378025),(-7430392378000)⟩,⟨(-19796589260928),(-19796589260907)⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨763663786584,763663786610⟩,⟨(-4142268182664),(-4142268182640)⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨536385917887,536385917910⟩,⟨(-443587452820),(-443587452799)⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨101780216706,101780216726⟩,⟨16938642841,16938642863⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨5949687782,5949687803⟩,⟨13698538575,13698538595⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-1451063720),(-1451063698)⟩,⟨1782583931,1782583953⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-394859166),(-394859142)⟩,⟨(-93847070),(-93847045)⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-23746191),(-23746169)⟩,⟨(-83532019),(-83531998)⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨13438168,13438189⟩,⟨(-18533609),(-18533589)⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨6721670,6721688⟩,⟨(-1959492),(-1959476)⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨1659482,1659498⟩,⟨106825,106841⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-100604803925571854159),(-100604803925571853465)⟩,⟨(-323634156508143957295),(-323634156508143956577)⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-289914652935443896154),(-289914652935443894454)⟩,⟨(-759375407410018500682),(-759375407410018498930)⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-405493924002755726572),(-405493924002755724581)⟩,⟨(-767555209430897938595),(-767555209430897936563)⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-382411765169183107148),(-382411765169183105494)⟩,⟨(-498599019948878623320),(-498599019948878621646)⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-256159945410949100807),(-256159945410949099755)⟩,⟨(-223729118537419268205),(-223729118537419267152)⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-125942672519681985010),(-125942672519681984477)⟩,⟨(-70247252081286905613),(-70247252081286905079)⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-47242447223062030035),(-47242447223062029808)⟩,⟨(-15090123390447427938),(-15090123390447427711)⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-14211220366411580108),(-14211220366411580019)⟩,⟨(-1970122281285136634),(-1970122281285136545)⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-3646026578755884170),(-3646026578755884126)⟩,⟨(-38841078742971920),(-38841078742971877)⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-855415036589945491),(-855415036589945460)⟩,⟨52084930192312191,52084930192312222⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-196863134307552306),(-196863134307552278)⟩,⟨14347258431906382,14347258431906408⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-47272434957905145),(-47272434957905118)⟩,⟨1435425821840870,1435425821840897⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-12408335987845460),(-12408335987845436)⟩,⟨(-641376779010148),(-641376779010121)⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-3644220158913936),(-3644220158913913)⟩,⟨(-550652063016583),(-550652063016560)⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-1157779365535812),(-1157779365535790)⟩,⟨(-279522473330094),(-279522473330076)⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-276443664505579),(-276443664505562)⟩,⟨(-81778720480090),(-81778720480071)⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-688372743224836779855815),(-688372743224834008398266)⟩,⟨1465600209863387751720993,1465600209863390523428537⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-1485990613483959526554353),(-1485990613483954085197203)⟩,⟨3967119847836198864138486,3967119847836204306191092⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-1071127071571651049015345),(-1071127071571646509020302)⟩,⟨5261219950637883904635953,5261219950637888445413528⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨131984627558196016259191,131984627558198221103130⟩,⟨4990145577882804719994255,4990145577882806925361053⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨1153600027076870023899521,1153600027076870635762450⟩,⟨3550082321950546898586323,3550082321950547510630256⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨1418229410490137446685589,1418229410490137544740477⟩,⟨1860315305572060778896090,1860315305572060876902140⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨1080315118973696391647703,1080315118973696402370789⟩,⟨657508448975718334522393,657508448975718345130275⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨598218876370293868357555,598218876370293870092775⟩,⟨94028687614746173095671,94028687614746174750598⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨256500693179993853245281,256500693179993853929172⟩,⟨(-61168805774330422249834),(-61168805774330421587618)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨88338405721490514577860,88338405721490514884599⟩,⟨(-61126018193869638794036),(-61126018193869638489304)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨24819050605491833104904,24819050605491833239990⟩,⟨(-34164574295974140388471),(-34164574295974140251685)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨5458840089865646845327,5458840089865646904065⟩,⟨(-15610628686718619628044),(-15610628686718619567895)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨646106535203212718780,646106535203212744616⟩,⟨(-6601615307898688495671),(-6601615307898688469080)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-229758708293679033444),(-229758708293679021864)⟩,⟨(-2741215666966755634377),(-2741215666966755622508)⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-228125487618324907308),(-228125487618324902343)⟩,⟨(-1097794842323440476281),(-1097794842323440471211)⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-80204508351379945102),(-80204508351379943707)⟩,⟨(-294911153101677340908),(-294911153101677339489)⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨186732741459047350830017273,186732741459050021235340998⟩,⟨166146814727226741205578892,166146814727229411613347707⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨547728880228295625561136604,547728880228304931925907399⟩,⟨403091647121351255423673347,403091647121360561804990927⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨841632960383831594144903169,841632960383851352895447757⟩,⟨407524070809015642475309970,407524070809035401275465501⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨973428344498812220244308477,973428344498847218415673088⟩,⟨179509087686436341468519913,179509087686471339732711947⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨878132216561948946658377333,878132216561998742616079018⟩,⟨(-141251125101789332291069685),(-141251125101739536208334402)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨599542855534389877719644531,599542855534462961566864537⟩,⟨(-374267106799051128344591355),(-374267106798978044407923575)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨275749593021127260972553263,275749593021220157558586345⟩,⟨(-426114825591504138372399941),(-426114825591411241758873181)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨37348123019552656785502403,37348123019630056712792131⟩,⟨(-332688577840067838460408271),(-332688577839990438540787256)⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-72484052804842833549436338),(-72484052804800719604926029)⟩,⟨(-193027288274902819362486605),(-193027288274860705437816679)⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-88434513649286627683678487),(-88434513649269706701928546)⟩,⟨(-82177510631668390931614292),(-82177510631651469965754051)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-65166353241205861315687913),(-65166353241198520442538924)⟩,⟨(-20997934572831223628416635),(-20997934572823882760386145)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨(-38110639889091683308705465),(-38110639889089253539050704)⟩,⟨3084402954624984270423377,3084402954627414039592504⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-19411649946167953355050154),(-19411649946167267483956316)⟩,⟨8451472952204420498184578,8451472952205106370092010⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-9017669591415615816267893),(-9017669591415429217011380)⟩,⟨7067697615126886317244122,7067697615127072917353029⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-3780300088987954762108790),(-3780300088987902507307233)⟩,⟨4187082194995577570054295,4187082194995629825397634⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-1023437628510366749916741),(-1023437628510355357798430)⟩,⟨1351817197576822447702020,1351817197576833840000069⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨1827879466123140236120418442,1827879466123140238540429151⟩,⟨(-1126739139817542892558790835),(-1126739139817542890252408424)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨4776432965880097604395115263,4776432965880097611657002646⟩,⟨(-3712717205347653585881870203),(-3712717205347653578874681999)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨5795858630337494624896490716,5795858630337494636871453933⟩,⟨(-6874075364583024727956688211),(-6874075364583024716163532340)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨4319623102910233545677060007,4319623102910233561886010105⟩,⟨(-9918339376820589888102921943),(-9918339376820589871813864629)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨826761425603034320293702682,826761425603034339870238944⟩,⟨(-11494846672006502269868478066),(-11494846672006502249912195765)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-3233373288266948815456322845),(-3233373288266948794157847001)⟩,⟨(-10597743829771770344512071333),(-10597743829771770322650707332)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-6165809870717808026765198372),(-6165809870717808004616354446)⟩,⟨(-7464137595195215721975932709),(-7464137595195215699343398124)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-6996195237013777232866719681),(-6996195237013777205870168866)⟩,⟨(-3470825697719519566178307932),(-3470825697719519538998062168)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-5933044206750682415236911502),(-5933044206750682358765410178)⟩,⟨(-148997572258449746705916090),(-148997572258449690222348362)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-3969570981950666332301485709),(-3969570981950666129949633728)⟩,⟨1715711877146521574028917913,1715711877146521776355242776⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-2093266657941525098204514838),(-2093266657941524455688455285)⟩,⟨2229313251170046341678054668,2229313251170046984187996315⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-803222565204542677053940777),(-803222565204540914800268709)⟩,⟨1946899337950684901356935970,1946899337950686663624407677⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-128529352967505295144396765),(-128529352967501353334339706)⟩,⟨1394490435375287982603212050,1394490435375291924430309721⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨118500586514969348498439815,118500586514974990739126225⟩,⟨867264719545711968044380137,867264719545717610295577967⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨135583053970910048493843006,135583053970915131788588048⟩,⟨455863825519356961796202724,455863825519362045095291721⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨53830704643173759450965493,53830704643175792338091690⟩,⟨140290702767285288839680155,140290702767287321727886256⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def ans : CBox := ⟨⟨(-1237360778511536634336309595),(-1237360778511461774488015059)⟩,⟨(-7737839670830944557508251842),(-7737839670830869697405599439)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-3623898971532113211317326047),(-3623898971532113208125010435)⟩,⟨(-6932064482439222866706774708),(-6932064482439222863394048234)⟩⟩
noncomputable def realAnswer : RBox := ⟨(-4861259750043649845753635642),(-4861259750043574982513025494)⟩
end tm0_7_0

namespace tm0_7_1
noncomputable def s0_0 : CBox := ⟨⟨(-10561145),(-10561119)⟩,⟨(-8315978),(-8315953)⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-15848860),(-15848817)⟩,⟨(-23420314),(-23420270)⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨740948,741008⟩,⟨(-23613624),(-23613562)⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨10311750,10311827⟩,⟨(-6770553),(-6770474)⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨3495041,3495134⟩,⟨3095614,3095706⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-1040546),(-1040452)⟩,⟨983423,983520⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-128291),(-128189)⟩,⟨(-375485),(-375379)⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨102439,102540⟩,⟨42554,42658⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-33843),(-33742)⟩,⟨8193,8292⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨9384,9480⟩,⟨(-9309),(-9212)⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-1356),(-1269)⟩,⟨6150,6233⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-2078),(-2004)⟩,⟨(-3173),(-3099)⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨2509,2567⟩,⟨(-346),(-283)⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨156,202⟩,⟨1782,1830⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-974),(-939)⟩,⟨600,634⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-403),(-384)⟩,⟨(-5),19⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨966123652340115,966123652340139⟩,⟨1453699018937275,1453699018937299⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨1927956854425152,1927956854425187⟩,⟨3216081273079775,3216081273079814⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨1368277239132940,1368277239132990⟩,⟨2914641328762531,2914641328762582⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨447801102278604,447801102278665⟩,⟨1631098773622906,1631098773622968⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨3870087447172,3870087447246⟩,⟨606449383386370,606449383386446⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-57207728386258),(-57207728386176)⟩,⟨147823987222619,147823987222700⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-24789446939905),(-24789446939817)⟩,⟨20429920948009,20429920948096⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-5404011556141),(-5404011556046)⟩,⟨129717617537,129717617632⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-569964095528),(-569964095427)⟩,⟨(-584020601202),(-584020601105)⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨22429816219,22429816317⟩,⟨(-118089181935),(-118089181839)⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨17812938667,17812938756⟩,⟨(-5998058402),(-5998058313)⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨2430419205,2430419289⟩,⟨2326494969,2326495054⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-162050223),(-162050153)⟩,⟨709549345,709549417⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-172866879),(-172866822)⟩,⟨86757235,86757290⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-58520007),(-58519964)⟩,⟨(-10548606),(-10548566)⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-12302374),(-12302350)⟩,⟨(-7009365),(-7009338)⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-1368267985810438232886),(-1368267985810438227489)⟩,⟨1432509750741735451760,1432509750741735457166⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-3053610598304448498228),(-3053610598304448484880)⟩,⟨3661684412632035049619,3661684412632035063031⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-2748475019929182887857),(-2748475019929182872190)⟩,⟨4328488070359073703201,4328488070359073719015⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-1410405031362118741418),(-1410405031362118728384)⟩,⟨3473959886375903850495,3473959886375903863714⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-351325798482549857889),(-351325798482549849575)⟩,⟨2025835946980016088018,2025835946980016096481⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨49486167175186420544,49486167175186424773⟩,⟨884094781730368517539,884094781730368521851⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨84664878103142643369,84664878103142645150⟩,⟨298119201651376845740,298119201651376847552⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨41492003907837615866,41492003907837616527⟩,⟨81398692056437331023,81398692056437331691⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨13818188216848354007,13818188216848354264⟩,⟨19227018156926015981,19227018156926016240⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨3740472309352314125,3740472309352314263⟩,⟨4266571030008875913,4266571030008876053⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨913625541394026019,913625541394026134⟩,⟨968179708114704882,968179708114704998⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨218013763424769013,218013763424769115⟩,⟨240141242483878389,240141242483878490⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨54049571432914334,54049571432914420⟩,⟨67452757080344074,67452757080344160⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨14506588001823470,14506588001823539⟩,⟨21491810050559590,21491810050559657⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨4184784979160439,4184784979160484⟩,⟨7334731785147233,7334731785147277⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨936277374687019,936277374687047⟩,⟨1825989699702375,1825989699702402⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨7821265035394315968979125,7821265035394330914000580⟩,⟨953993818943550348852090,953993818943565292868481⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨20664923216928590966243102,20664923216928623226598036⟩,⟨776328197683043195197178,776328197683075453244797⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨26163805829479733338213060,26163805829479760087184053⟩,⟨(-3318636810667779640325796),(-3318636810667752893436039)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨23137106322083461006458885,23137106322083473144020741⟩,⟨(-8774906110720157359247687),(-8774906110720145222438116)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨14768536692105534930407899,14768536692105538046307933⟩,⟨(-11507654692616534187211000),(-11507654692616531070737889)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨6296951459765052473277480,6296951459765052928980954⟩,⟨(-10095881742460873672881360),(-10095881742460873216020459)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨1099526673930018835748057,1099526673930018885087081⟩,⟨(-6442366577069025027848474),(-6442366577069024977633871)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-754134273426972210574347),(-754134273426972199388788)⟩,⟨(-3092901635160308934021265),(-3092901635160308922597080)⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-851106978784366556180592),(-851106978784366551574300)⟩,⟨(-1125654814946483911535803),(-1125654814946483906926195)⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-503833026009235305482805),(-503833026009235303331206)⟩,⟨(-297765088096442940665001),(-297765088096442938550754)⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-230304859949997353629668),(-230304859949997352646529)⟩,⟨(-41586114101047265149999),(-41586114101047264193224)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨(-92317369506644066202967),(-92317369506644065757364)⟩,⟨12052857347875573775060,12052857347875574211562⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨(-35106958081734518242849),(-35106958081734518040455)⟩,⟨14151813737383824866141,14151813737383825066209⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨(-13307117850846857419427),(-13307117850846857327940)⟩,⟨8643409136931900868551,8643409136931900959524⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨(-4960888773960585892706),(-4960888773960585853411)⟩,⟨4225455818319606853901,4225455818319606893119⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨(-1279608626219911998017),(-1279608626219911987042)⟩,⟨1241767203922601960662,1241767203922601971628⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨547071374487599164547335491,547071374487610075788319435⟩,⟨(-880835001208826306193406026),(-880835001208815395002221082)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨1257391827285988942756782206,1257391827286026579688272532⟩,⟨(-2534163220284551894966103987),(-2534163220284514258212363668)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨1051237853245581556833678338,1051237853245659703849432359⟩,⟨(-3767018864720407815332183313),(-3767018864720329668675061741)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-15315847448897588530265397),(-15315847448764623176356997)⟩,⟨(-4172757439357829833044252675),(-4172757439357696868236648204)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-1316078831631661625509471928),(-1316078831631451906315638602)⟩,⟨(-3551937848054741160266542168),(-3551937848054531441630572706)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-2109111633996259461220293974),(-2109111633995906989493701018)⟩,⟨(-2199001124673828205611309121),(-2199001124673475734143238404)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-2079897109023901780835485985),(-2079897109023481708291740390)⟩,⟨(-771760232954436590413424517),(-771760232954016517884220553)⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-1474413392168482544386599631),(-1474413392168156015550610442)⟩,⟨179064501301142118645217749,179064501301468647587735510⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-763588504458331878325235297),(-763588504458165035326534176)⟩,⟨529201173812093291078118923,529201173812260134200150210⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨(-258878913545799282726719658),(-258878913545710187562025792)⟩,⟨488046654963563193770059163,488046654963652288986186744⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨(-11758633435292511921816497),(-11758633435255917410193168)⟩,⟨317808655442907121144555113,317808655442943715662934446⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨64786435347151297225850315,64786435347162491176935062⟩,⟨167991028872480645163300152,167991028872491839106675683⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨65672845088343632885447724,65672845088346554861752816⟩,⟨76581554876269921503773105,76581554876272843470948710⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨45513999055040478574289359,45513999055041218681229433⟩,⟨31076961584234496310431418,31076961584235236410816665⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨24924208862900812517045262,24924208862901048336267081⟩,⟨11171104114260933547517434,11171104114261169363741357⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨7787624343943136191675512,7787624343943194195690022⟩,⟨2683692857647296916498082,2683692857647354919705060⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-4417899747386419077856539399),(-4417899747386419069152448055)⟩,⟨(-6390463947482317971877143346),(-6390463947482317962821466913)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-14389329679733437036251267055),(-14389329679733437009734406137)⟩,⟨(-16561986115457039320694385442),(-16561986115457039293434819877)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-26241578592184732884959131666),(-26241578592184732840087915485)⟩,⟨(-19611512886158875008081303329),(-19611512886158874962836004145)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-37334322334861000267687630789),(-37334322334861000205197834591)⟩,⟨(-13459789490746292979947454168),(-13459789490746292918106946489)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-42651975941651769773373090578),(-42651975941651769695959238329)⟩,⟨27491512743930856204852139,27491512743930931861460891⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-38517953391621921445876144023),(-38517953391621921359942060178)⟩,⟨15283381379848829288885122172,15283381379848829372434210411⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-25986826779131041551425302687),(-25986826779131041458791097656)⟩,⟨25828996921323524379300234116,25828996921323524470252760581⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-10474769196572679070899128450),(-10474769196572678959165185764)⟩,⟨28044133960250205324901962690,28044133960250205436095522830⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨2060638431524246320938986559,2060638431524246545540617979⟩,⟨22961693976269153693186395611,22961693976269153917840310577⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨8665887718305558663552004826,8665887718305559427832628855⟩,⟨14652345383400361624579851153,14652345383400362388996395159⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨9946057361021964657682188769,9946057361021967085372874127⟩,⟨7052326716940891321339123967,7052326716940893749051081886⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨8244099586938748043639915378,8244099586938755882287785519⟩,⟨2053009912866615656170746646,2053009912866623494758319011⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨5694822846061527928648340163,5694822846061544926183267221⟩,⟨(-364979914512290652049943658),(-364979914512273654576268146)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨3436487665607753279221275811,3436487665607777044399562682⟩,⟨(-1057827872888952357935729607),(-1057827872888928592789762677)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨1763222465621199190898320202,1763222465621220248934927774⟩,⟨(-866390721358062771169645991),(-866390721358041713143257891)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨535031875092998970157723220,535031875093007316757681088⟩,⟨(-318159606473993682740793324),(-318159606473985336142582197)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-27422601230747531087513987375),(-27422601230747204727851294927)⟩,⟨6859251716628407431312716761,6859251716628733789774157220⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-24633322160756871695566154255),(-24633322160756871682530163007)⟩,⟨14560444179076651073431782989,14560444179076651086021210683⟩⟩
noncomputable def realAnswer : RBox := ⟨(-52055923391504402783180141630),(-52055923391504076410281457934)⟩
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
open IntegerIntervals IntegerBasis IntegerGrid
namespace tm0_72_0
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
noncomputable def s4_0 : CBox := ⟨⟨1295231,1295247⟩,⟨(-2363654),(-2363638)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-411313),(-411296)⟩,⟨(-3367032),(-3367014)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-997739),(-997723)⟩,⟨(-211049),(-211031)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨7895,7911⟩,⟨115184,115202⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨3378,3396⟩,⟨(-4504),(-4487)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-103),(-87)⟩,⟨76,94⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-12),16⟩,⟨(-16),9⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-9198684761505121422620),(-9198684759818531705786)⟩,⟨(-2076692535130223741569),(-2076692533443634025533)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-14693578267679411962715),(-14693578263988662335495)⟩,⟨5646689915815815660782,5646689919506565286686⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-342042037768165614358),(-342042034559698577652)⟩,⟨8316027435210717582579,8316027438419184619824⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨2192345719735485200806,2192345721349895186019⟩,⟨(-193370651584068219065),(-193370649969658233955)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-212430535349152809028),(-212430534848154862960)⟩,⟨(-254554399000455495953),(-254554398499457549871)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨4429517684359930273,4429517778461302955⟩,⟨29966683957764631597,29966684051866004275⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨83909977776925943,83909988456523273⟩,⟨(-1767487350440248867),(-1767487339760651537)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨2762647627852805,2762648387099918⟩,⟨71235637180839416,71235637940086530⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-655995450256161),(-655995414432857)⟩,⟨(-2096822699963296),(-2096822664139992)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨34110648007974,34110649238259⟩,⟨47865319917759,47865321148046⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-1180417593550),(-1180417557650)⟩,⟨(-1048763419636),(-1048763383736)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨36781792749,36781793851⟩,⟨33725977238,33725978344⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-890244981),(-890244923)⟩,⟨(-1979795778),(-1979795720)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-72977286),(-72977268)⟩,⟨129522602,129522620⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨14694796,14694812⟩,⟨8612843,8612859⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨2320830,2320846⟩,⟨(-652798),(-652782)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-3708312385880997709728),(-3708312384079865772669)⟩,⟨1911061357930337562613,1911061359731469499396⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-13822341039367606862254),(-13822341039367606341044)⟩,⟨34827988692917066370919,34827988692917066892158⟩⟩
noncomputable def realAnswer : RBox := ⟨(-17530653425248704571982),(-17530653423447372113713)⟩
end tm0_72_0

namespace tm0_72_1
noncomputable def s0_0 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-75),75⟩,⟨(-75),75⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-88),88⟩,⟨(-88),88⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-89),89⟩,⟨(-89),89⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-74),74⟩,⟨(-74),74⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-47),47⟩,⟨(-47),47⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-21),21⟩,⟨(-21),21⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-28),28⟩,⟨(-28),28⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-38),38⟩,⟨(-38),38⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-65),65⟩,⟨(-65),65⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-79),79⟩,⟨(-79),79⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-45),45⟩,⟨(-45),45⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-31),31⟩,⟨(-31),31⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-27),27⟩,⟨(-27),27⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-10577253),(-10577236)⟩,⟨(-3622363),(-3622347)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-13490026),(-13490008)⟩,⟨4104063,4104080⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-127780),(-127761)⟩,⟨4255598,4255620⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨469726,469747⟩,⟨(-121739),(-121718)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-21480),(-21457)⟩,⟨(-10445),(-10424)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨429,454⟩,⟨315,340⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-20),10⟩,⟨(-18),12⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-5757129175932318466124),(-5757129169518589170511)⟩,⟨33628145756265465943376,33628145762679195242193⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨23345560841915551179973,23345560856007566695589⟩,⟨52067576177064778080065,52067576191156793600145⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨30284166462909826919548,30284166475258017198871⟩,⟨(-533280165672748393974),(-533280153324558116743)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-1224287846409035793032),(-1224287840123680428415)⟩,⟨(-7962435530035702638807),(-7962435523750347273780)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-880226105279891004098),(-880226103300359421569)⟩,⟨849095265846538029234,849095267826069611712⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨109910179471244323729,109910179849608842217⟩,⟨(-25431036981937528348),(-25431036603573009862)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-6657640038639830598),(-6657639994844945858)⟩,⟨286398534891944382,286398578686829122⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨269168376067580018,269168379248145183⟩,⟨(-37912026767172708),(-37912023586607541)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-7765582300023720),(-7765582146589089)⟩,⟨3428209872661111,3428210026095741⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨169468296897855,169468302285881⟩,⟨(-155757459693516),(-155757454305489)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-3491192228816),(-3491192068210)⟩,⟨5203325917797,5203326078403⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨112570994267,112570999254⟩,⟨(-165935702055),(-165935697065)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-7388243956),(-7388243753)⟩,⟨4817284794,4817285001⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨572560789,572560819⟩,⟨209360524,209360554⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨24938381,24938401⟩,⟨(-65739159),(-65739141)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-4292337),(-4292321)⟩,⟨(-9017097),(-9017080)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨7645266380918893627128,7645266387842947127158⟩,⟨13003987038414879656386,13003987045338933157407⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨128360241379701749678839,128360241379701751659335⟩,⟨43373065157479536488539,43373065157479538468704⟩⟩
noncomputable def realAnswer : RBox := ⟨136005507760620543305967,136005507767544798786493⟩
end tm0_72_1

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
open IntegerIntervals IntegerBasis IntegerGrid
namespace tm0_73_0
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
noncomputable def s4_0 : CBox := ⟨⟨571340,571356⟩,⟨1199590,1199606⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨1453505,1453523⟩,⟨787539,787556⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨352846,352862⟩,⟨(-334352),(-334335)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-46437),(-46420)⟩,⟨(-26164),(-26148)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨901,919⟩,⟨2310,2326⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-20),(-3)⟩,⟨(-60),(-42)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨7558960863352082627881,7558960865228678888114⟩,⟨(-1924311541028714816245),(-1924311539152118556759)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨8573798738661384095609,8573798742747386253986⟩,⟨(-9659588596337543995484),(-9659588592251541837231)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-2925020467271646737685),(-2925020463755460343642)⟩,⟨(-6052992982775412250189),(-6052992979259225855667)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-1435156817773920852012),(-1435156816031916524813)⟩,⟨979923916430699583311,979923918172703910412⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨239952171127113989115,239952171656378609162⟩,⟨84282710169241971056,84282710698506591101⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-14751448745280418200),(-14751448648520486887)⟩,⟨(-16915554093091947456),(-16915553996332016140)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨670595854003119074,670595864627330421⟩,⟨1066104720482063354,1066104731106274701⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-30901340838016554),(-30901340111543381)⟩,⟨(-37394359779901426),(-37394359053428252)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨1198762806419742,1198762839216853⟩,⟨768377371866315,768377404663426⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-35425660594410),(-35425659520923)⟩,⟨(-7450422706055),(-7450421632564)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨922218616983,922218646775⟩,⟨(-59019747685),(-59019717898)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-27699101463),(-27699100584)⟩,⟨2544639658,2544640534⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨1114620689,1114620737⟩,⟨315208685,315208734⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-29243932),(-29243914)⟩,⟨(-70758589),(-70758572)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-7886504),(-7886488)⟩,⟨3319033,3319049⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-416456),(-416440)⟩,⟨1120942,1120958⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨1999737316349273758802,1999737318325640138735⟩,⟨(-2764762096067232453851),(-2764762094090866074001)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-2841479601468849682914),(-2841479601468849274690)⟩,⟨(-30925463166807230209448),(-30925463166807229800812)⟩⟩
noncomputable def realAnswer : RBox := ⟨(-841742285119675924112),(-841742283143109135955)⟩
end tm0_73_0

namespace tm0_73_1
noncomputable def s0_0 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-75),75⟩,⟨(-75),75⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-88),88⟩,⟨(-88),88⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-89),89⟩,⟨(-89),89⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-74),74⟩,⟨(-74),74⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-47),47⟩,⟨(-47),47⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-21),21⟩,⟨(-21),21⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-28),28⟩,⟨(-28),28⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-38),38⟩,⟨(-38),38⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-65),65⟩,⟨(-65),65⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-79),79⟩,⟨(-79),79⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-45),45⟩,⟨(-45),45⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-31),31⟩,⟨(-31),31⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-27),27⟩,⟨(-27),27⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨4499093,4499109⟩,⟨(-3183783),(-3183767)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨2179727,2179744⟩,⟨(-6517130),(-6517112)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-1635092),(-1635069)⟩,⟨(-1201981),(-1201959)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-72162),(-72138)⟩,⟨211997,212022⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨8892,8916⟩,⟨(-5691),(-5668)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-223),(-198)⟩,⟨80,108⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-13),17⟩,⟨(-16),15⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-8386938700844131050144),(-8386938693707852051602)⟩,⟨(-26944618400270335745582),(-26944618393134056744497)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-36659650469378649569019),(-36659650453777546629122)⟩,⟨(-29122415881673625824244),(-29122415866072522884316)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-21364794397397177032248),(-21364794383864843025506)⟩,⟨11918584724875352843970,11918584738407686849070⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨3918312134777222786450,3918312141559196150958⟩,⟨5010658637956531470120,5010658644738504834954⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨246468823482557299254,246468825573708667228⟩,⟨(-905150554229525830278),(-905150552138374462302)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-58367154144912891973),(-58367153755875162032)⟩,⟨59827289029244755874,59827289418282485811⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨3770442017254209625,3770442060819795201⟩,⟨(-2877387601224723815),(-2877387557659138236)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-129958601248215333),(-129958598205109155)⟩,⟨131612217591932957,131612220635039137⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨2430106146274990,2430106286740336⟩,⟨(-4935381119325902),(-4935380978860554)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-11786254957717),(-11786250256637)⟩,⟨141270341523111,141270346224195⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-726022009886),(-726021876634)⟩,⟨(-3594418288225),(-3594418154976)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨26302891874,26302895819⟩,⟨108623123341,108623127284⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨565279975,565280139⟩,⟨(-4672222059),(-4672221900)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-266923649),(-266923624)⟩,⟨165289692,165289718⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨18938203,18938223⟩,⟨29813592,29813609⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨4868259,4868277⟩,⟨914155,914171⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-10383554477078097520638),(-10383554469481658785840)⟩,⟨(-6664310792882841832088),(-6664310785286403097080)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-111139098596270976696305),(-111139098596270975143689)⟩,⟨16067634772152142308198,16067634772152143859094⟩⟩
noncomputable def realAnswer : RBox := ⟨(-121522653073349174216943),(-121522653065752533929529)⟩
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
open IntegerIntervals IntegerBasis IntegerGrid
namespace tm0_75_0
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
noncomputable def s4_0 : CBox := ⟨⟨232880,232896⟩,⟨(-223700),(-223684)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨63353,63370⟩,⟨(-387543),(-387527)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-99496),(-99480)⟩,⟨(-48013),(-47997)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-1206),(-1190)⟩,⟨11283,11300⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨317,333⟩,⟨(-372),(-355)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-13),5⟩,⟨(-4),18⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨1973915910605378560372,1973915912928620239833⟩,⟨(-4957955237811986049127),(-4957955235488744369350)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-1982085842908620181817),(-1982085837900515128428)⟩,⟨(-8466431118560300043045),(-8466431113552194988851)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-4344200465577455457078),(-4344200461354273959447)⟩,⟨(-604847468802777906400),(-604847464579596409015)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨54348945036821596201,54348947065242368027⟩,⟨1082246580291680660647,1082246582320101432517⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨110854113058122920164,110854113648879615234⟩,⟨(-100595482507153402344),(-100595481916396707282)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-11823761421255064902),(-11823761318929772891)⟩,⟨3486541827281680683,3486541929606972691⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨624700645296171765,624700655813223770⟩,⟨(-131934767290441321),(-131934756773389310)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-20494501353366650),(-20494500688051572)⟩,⟨9230868622426334,9230869287741414⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨406150106385220,406150133884758⟩,⟨(-439563734121692),(-439563706622154)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-3925156691887),(-3925155874292)⟩,⟨13169267142472,13169267960069⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-23236612029),(-23236591507)⟩,⟨(-315856575552),(-315856555031)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨1614668618,1614669170⟩,⟨8494274555,8494275111⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨33431952,33431983⟩,⟨(-328238673),(-328238639)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-16400594),(-16400578)⟩,⟨11979778,11979794⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨1365213,1365229⟩,⟨1673014,1673030⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨293887,293903⟩,⟨13146,13162⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-699731082143286364488),(-699731079762079414946)⟩,⟨(-2174036552694011262845),(-2174036550312804313149)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-18293810212045280749424),(-18293810212045280286320)⟩,⟨(-10973444139838731576033),(-10973444139838731112853)⟩⟩
noncomputable def realAnswer : RBox := ⟨(-18993541294188667113912),(-18993541291807259701266)⟩
end tm0_75_0

namespace tm0_75_1
noncomputable def s0_0 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-75),75⟩,⟨(-75),75⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-88),88⟩,⟨(-88),88⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-89),89⟩,⟨(-89),89⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-74),74⟩,⟨(-74),74⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-47),47⟩,⟨(-47),47⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-21),21⟩,⟨(-21),21⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-28),28⟩,⟨(-28),28⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-38),38⟩,⟨(-38),38⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-65),65⟩,⟨(-65),65⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-79),79⟩,⟨(-79),79⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-45),45⟩,⟨(-45),45⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-31),31⟩,⟨(-31),31⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-27),27⟩,⟨(-27),27⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-1079033),(-1079017)⟩,⟨(-793690),(-793674)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-1632188),(-1632171)⟩,⟨19098,19119⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-123525),(-123505)⟩,⟨444279,444301⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨47558,47583⟩,⟨(-3792),(-3769)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-1792),(-1771)⟩,⟨(-1062),(-1041)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨21,47⟩,⟨13,36⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-18287225492286508678565),(-18287225483451744571895)⟩,⟨(-6190616075790599468062),(-6190616066955835362717)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-30252232237817942154997),(-30252232218696241801958)⟩,⟨8849097640826374294735,8849097659948074644914⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-1269690138197860506960),(-1269690121944964410325)⟩,⟨15910234274156201559110,15910234290409097656710⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨3939988529425425294255,3939988537322143885112⟩,⟨(-454034299251881394882),(-454034291355162804218)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-399436547451682295248),(-399436545117720934271)⟩,⟨(-381162270981848758864),(-381162268647887397864)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨16481417463886558078,16481417875266348664⟩,⟨42841492296893176226,42841492708272966815⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-706850512201775108),(-706850469079853454)⟩,⟨(-2297962020611690466),(-2297961977489768813)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨42892559320348457,42892562106972463⟩,⟨74190976585191691,74190979371815698⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-1863386759996923),(-1863386642233206)⟩,⟨(-1368795163038033),(-1368795045274316)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨53072145507555,53072149087625⟩,⟨8876867473502,8876871053571⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-1229402185608),(-1229402093849)⟩,⟨260408915756,260409007517⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨32821637286,32821639751⟩,⟨(-11379477246),(-11379474780)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-1338513579),(-1338513476)⟩,⟨71876245,71876345⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨59355773,59355797⟩,⟨58415039,58415063⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨5869330,5869350⟩,⟨(-6708188),(-6708172)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-152378),(-152361)⟩,⟨(-1209056),(-1209039)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-7708796706388339080053),(-7708796697238764032024)⟩,⟨2962355938423661469938,2962355947573236517402⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-36190302421083106259859),(-36190302421083104500199)⟩,⟨68119945432219250083750,68119945432219251843229⟩⟩
noncomputable def realAnswer : RBox := ⟨(-43899099127471545339912),(-43899099118321768532223)⟩
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
open IntegerIntervals IntegerBasis IntegerGrid
namespace tm0_76_0
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
noncomputable def s4_0 : CBox := ⟨⟨22244,22260⟩,⟨157617,157634⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨136011,136029⟩,⟨134628,134644⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨45772,45788⟩,⟨(-26042),(-26026)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-4061),(-4044)⟩,⟨(-3335),(-3319)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨54,71⟩,⟨198,216⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-14),6⟩,⟨(-17),7⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨407329925826217020579,407329928411193143295⟩,⟨4395135022587111011248,4395135025172087134449⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨4639085154346052125262,4639085159890576028712⟩,⟨5420488271218923318604,5420488276763447222293⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨3324773362598746868668,3324773367227172401930⟩,⟨(-1223871103849790801587),(-1223871099221365268586)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-455246414367018078938),(-455246412178090404622)⟩,⟨(-724600024568646501029),(-724600022379718826670)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-33586032298694006812),(-33586031674517597485)⟩,⟨109842881270499536895,109842881894675946223⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨5984556227376275201,5984556332613762653⟩,⟨(-6905549414138133899),(-6905549308900646448)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-311332572811909792),(-311332562346677506)⟩,⟨331449126050976709,331449136516208996⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨7284915323861771,7284915960654026⟩,⟨(-13460701495465244),(-13460700858672987)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-18852109918254),(-18852084733134)⟩,⟨387677143897793,387677169082914⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-3717482887160),(-3717482173510)⟩,⟨(-7609909041209),(-7609908327560)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨140971121440,140971138474⟩,⟨120519939356,120519956390⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-4111779304),(-4111778866)⟩,⟨(-2518694115),(-2518693677)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨122699447,122699477⟩,⟨126342314,126342344⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨367937,367956⟩,⟨(-10454888),(-10454869)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-1083853),(-1083837)⟩,⟨45559,45575⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-91152),(-91136)⟩,⟨113945,113962⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨1314672747040430130641,1314672749654995976289⟩,⟨1328401310975644392050,1328401313590210237783⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨17636131227012663419635,17636131227012663686825⟩,⟨1252002633818136476539,1252002633818136743569⟩⟩
noncomputable def realAnswer : RBox := ⟨18950803974052993550276,18950803976667759663114⟩
end tm0_76_0

namespace tm0_76_1
noncomputable def s0_0 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-75),75⟩,⟨(-75),75⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-88),88⟩,⟨(-88),88⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-89),89⟩,⟨(-89),89⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-74),74⟩,⟨(-74),74⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-47),47⟩,⟨(-47),47⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-21),21⟩,⟨(-21),21⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-28),28⟩,⟨(-28),28⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-38),38⟩,⟨(-38),38⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-65),65⟩,⟨(-65),65⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-79),79⟩,⟨(-79),79⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-45),45⟩,⟨(-45),45⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-31),31⟩,⟨(-31),31⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-27),27⟩,⟨(-27),27⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨628537,628555⟩,⟨(-202444),(-202428)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨453460,453478⟩,⟨(-653663),(-653643)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-140878),(-140856)⟩,⟨(-168795),(-168769)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-10623),(-10603)⟩,⟨19295,19319⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨798,823⟩,⟨(-439),(-418)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-32),(-1)⟩,⟨(-7),21⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨15801873190212722350208,15801873200042798907952⟩,⟨(-2305775267664561315096),(-2305775257834484759067)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨18701642057545346719856,18701642078715086645995⟩,⟨(-17863437550417128257728),(-17863437529247388332233)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-5155676405243796947998),(-5155676387431521651380)⟩,⟨(-11816330229389473767287),(-11816330211577198469742)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-2538998251664478738452),(-2538998243143078995457)⟩,⟨1833749346623476433939,1833749355144876176770⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨412968223011025416558,412968225476943508819⟩,⟨94465778254336349310,94465780720254441573⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-27421039089414684195),(-27421038666344427060)⟩,⟨(-20144968918884386787),(-20144968495814129653)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨1348586342802310169,1348586385709674971⟩,⟨1055072438918540848,1055072481825905652⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-53856390587999456),(-53856387920981827)⟩,⟨(-22460981893893825),(-22460979226876197)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨1496404771618232,1496404879464914⟩,⟨(-95462624121284),(-95462516274600)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-27770529729028),(-27770526604276)⟩,⟨18127006239237,18127009363988⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨398410646056,398410722216⟩,⟨(-618715998676),(-618715922517)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-7610689774),(-7610687822)⟩,⟨17814497628,17814499580⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨430096976,430097061⟩,⟨(-571796275),(-571796195)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-42547640),(-42547617)⟩,⟨5446903,5446927⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨931567,931586⟩,⟨4379812,4379832⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨529110,529126⟩,⟨292185,292203⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨4532613995624841701787,4532614005669535920221⟩,⟨(-5012740059665382060980),(-5012740049620687842812)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨1209418598908788263987,1209418598908789278441⟩,⟨(-63919621814845739283477),(-63919621814845738268294)⟩⟩
noncomputable def realAnswer : RBox := ⟨5742032594533529965774,5742032604578425198662⟩
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
open IntegerIntervals IntegerBasis IntegerGrid
namespace tm0_79_0
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
noncomputable def s4_0 : CBox := ⟨⟨(-3123),(-3107)⟩,⟨18809,18825⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨10739,10756⟩,⟨19371,19387⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨5488,5505⟩,⟨(-1555),(-1539)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-346),(-329)⟩,⟨(-401),(-384)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-4),13⟩,⟨8,25⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-2492626783664266158153),(-2492626780103491696186)⟩,⟨(-160939078561074218320),(-160939075000299756620)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-3316691118753528221126),(-3316691111229500633462)⟩,⟨2128942452748717840811,2128942460272745428260⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨470465469813642864607,470465475906937991270⟩,⟨1807109284123708519030,1807109290217003645829⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨365482772411917917585,365482775163148115224⟩,⟨(-210137514414920584086),(-210137511663690386468)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-50222978921153001728),(-50222978184732935124)⟩,⟨(-13196015970214663327),(-13196015233794596723)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨3125352051042260127,3125352165568683421⟩,⟨2028603467320896144,2028603581847319439⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-144357846088904359),(-144357835772358459)⟩,⟨(-78847994468056930),(-78847984151511031)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨4808036784119181,4808037342807270⟩,⟨544339026102412,544339584790498⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-94417463203741),(-94417443844535)⟩,⟨48215427372594,48215446731804⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨873173729797,873174204727⟩,⟨(-1783058614046),(-1783058139115)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨3403030746,3403040501⟩,⟨37135390086,37135399839⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-309756597),(-309756373)⟩,⟨(-777735314),(-777735088)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨6510797,6510818⟩,⟨26002675,26002698⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨638782,638800⟩,⟨(-1279520),(-1279503)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-130805),(-130789)⟩,⟨(-42583),(-42567)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-14927),(-14911)⟩,⟨9707,9723⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-836767821735473051379),(-836767818270278227293)⟩,⟨592288245701141162392,592288249166335986417⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-2327771549836925009187),(-2327771549836924684758)⟩,⟨9792943020838484907830,9792943020838485232307⟩⟩
noncomputable def realAnswer : RBox := ⟨(-3164539371572498060566),(-3164539368107102912051)⟩
end tm0_79_0

namespace tm0_79_1
noncomputable def s0_0 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-75),75⟩,⟨(-75),75⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-88),88⟩,⟨(-88),88⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-89),89⟩,⟨(-89),89⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-74),74⟩,⟨(-74),74⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-47),47⟩,⟨(-47),47⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-21),21⟩,⟨(-21),21⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-28),28⟩,⟨(-28),28⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-38),38⟩,⟨(-38),38⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-65),65⟩,⟨(-65),65⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-79),79⟩,⟨(-79),79⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-45),45⟩,⟨(-45),45⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-31),31⟩,⟨(-31),31⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-27),27⟩,⟨(-27),27⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨79104,79121⟩,⟨(-583),(-567)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨71605,71623⟩,⟨(-57940),(-57924)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-10447),(-10425)⟩,⟨(-21432),(-21412)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-1372),(-1349)⟩,⟨1679,1701⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨63,84⟩,⟨(-43),(-20)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-108389780449583618337),(-108389766908786830702)⟩,⟨9036131807507931284921,9036131821048728073553⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨8361644973038173682506,8361645001765565656259⟩,⟨11583314783669925533823,11583314812397317508254⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨6463754446556350737162,6463754470005315983648⟩,⟨(-2094656726549751964244),(-2094656703100786718258)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-853635269574113427030),(-853635258864363375141)⟩,⟨(-1285163209748645984880),(-1285163199038895932910)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-35256317437700173756),(-35256314528617143700)⟩,⟨188222786640507634158,188222789549590664215⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨6594589840530108272,6594590300886941355⟩,⟨(-12204652060504937877),(-12204651600148104793)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-246774131886120518),(-246774089594432052)⟩,⟨568011461213732021,568011503505420490⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨220578484000707,220580823539672⟩,⟨(-18444948106988974),(-18444945767450011)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨225896216588061,225896299474233⟩,⟨341596026074624,341596108960794⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-7349892509364),(-7349890430194)⟩,⟨(-2531030142621),(-2531028063446)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨144172353319,144172396900⟩,⟨(-33223945969),(-33223902386)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-2910467658),(-2910466683)⟩,⟨1684873268,1684874243⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨100276970,100277014⟩,⟨(-42443682),(-42443635)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-5600628),(-5600608)⟩,⟨(-1735971),(-1735950)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-83239),(-83222)⟩,⟨561619,561635⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨50120,50136⟩,⟨54098,54115⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨2305744384517989322133,2305744397824832683118⟩,⟨2902699115834330253875,2902699129141173615072⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨35799665714138135810233,35799665714138137042970⟩,⟨6566789921765459153151,6566789921765460385640⟩⟩
noncomputable def realAnswer : RBox := ⟨38105410098656025132366,38105410111963069726088⟩
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
open IntegerIntervals IntegerBasis IntegerGrid
namespace tm0_81_0
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
noncomputable def s4_0 : CBox := ⟨⟨4571,4587⟩,⟨(-733),(-717)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨3504,3520⟩,⟨(-3930),(-3914)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-783),(-766)⟩,⟨(-1052),(-1035)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-58),(-40)⟩,⟨92,109⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-9),16⟩,⟨(-16),5⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-1091304785038573923080),(-1091304780630275381972)⟩,⟨1315053194208939967740,1315053198617238508855⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-118183562882052740531),(-118183553659471834320)⟩,⟨2650737932802335697417,2650737942024916603858⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨1150959211639134415006,1150959218958891960704⟩,⟨400143022301643770831,400143029621401316489⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨7480204052707674429,7480207257400987533⟩,⟨(-262940956702893388970),(-262940953498200075855)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-20965817409420225170),(-20965816586978040157)⟩,⟨22295592645508173699,22295593467950358706⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨1733979166865325130,1733979288075190019⟩,⟨(-1094579355092115686),(-1094579233882250794)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-63049048397233458),(-63049038174380151)⟩,⟨54882301321822042,54882311544675355⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨836198841873174,836199354139949⟩,⟨(-2086646999754181),(-2086646487487403)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨13006750667215,13006766920851⟩,⟨42743312220779,42743328474415⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-648628119537),(-648627757319)⟩,⟨(-387585305124),(-387584942905)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨12747362728,12747369459⟩,⟨(-1277638954),(-1277632222)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-231999327),(-231999179)⟩,⟨119026190,119026338⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨6987038,6987060⟩,⟨(-3104652),(-3104633)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-370047),(-370029)⟩,⟨(-84742),(-84726)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-1017),(-1001)⟩,⟨34697,34714⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨3389,3405⟩,⟨2754,2770⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-11723828491708383008),(-11723824306752699437)⟩,⟨687374507318221552831,687374511503177236437⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨4483347198605065443239,4483347198605065538163⟩,⟨5263800347519736291722,5263800347519736386728⟩⟩
noncomputable def realAnswer : RBox := ⟨4471623370113257060231,4471623374298412838726⟩
end tm0_81_0

namespace tm0_81_1
noncomputable def s0_0 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-75),75⟩,⟨(-75),75⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-88),88⟩,⟨(-88),88⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-89),89⟩,⟨(-89),89⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-74),74⟩,⟨(-74),74⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-47),47⟩,⟨(-47),47⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-21),21⟩,⟨(-21),21⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-28),28⟩,⟨(-28),28⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-38),38⟩,⟨(-38),38⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-65),65⟩,⟨(-65),65⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-79),79⟩,⟨(-79),79⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-45),45⟩,⟨(-45),45⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-31),31⟩,⟨(-31),31⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-27),27⟩,⟨(-27),27⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-6202),(-6183)⟩,⟨(-18209),(-18193)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-18589),(-18569)⟩,⟨(-11572),(-11554)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-3728),(-3707)⟩,⟨3933,3952⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨435,458⟩,⟨113,136⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-24),(-1)⟩,⟨(-26),3⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨4958250532972744361785,4958250549736462328515⟩,⟨3693179840058605470440,3693179856822323437087⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨9617361006005960883837,9617361041218283393940⟩,⟨(-96625396997173843212),(-96625361784851333973)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨1207797140418865753989,1207797168587022589195⟩,⟨(-4266012552429317916535),(-4266012524261161081163)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-961961266917717832934),(-961961254443281966717)⟩,⟨34682877437014018476,34682889911449884656⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨87542973324096808224,87542976572792093020⟩,⟨71221075885416818817,71221079134112103618⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-4579349259091995589),(-4579348771909118021)⟩,⟨(-6107926376691111578),(-6107925889508234004)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨227113254884242313,227113296787928797⟩,⟨217843995696616329,217844037600302815⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-8234431073923674),(-8234428928992184)⟩,⟨(-2372063779277044),(-2372061634345556)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨158456263725952,158456333308591⟩,⟨(-68385600132875),(-68385530550241)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-1192724227233),(-1192722641659)⟩,⟨2707259608997,2707261194567⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-11829996224),(-11829966166)⟩,⟨(-49429906569),(-49429876512)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨608326375,608326990⟩,⟨852660240,852660853⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-16841483),(-16841446)⟩,⟨(-26094110),(-26094074)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-97456),(-97432)⟩,⟨1553306,1553325⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨141926,141942⟩,⟨(-19789),(-19772)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨8892,8908⟩,⟨(-15825),(-15809)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨2484105012103494884642,2484105028169933411836⟩,⟨(-94907779369528599906),(-94907763303090072849)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨18165866976269702724853,18165866976269703085820⟩,⟨(-17177884920367915669242),(-17177884920367915308568)⟩⟩
noncomputable def realAnswer : RBox := ⟨20649971988373097609495,20649972004439736497656⟩
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
open IntegerIntervals IntegerBasis IntegerGrid
namespace tm0_84_0
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
noncomputable def s4_0 : CBox := ⟨⟨542,558⟩,⟨74,91⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨509,526⟩,⟨(-331),(-314)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-60),(-44)⟩,⟨(-141),(-124)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-12),4⟩,⟨(-1),18⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-638511344105252751465),(-638511338032820710663)⟩,⟨(-726273103240884177988),(-726273097168452137165)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-1441507082230961550348),(-1441507069714757978632)⟩,⟨(-265519690988839440894),(-265519678472635869286)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-269897521080984939663),(-269897511442449571843)⟩,⟨582957658611223078476,582957668249758446305⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨129389596923500180202,129389600953165017983⟩,⟨8969444902533242159,8969448932198079938⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-10449129479197768052),(-10449128508185737029)⟩,⟨(-9105589144681552742),(-9105588173669521719)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨539800927008102788,539801059045141398⟩,⟨641292661062571938,641292793099610547⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-25001037417083008),(-25001027327024006)⟩,⟨(-17165648278858021),(-17165638188799018)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨712922216641157,712922666727323⟩,⟨(-866919902814),(-866469816649)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-8393559751701),(-8393547238043)⟩,⟨8911752275652,8911764789310⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-21547519905),(-21547278447)⟩,⟨(-176364690408),(-176364448952)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨2019770600,2019774466⟩,⟨1610741068,1610744936⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-44733021),(-44732939)⟩,⟨(-7655235),(-7655154)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨1158830,1158850⟩,⟨126572,126591⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-41223),(-41207)⟩,⟨(-31615),(-31599)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-1668),(-1652)⟩,⟨4071,4087⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨280,296⟩,⟨440,456⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-371743329262370047741),(-371743323700630415312)⟩,⟨(-68057857496299045162),(-68057851934559412745)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-3370225554467598988100),(-3370225554467598930325)⟩,⟨2033993157263886800556,2033993157263886858269⟩⟩
noncomputable def realAnswer : RBox := ⟨(-3741968883730069035841),(-3741968878168129345637)⟩
end tm0_84_0

namespace tm0_84_1
noncomputable def s0_0 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-75),75⟩,⟨(-75),75⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-88),88⟩,⟨(-88),88⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-89),89⟩,⟨(-89),89⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-74),74⟩,⟨(-74),74⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-47),47⟩,⟨(-47),47⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-21),21⟩,⟨(-21),21⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-28),28⟩,⟨(-28),28⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-38),38⟩,⟨(-38),38⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-65),65⟩,⟨(-65),65⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-79),79⟩,⟨(-79),79⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-45),45⟩,⟨(-45),45⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-31),31⟩,⟨(-31),31⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-27),27⟩,⟨(-27),27⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-64),(-47)⟩,⟨(-2312),(-2294)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-1699),(-1680)⟩,⟨(-1897),(-1880)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-503),(-484)⟩,⟨307,329⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨30,53⟩,⟨9,31⟩⟩
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
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-2502754380441572876126),(-2502754357349580770892)⟩,⟨2444699533808177378062,2444699556900169483246⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-675837190957516667125),(-675837143170558647659)⟩,⟨5269753535192746528603,5269753582979704548493⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨2174943568437986266968,2174943605528104993370⟩,⟨855907605015870187603,855907642105988913949⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨2265354663738177329,2265370348451899823⟩,⟨(-474572152886321318186),(-474572137201607595672)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-30729764482488030731),(-30729760647285501812)⟩,⟨40830827121905792769,40830830957108321690⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨2218735456962582644,2218735987600667792⟩,⟨(-2194033450436041842),(-2194032919797956692)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-55918221905059316),(-55918180551371633)⟩,⟨99534504876786107,99534546230473787⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-275981569965900),(-275979685669516)⟩,⟨(-2703478920334665),(-2703477036038281)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨37826894074774,37826947638457⟩,⟨28375114113376,28375167677062⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-674820214204),(-674819157422)⟩,⟨168763048531,168764105310⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨5254368579,5254385813⟩,⟨(-8799015750),(-8798998516)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-4363438),(-4363121)⟩,⟨182235843,182236158⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-218358),(-218333)⟩,⟨(-4729785),(-4729757)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-100554),(-100536)⟩,⟨187687,187706⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨17732,17750⟩,⟨3937,3953⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨1628,1644⟩,⟨(-1501),(-1485)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-171658305728173668515),(-171658284384354365945)⟩,⟨1355753695727192469023,1355753717071011771649⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨7977640809357066180302,7977640809357066399588⟩,⟨11788042515999730231674,11788042515999730451188⟩⟩
noncomputable def realAnswer : RBox := ⟨7805982503628792511787,7805982524972812033643⟩
end tm0_84_1

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
open IntegerIntervals IntegerBasis IntegerGrid
namespace tm0_85_0
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
noncomputable def s4_0 : CBox := ⟨⟨(-199),(-183)⟩,⟨188,204⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-27),(-11)⟩,⟨288,304⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨59,75⟩,⟨6,22⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-14),3⟩,⟨(-16),5⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-16),16⟩,⟨(-15),16⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨743309218912913215475,743309225669495174120⟩,⟨295450104484673066517,295450111241255025109⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨1150545157875340219222,1150545171732807530778⟩,⟨(-350276370046047607956),(-350276356188580296507)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-29499243945463654180),(-29499233380650323515)⟩,⟨(-518137711880487613016),(-518137701315674282316)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-92690752031582042869),(-92690747681930730751)⟩,⟨43703646486693238391,43703650836344550504⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨10472421631117939483,10472422657487777160⟩,⟨1914475303066801906,1914476329436639585⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-594118427917073496),(-594118292042937877)⟩,⟨(-185208018109118219),(-185207882234982601)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨21637624631653277,21637634679436284⟩,⟨(-131390447512622),(-131380399729615)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-386550866763172),(-386550435598848)⟩,⟨295185411079640,295185842243964⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨466051681593,466063153011⟩,⟨(-7940926809594),(-7940915338178)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨83509836954,83510047924⟩,⟨71148368518,71148579488⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-1505275933),(-1505272720)⟩,⟨175677936,175681148⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨19976439,19976510⟩,⟨(-15601734),(-15601665)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-450419),(-450397)⟩,⟨430289,430307⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨25929,25947⟩,⟨(-6627),(-6611)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-1149),(-1133)⟩,⟨(-1903),(-1887)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-271),(-255)⟩,⟨(-26),(-8)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨296927322606041547578,296927328722916301225⟩,⟨(-87921817957477601544),(-87921811840602847919)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨1728476507573334928186,1728476507573334986496⟩,⟨(-2767033153932412027112),(-2767033153932411968815)⟩⟩
noncomputable def realAnswer : RBox := ⟨2025403830179276475764,2025403836296351287721⟩
end tm0_85_0

namespace tm0_85_1
noncomputable def s0_0 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-75),75⟩,⟨(-75),75⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-88),88⟩,⟨(-88),88⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-89),89⟩,⟨(-89),89⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-74),74⟩,⟨(-74),74⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-47),47⟩,⟨(-47),47⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-21),21⟩,⟨(-21),21⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-28),28⟩,⟨(-28),28⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-38),38⟩,⟨(-38),38⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-65),65⟩,⟨(-65),65⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-79),79⟩,⟨(-79),79⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-45),45⟩,⟨(-45),45⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-31),31⟩,⟨(-31),31⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-27),27⟩,⟨(-27),27⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨928,944⟩,⟨634,650⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨1218,1238⟩,⟨(-147),(-125)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-1),19⟩,⟨(-291),(-272)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-31),(-6)⟩,⟨0,22⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨926353888313111295940,926353914006748235296⟩,⟨(-2741554983027620457488),(-2741554957333983517931)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-1495338068618540906437),(-1495338015710848279870)⟩,⟨(-4094835529214085142184),(-4094835476306392515251)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-1875596641358251247043),(-1875596600704168479267)⟩,⟨217687243566977541858,217687284221060309504⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨181410528855885216514,181410545785740235828⟩,⟨328150857408355524644,328150874338210543980⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨4278364349226065739,4278368402952069726⟩,⟨(-39017496573133424887),(-39017492519407420900)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-510300832302655011),(-510300286265077175)⟩,⟨2259609808752802929,2259610354790380766⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-7794941594889032),(-7794900416316540)⟩,⟨(-81081800021297189),(-81081758842724697)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨1267280347979567,1267282152972914⟩,⟨1353153011735235,1353154816728584⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-30681477124633),(-30681428024536)⟩,⟨1633934639283,1633983739381⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨236167751443,236168674742⟩,⟨(-358746166340),(-358745243038)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨1493310811,1493325132⟩,⟨5823479340,5823493663⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-73637109),(-73636859)⟩,⟨(-70302109),(-70301855)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨2008974,2009000⟩,⟨1537788,1537816⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-43970),(-43951)⟩,⟨(-100551),(-100531)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-6939),(-6919)⟩,⟨5939,5957⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨112,129⟩,⟨1083,1099⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-376568131232667813620),(-376568107761323722900)⟩,⟨(-1054565004232803270869),(-1054564980761459180070)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-10316390599694709864337),(-10316390599694709642834)⟩,⟨(-5721998580006887173062),(-5721998580006886951526)⟩⟩
noncomputable def realAnswer : RBox := ⟨(-10692958730927477677957),(-10692958707455933365734)⟩
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
open IntegerIntervals IntegerBasis IntegerGrid
namespace tm0_87_0
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
noncomputable def s4_0 : CBox := ⟨⟨52,68⟩,⟨21,37⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨61,77⟩,⟨(-28),(-11)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-12),4⟩,⟨(-25),(-8)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-16),10⟩,⟨(-6),16⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨462416785448670793439,462416793813490178799⟩,⟨(-292641174893752306640),(-292641166528932921306)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨254691434641138276178,254691451627999563902⟩,⟨(-768616733534297297611),(-768616716547436009840)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-291709085429377933866),(-291709072735850080087)⟩,⟨(-172167350168015431588),(-172167337474487577809)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-7082620738993767907),(-7082615670693667245)⟩,⟨63592318111762872317,63592323180062972977⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨3950872656096853161,3950873802985244247⟩,⟨(-4885897321459518949),(-4885896174571127864)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-230232998317065097),(-230232854403968894)⟩,⟨254488316773213757,254488460686309959⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨3773213426759509,3773223392864229⟩,⟨(-10355677708871629),(-10355667742766912)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨84681650876117,84682046657558⟩,⟨210072639674988,210073035456426⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-3267322430154),(-3267312787161)⟩,⟨(-785127966381),(-785118323389)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨29710295121,29710456230⟩,⟨(-29475911814),(-29475750705)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨64554804,64557030⟩,⟨517796543,517798767⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-5433175),(-5433129)⟩,⟨(-5749402),(-5749353)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨143070,143088⟩,⟨105753,105772⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-3335),(-3317)⟩,⟨(-6292),(-6276)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-385),(-369)⟩,⟨404,420⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨9,25⟩,⟨55,71⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨70340168039456986058,70340175441903954382⟩,⟨(-195745749318024899626),(-195745741915577931300)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-832314917265454803184),(-832314917265454764158)⟩,⟨(-2080787293163636977518),(-2080787293163636938449)⟩⟩
noncomputable def realAnswer : RBox := ⟨(-761974749226097817126),(-761974741823450809776)⟩
end tm0_87_0

namespace tm0_87_1
noncomputable def s0_0 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-75),75⟩,⟨(-75),75⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-88),88⟩,⟨(-88),88⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-89),89⟩,⟨(-89),89⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-74),74⟩,⟨(-74),74⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-47),47⟩,⟨(-47),47⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-21),21⟩,⟨(-21),21⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-28),28⟩,⟨(-28),28⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-38),38⟩,⟨(-38),38⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-65),65⟩,⟨(-65),65⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-79),79⟩,⟨(-79),79⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-45),45⟩,⟨(-45),45⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-31),31⟩,⟨(-31),31⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-27),27⟩,⟨(-27),27⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨71,87⟩,⟨(-274),(-257)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-136),(-118)⟩,⟨(-273),(-257)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-72),(-50)⟩,⟨12,29⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-8),16⟩,⟨(-11),17⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-1145034627198216850228),(-1145034595388874134393)⟩,⟨(-1615111597805211518629),(-1615111565995868802712)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-2832168925552800284199),(-2832168860697647711203)⟩,⟨(-769741156815523767437),(-769741091960371194631)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-563068663259014976641),(-563068614414587783792)⟩,⟨1096183481986081852866,1096183530830509045730⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨233851648991790139068,233851668717990577293⟩,⟨10888094329299558217,10888114055499996438⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-19008003532210430307),(-19007999002760265863)⟩,⟨(-13241051454867855200),(-13241046925417690756)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨1012706276319258289,1012706854618459339⟩,⟨778539520041180740,778540098340381788⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-40097426548481335),(-40097385708266012)⟩,⟨(-10655558212010097),(-10655517371794777)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨764350083373299,764351740086661⟩,⟨(-401386152260144),(-401384495546784)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-1606473974656),(-1606432704507)⟩,⟨12879270762194,12879312032342⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-128827655680),(-128826950670)⟩,⟨(-101230584284),(-101229879273)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨2000989593,2000999489⟩,⟨(-529712515),(-529702618)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-19685361),(-19685195)⟩,⟨24937687,24937855⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨334765,334787⟩,⟨(-640402),(-640381)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-23229),(-23206)⟩,⟨17611,17629⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨1924,1942⟩,⟨1247,1267⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨238,255⟩,⟨(-119),(-103)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-720742533180653044561),(-720742504783084510396)⟩,⟨(-215042455734501673595),(-215042427336933139450)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-7357490532814996747934),(-7357490532814996599493)⟩,⟨3396227247582085810537,3396227247582085958815⟩⟩
noncomputable def realAnswer : RBox := ⟨(-8078233065995749792495),(-8078233037597981109889)⟩
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
open IntegerIntervals IntegerBasis IntegerGrid
namespace tm0_88_0
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
noncomputable def s4_0 : CBox := ⟨⟨(-38),(-22)⟩,⟨8,24⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-20),(-3)⟩,⟨26,43⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨0,16⟩,⟨(-8),10⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-15),16⟩,⟨(-16),10⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-230889396504214540930),(-230889387196957657286)⟩,⟨389322661868279435195,389322671175536318848⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨104296024477231234394,104296043284735596343⟩,⟨656154631921883546366,656154650729387908375⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨273408766363163254190,273408780277164966085⟩,⟨11739255510193407291,11739269424195119170⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-19624535641734406612),(-19624530170508925425)⟩,⟨(-46601454108024411987),(-46601448636798930800)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-694419412753650076),(-694418200317219476)⟩,⟨4777955836450768294,4777957048887198897⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨42305366710030856,42305514833010482⟩,⟨(-251372772023936052),(-251372623900956426)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨2008821236937151,2008831163604552⟩,⟨7607572363259488,7607582289926887⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-132867073915128),(-132866694670018)⟩,⟨(-79060379377688),(-79060000132582)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨1956649121461,1956657963907⟩,⟨(-971715254558),(-971706412108)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-1185439604),(-1185298792)⟩,⟨25828684457,25828825268⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-242419106),(-242417257)⟩,⟨(-187173070),(-187171218)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨4419359,4419403⟩,⟨(-82552),(-82508)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-92513),(-92495)⟩,⟨22095,22113⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨3597,3615⟩,⟨648,666⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-59),(-43)⟩,⟨(-284),(-268)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-39),(-23)⟩,⟨(-23),(-7)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨21090103759631755939,21090111904775547468⟩,⟨169191534303778147733,169191542448921939271⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨1395361797808619467095,1395361797808619503720⟩,⟨1225943268419401389234,1225943268419401425874⟩⟩
noncomputable def realAnswer : RBox := ⟨1416451901568151223034,1416451909713495051188⟩
end tm0_88_0

namespace tm0_88_1
noncomputable def s0_0 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-75),75⟩,⟨(-75),75⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-88),88⟩,⟨(-88),88⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-89),89⟩,⟨(-89),89⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-74),74⟩,⟨(-74),74⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-47),47⟩,⟨(-47),47⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-21),21⟩,⟨(-21),21⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-28),28⟩,⟨(-28),28⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-38),38⟩,⟨(-38),38⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-65),65⟩,⟨(-65),65⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-79),79⟩,⟨(-79),79⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-45),45⟩,⟨(-45),45⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-31),31⟩,⟨(-31),31⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-27),27⟩,⟨(-27),27⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨74,92⟩,⟨101,117⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨131,149⟩,⟨16,34⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨0,18⟩,⟨(-40),(-21)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-16),11⟩,⟨(-16),16⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨1450390222633086132038,1450390258026269382113⟩,⟨760284003462431474146,760284038855614724152⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨2354116474528105926053,2354116546334101904066⟩,⟨(-507260974553177109745),(-507260902747181131949)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-15681713363698908597),(-15681659823508201241)⟩,⟨(-995479337435527923595),(-995479283895337216180)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-165524631823858070886),(-165524610529873640936)⟩,⟨82618231030632268205,82618252324616698146⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨17752363667990481092,17752368456168709583⟩,⟨1295049885749927721,1295054673928156215⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-945223516338078819),(-945222921144608246)⟩,⟨(-82238091763519972),(-82237496570049402)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨27845054523932446,27845095200760697⟩,⟨(-10094589683607021),(-10094549006778774)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-249110170961855),(-249108583541812)⟩,⟨534068853163906,534070440583952⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-4572102528499),(-4572064686273)⟩,⟨(-7092022062270),(-7091984220045)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨100917258282,100917874433⟩,⟨(-7831444898),(-7830828745)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-606599160),(-606590932)⟩,⟨1052618680,1052626907⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-2899789),(-2899654)⟩,⟨(-17514239),(-17514102)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨146623,146642⟩,⟨357333,357356⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨258,278⟩,⟨(-15031),(-15011)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-1096),(-1080)⟩,⟨389,407⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-35),(-19)⟩,⟨122,138⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨606689180599640970914,606689211842812435108⟩,⟨(-109772472220217231494),(-109772440977045767338)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨4164901299291138266919,4164901299291138406128⟩,⟨(-5268887264501363866892),(-5268887264501363727734)⟩⟩
noncomputable def realAnswer : RBox := ⟨4771590479890679237833,4771590511134050841236⟩
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
open IntegerIntervals IntegerBasis IntegerGrid
namespace tm0_9_0
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
noncomputable def s1_0 : CBox := ⟨⟨9724426581,9724426597⟩,⟨(-8084170276),(-8084170260)⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨20038264554,20038264570⟩,⟨(-14465940369),(-14465940351)⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨15611023347,15611023366⟩,⟨(-8102298874),(-8102298850)⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨6806410987,6806411008⟩,⟨(-1628624614),(-1628624594)⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨1731470332,1731470350⟩,⟨230662380,230662399⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨234037624,234037646⟩,⟨178979280,178979300⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨7749283,7749305⟩,⟨35339764,35339787⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-2238218),(-2238192)⟩,⟨2721369,2721390⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-292772),(-292746)⟩,⟨(-67723),(-67701)⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-1270),(-1247)⟩,⟨(-25008),(-24984)⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨2221,2242⟩,⟨(-461),(-439)⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨66,86⟩,⟨228,248⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-44),(-20)⟩,⟨6,27⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-16),2⟩,⟨(-16),0⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),2⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨1033736294296294059,1033736294296294079⟩,⟨530603521805111454,530603521805111474⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨2416084454535359941,2416084454535359965⟩,⟨1016484680209096151,1016484680209096176⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨2399436998215053158,2399436998215053187⟩,⟨619444654633215153,619444654633215179⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨1494756500887448205,1494756500887448233⟩,⟨75798662223984614,75798662223984639⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨627427146835454499,627427146835454520⟩,⟨(-119348613173410299),(-119348613173410275)⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨183304876973936103,183304876973936121⟩,⟨(-86151326967879859),(-86151326967879837)⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨38694928261669773,38694928261669792⟩,⟨(-31203676032389216),(-31203676032389192)⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨6274424181989246,6274424181989267⟩,⟨(-7623276018951117),(-7623276018951098)⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨863965959839915,863965959839936⟩,⟨(-1436290221225962),(-1436290221225939)⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨116560589612226,116560589612245⟩,⟨(-232100331753818),(-232100331753800)⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨17769133194845,17769133194864⟩,⟨(-35399255462183),(-35399255462163)⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨3276285883601,3276285883620⟩,⟨(-5540549025091),(-5540549025071)⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨728093578472,728093578492⟩,⟨(-953248554945),(-953248554925)⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨191172929934,191172929952⟩,⟨(-189670274805),(-189670274785)⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨56406098688,56406098705⟩,⟨(-43951777316),(-43951777300)⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨12970794309,12970794326⟩,⟨(-8733057439),(-8733057422)⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨44910965140247787380529,44910965140247937662639⟩,⟨(-63064474855885816397906),(-63064474855885666106696)⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨96602912070968853450499,96602912070969136240266⟩,⟨(-169290711910089017655691),(-169290711910088734839421)⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨72546706883103761900199,72546706883103946869269⟩,⟨(-217050890761973439183865),(-217050890761973254178756)⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨7497067943622186433080,7497067943622268039011⟩,⟨(-189808046288286351265941),(-189808046288286269637703)⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-38418436282191317149946),(-38418436282191296718680)⟩,⟨(-116226359280661839316412),(-116226359280661818879367)⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-43124659426158629354491),(-43124659426158626609592)⟩,⟨(-47256855210856821235189),(-47256855210856818492895)⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨(-26158867595240773223957),(-26158867595240772980857)⟩,⟨(-10032476926038611301803),(-10032476926038611062137)⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨(-10530425523346500924277),(-10530425523346500883362)⟩,⟨1288325673258627954350,1288325673258627994217⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨(-2944325069598004061812),(-2944325069598004048444)⟩,⟨2055913958302934214382,2055913958302934227710⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨(-536486546844704226935),(-536486546844704222057)⟩,⟨991794980148743657523,991794980148743662481⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨(-24654967275820332462),(-24654967275820330693)⟩,⟨341451464634375261461,341451464634375263272⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨30564357256991568109,30564357256991568764⟩,⟨100473332658108548533,100473332658108549197⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨19036809306551297450,19036809306551297703⟩,⟨28054336837996666347,28054336837996666600⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨8648162692864046797,8648162692864046905⟩,⟨7997452133501145902,7997452133501146010⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨3510903137312726710,3510903137312726762⟩,⟨2369050889170441008,2369050889170441058⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨940258153721123223,940258153721123250⟩,⟨534903677138701287,534903677138701311⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨23970232659016335688838577,23970232659016950788527948⟩,⟨(-55805092339568703539036811),(-55805092339568088444031897)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨46773321218604349909368632,46773321218606372947518232⟩,⟨(-154339184848419968027899698),(-154339184848417945004976200)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨15570589853484593700837338,15570589853488371605647403⟩,⟨(-210691857911325331007226239),(-210691857911321553129299655)⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-51285911422267924249457756),(-51285911422261760765796305)⟩,⟨(-201726920405024142310530482),(-201726920405017978857390668)⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-104466008636042344622393544),(-104466008636031148898514155)⟩,⟨(-134455478237686874584598741),(-134455478237675678875093466)⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-109791961470559361431007264),(-109791961470544347893933098)⟩,⟨(-50168151564701009730045142),(-50168151564685996192941474)⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨(-75576065333119772541247484),(-75576065333106676832790592)⟩,⟨7843705473191249722898080,7843705473204345438198476⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨(-34027746209980930025923080),(-34027746209972905958703456)⟩,⟨26786431584196456107203483,26786431584204480180118483⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨(-7360996021305316846739472),(-7360996021300211904077305)⟩,⟨21600894026850919595585752,21600894026856024539244897⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨2687937810548788266515473,2687937810550805473976828⟩,⟨11060128329410622655426049,11060128329412639862281346⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨3855029401321375561893171,3855029401321887885533547⟩,⟨3937749588202245319591937,3937749588202757642546031⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨2523330966547991494441905,2523330966548143575191392⟩,⟨816663063222353054811112,816663063222505135333060⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨1281898284306960600340648,1281898284307003236820904⟩,⟨(-121670398119595666733683),(-121670398119553030280539)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨574332519470375755821019,574332519470386847886028⟩,⟨(-249817281090518144490149),(-249817281090507052406511)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨232011895637753468473856,232011895637756430550466⟩,⟨(-167217840279298201702272),(-167217840279295239607946)⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨61459285452539406963290,61459285452540034057532⟩,⟨(-55292490137629779459179),(-55292490137629152358562)⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨110666656397718711796665405,110666656397718714121426710⟩,⟨(-1464901816835560494955085567),(-1464901816835560492473279624)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-199947743550308376133229999),(-199947743550308369235228514)⟩,⟨(-4068071205076611369676858519),(-4068071205076611362311363670)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-1680356302148494371635844750),(-1680356302148494359996219473)⟩,⟨(-5617526856717998470949277336),(-5617526856717998458726865788)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-3951361293333218560285784771),(-3951361293333218544087776849)⟩,⟨(-5448346839915247982085658330),(-5448346839915247965435999315)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-5772051077033485083028515508),(-5772051077033485063170192481)⟩,⟨(-3488584765088008676281093189),(-3488584765088008656258391190)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-5990044408097846889993102280),(-5990044408097846868661262837)⟩,⟨(-620796666740724650326236271),(-620796666740724629074032008)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-4500911607058230005362617923),(-4500911607058229984993904583)⟩,⟨1760474897343839907551698884,1760474897343839927728888865⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-2258040325644974755553933232),(-2258040325644974735913906945)⟩,⟨2738340545317183417505581163,2738340545317183437022825036⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-393550395666093112376651260),(-393550395666093083272568474)⟩,⟨2409249002958464370465546454,2409249002958464399551883166⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨571313025774019811557570481,571313025774019890907139269⟩,⟨1501399666370833622676101465,1501399666370833702033883646⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨780011236501464365831526095,780011236501464576374387001⟩,⟨669587889405068751265935816,669587889405068961810702950⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨622390245596354441852918357,622390245596355028363932713⟩,⟨169015725658844767278714877,169015725658845353785016669⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨392912909095337141660413637,392912909095338325266523972⟩,⟨(-41281124086521271933168467),(-41281124086520088331024478)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨213888725347239772419881065,213888725347241298722023044⟩,⟨(-87532049534506509862622741),(-87532049534504983561710978)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨100197866300186824566131145,100197866300188087197755405⟩,⟨(-65750433314785138926492814),(-65750433314783876294879860)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨28786771196802246086352812,28786771196802727095612904⟩,⟨(-23184510504939554141372168),(-23184510504939073131998021)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-3701829061804096058538475559),(-3701829061804083853459432051)⟩,⟨(-2069075260485955948224339672),(-2069075260485943742923222070)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-5228957982970673769556563959),(-5228957982970673765550616868)⟩,⟨(-544649371312902746670181835),(-544649371312902742706373570)⟩⟩
noncomputable def realAnswer : RBox := ⟨(-8930787044774769828195039518),(-8930787044774757618910048919)⟩
end tm0_9_0

namespace tm0_9_1
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-28),16⟩,⟨(-25),18⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-38),16⟩,⟨(-32),18⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-31),47⟩,⟨(-47),18⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-24),55⟩,⟨(-28),52⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-59),25⟩,⟨(-38),45⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-35),67⟩,⟨(-65),38⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-82),56⟩,⟨(-58),78⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-58),70⟩,⟨(-78),52⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-64),64⟩,⟨(-68),60⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-40),69⟩,⟨(-53),60⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-62),40⟩,⟨(-48),56⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-33),41⟩,⟨(-47),31⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-19),32⟩,⟨(-29),32⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-21),19⟩,⟨(-16),21⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-89610549523),(-89610549500)⟩,⟨(-10164228465),(-10164228439)⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-174154399150),(-174154399117)⟩,⟨(-30951396526),(-30951396486)⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-120657395544),(-120657395493)⟩,⟨(-38896299484),(-38896299433)⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-43711143653),(-43711143593)⟩,⟨(-26204860166),(-26204860107)⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-8143746516),(-8143746445)⟩,⟨(-9989410727),(-9989410656)⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-413723055),(-413722971)⟩,⟨(-2168710942),(-2168710858)⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨128508580,128508667⟩,⟨(-244045508),(-244045419)⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨26729733,26729823⟩,⟨(-5808941),(-5808847)⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨1547076,1547176⟩,⟨1802892,1802988⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-105105),(-105010)⟩,⟨171762,171860⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-17431),(-17338)⟩,⟨(-6697),(-6606)⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨420,502⟩,⟨(-2063),(-1984)⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨266,337⟩,⟨(-32),40⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-7),49⟩,⟨28,81⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-32),16⟩,⟨(-2),34⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-222161278343409369),(-222161278343409320)⟩,⟨(-6788107497801328521),(-6788107497801328471)⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-1729400710855516343),(-1729400710855516243)⟩,⟨(-15276811324910815969),(-15276811324910815869)⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-3851059991294465907),(-3851059991294465799)⟩,⟨(-14119206575186345487),(-14119206575186345379)⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-4122702155355850277),(-4122702155355850188)⟩,⟨(-7919329758660676207),(-7919329758660676119)⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-2584888885878326559),(-2584888885878326493)⟩,⟨(-2866157087266519814),(-2866157087266519747)⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-1048394148373671937),(-1048394148373671883)⟩,⟨(-667864006248216046),(-667864006248215988)⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-295948186413048390),(-295948186413048335)⟩,⟨(-93781196148583516),(-93781196148583461)⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-62634447518646827),(-62634447518646772)⟩,⟨(-5033121264452783),(-5033121264452729)⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-10832100233532355),(-10832100233532290)⟩,⟨993963621646812,993963621646871⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-1686794654100188),(-1686794654100127)⟩,⟨329293646716324,329293646716383⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-260697196509786),(-260697196509724)⟩,⟨57673628622697,57673628622758⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-43474654178285),(-43474654178224)⟩,⟨7558858207340,7558858207401⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-8319421231519),(-8319421231465)⟩,⟨620444635121,620444635172⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-1892370566713),(-1892370566666)⟩,⟨(-86944098850),(-86944098806)⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-501002281351),(-501002281318)⟩,⟨(-77565589243),(-77565589208)⟩⟩
noncomputable def s2_15 : CBox := ⟨⟨(-108696615401),(-108696615376)⟩,⟨(-23944050807),(-23944050784)⟩⟩
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
noncomputable def s3_0 : CBox := ⟨⟨(-359790637946035812884151),(-359790637946035188853827)⟩,⟨(-111730650282597954491373),(-111730650282597330521428)⟩⟩
noncomputable def s3_1 : CBox := ⟨⟨(-932905003572507167599233),(-932905003572505824342941)⟩,⟨(-186883271713635346226486),(-186883271713634003105647)⟩⟩
noncomputable def s3_2 : CBox := ⟨⟨(-1124019516369950717644863),(-1124019516369949630142637)⟩,⟨4964791084524596997245,4964791084525684382102⟩⟩
noncomputable def s3_3 : CBox := ⟨⟨(-900374973884132206508886),(-900374973884131745076332)⟩,⟨275087230312758553098593,275087230312759014488795⟩⟩
noncomputable def s3_4 : CBox := ⟨⟨(-482303534340403429222966),(-482303534340403325096438)⟩,⟨379668560735696004011192,379668560735696108157279⟩⟩
noncomputable def s3_5 : CBox := ⟨⟨(-147170312360268469647711),(-147170312360268457232330)⟩,⟨290103053098810807010771,290103053098810819463355⟩⟩
noncomputable def s3_6 : CBox := ⟨⟨1632716255685220317484,1632716255685221612910⟩,⟨144711263788241669118855,144711263788241670430503⟩⟩
noncomputable def s3_7 : CBox := ⟨⟨27532441444757485878359,27532441444757486143831⟩,⟨48471547582993370365488,48471547582993370632160⟩⟩
noncomputable def s3_8 : CBox := ⟨⟨16393665025962610823539,16393665025962610914579⟩,⟨10010778677305368361233,10010778677305368450930⟩⟩
noncomputable def s3_9 : CBox := ⟨⟨6127391299002471535229,6127391299002471570122⟩,⟨395209657300251204841,395209657300251239003⟩⟩
noncomputable def s3_10 : CBox := ⟨⟨1763079323479500557279,1763079323479500570458⟩,⟨(-698630905567196364733),(-698630905567196351665)⟩⟩
noncomputable def s3_11 : CBox := ⟨⟨427859841672599518167,427859841672599523008⟩,⟨(-407727885161158334579),(-407727885161158329734)⟩⟩
noncomputable def s3_12 : CBox := ⟨⟨91715002729784394909,91715002729784396725⟩,⟨(-170296390369515501405),(-170296390369515499579)⟩⟩
noncomputable def s3_13 : CBox := ⟨⟨17070909984171205807,17070909984171206518⟩,⟨(-65758026741568804577),(-65758026741568803862)⟩⟩
noncomputable def s3_14 : CBox := ⟨⟨2285960434542914259,2285960434542914543⟩,⟨(-24507938445769121609),(-24507938445769121323)⟩⟩
noncomputable def s3_15 : CBox := ⟨⟨78150576102499804,78150576102499891⟩,⟨(-6310751227987334144),(-6310751227987334058)⟩⟩
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
noncomputable def s4_0 : CBox := ⟨⟨(-245069926260178379871244281),(-245069926260176011594814249)⟩,⟨(-58508637073572474821096585),(-58508637073570106516357388)⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-665988585699872165860963685),(-665988585699864518394018721)⟩,⟨(-80578530751740374578317414),(-80578530751732727025056555)⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-878673084482137676894351685),(-878673084482123436567684729)⟩,⟨92619851111498066841477590,92619851111512307303178194⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-795656982642581376536027864),(-795656982642552254267298729)⟩,⟨369713653404306023635076791,369713653404335146005424822⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-475303014377329721689389264),(-475303014377279094837678783)⟩,⟨547498426896587812038653734,547498426896638438920581135⟩⟩
noncomputable def s4_5 : CBox := ⟨⟨(-114637946382461749096684143),(-114637946382398284242342331)⟩,⟨507490269587818341624837496,507490269587881806454989420⟩⟩
noncomputable def s4_6 : CBox := ⟨⟨105202666326144401803721791,105202666326195539699427466⟩,⟨314908233167878087492699418,314908233167929225345454410⟩⟩
noncomputable def s4_7 : CBox := ⟨⟨150388536097348832503608523,150388536097388795312222138⟩,⟨119468665219940416986937011,119468665219980379777218109⟩⟩
noncomputable def s4_8 : CBox := ⟨⟨102448921750277936912221910,102448921750301492992671233⟩,⟨8385818832305554455659208,8385818832329110536931430⟩⟩
noncomputable def s4_9 : CBox := ⟨⟨45711861834440059411636730,45711861834448376070842658⟩,⟨(-24935602099544111442263241),(-24935602099535794777696116)⟩⟩
noncomputable def s4_10 : CBox := ⟨⟨12744954838218887868822631,12744954838221348464809397⟩,⟨(-22190213256431627610536890),(-22190213256429167011699261)⟩⟩
noncomputable def s4_11 : CBox := ⟨⟨321378872320935292924317,321378872321723574319323⟩,⟨(-12482271654184314858286727),(-12482271654183526576480551)⟩⟩
noncomputable def s4_12 : CBox := ⟨⟨(-2348382665360777019904756),(-2348382665360576205641268)⟩,⟨(-5667533628374436711979582),(-5667533628374235897928599)⟩⟩
noncomputable def s4_13 : CBox := ⟨⟨(-1979992211045618113504901),(-1979992211045570038274356)⟩,⟨(-2270271500717446475509085),(-2270271500717398400526508)⟩⟩
noncomputable def s4_14 : CBox := ⟨⟨(-1116170098565116090086666),(-1116170098565104146312800)⟩,⟨(-819427538197463987925501),(-819427538197452044303805)⟩⟩
noncomputable def s4_15 : CBox := ⟨⟨(-348132636715436060643284),(-348132636715433614992010)⟩,⟨(-200260529722605252499148),(-200260529722602806896251)⟩⟩
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
noncomputable def s5_0 : CBox := ⟨⟨(-5313816206645151054510464307),(-5313816206645151045221203184)⟩,⟨(-121842765904017170396541535),(-121842765904017161719453632)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-14691539950289463726114832159),(-14691539950289463698183756571)⟩,⟨1528768946936434526329356684,1528768946936434552555090288⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-20072334518799345005543656524),(-20072334518799344958648129378)⟩,⟨7312462833711828097884142238,7312462833711828142770876890⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-19006413767282847043490763135),(-19006413767282846979013084546)⟩,⟨15757147471312703213808452414,15757147471312703276807172013⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-11329698953074224692788878500),(-11329698953074224614266070899)⟩,⟨22238462201287596863771785208,22238462201287596941885608214⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-487692982689973930981512966),(-487692982689973846386417738)⟩,⟨22514309588056132989176465207,22514309588056133074242669548⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨8196676924385357077266868650,8196676924385357158935659380⟩,⟨16347334599470572459178893502,16347334599470572541674105195⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨11329147082100434886816608884,11329147082100434968444054813⟩,⟨7528164455146402171623385205,7528164455146402253657623286⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨9470130031776756336863283565,9470130031776756455570639246⟩,⟨448340613049308161120651916,448340613049308279856259070⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨5579245256904407752204926481,5579245256904408055929984425⟩,⟨(-2973973816486369381684292761),(-2973973816486369078005191940)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨2219024372290882690536987488,2219024372290883533499421037⟩,⟨(-3445152608739501775037414333),(-3445152608739500932080921481)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨306084157645094659323732187,306084157645097204364631359⟩,⟨(-2583199036095713729543370058),(-2583199036095711184483291841)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-414748634783097088111702184),(-414748634783092152990148871)⟩,⟨(-1555392224776827125327981062),(-1555392224776822190193593430)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-497199716144378443641681028),(-497199716144372278744924317)⟩,⟨(-808653054004819814710121448),(-808653054004813649811554285)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-336840552501480354230384911),(-336840552501475380481629364)⟩,⟨(-362768590231385944989959439),(-362768590231380971243251513)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-114844459356533817462587124),(-114844459356531950087438776)⟩,⟨(-101272616212053379543100077),(-101272616212051512169125562)⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-6322169733967723643235671498),(-6322169733967670945591468917)⟩,⟨13912670257375713621459603921,13912670257375766318404064827⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-923424386511920245166739646),(-923424386511920229922906662)⟩,⟨19036194329455527413133444733,19036194329455527428572877251⟩⟩
noncomputable def realAnswer : RBox := ⟨(-7245594120479643888502411144),(-7245594120479591175414375579)⟩
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
open IntegerIntervals IntegerBasis IntegerGrid
namespace tm0_91_0
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
noncomputable def s4_0 : CBox := ⟨⟨(-16),0⟩,⟨(-5),15⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-16),3⟩,⟨0,16⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-5),16⟩,⟨(-9),16⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-197175561305161866826),(-197175548484259527383)⟩,⟨(-163495496556015315323),(-163495483735112975877)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-366963005691946814848),(-366962980165003249849)⟩,⟨7160682802825638827,7160708329769203793⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-20607117032889661971),(-20607098705572129084)⟩,⟨142849897088746316404,142849915416063849298⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨23402154896496910018,23402161780237075578⟩,⟨(-8692991973598092499),(-8692985089857926937)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-2179136744768260543),(-2179135311960099871)⟩,⟨(-237991759036958393),(-237990326228797719)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨104515129822523968,104515291387778210⟩,⟨3345085197367926,3345246762622171⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-2501416580039424),(-2501406766278514)⟩,⟨1398609582967102,1398619396728009⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨7606172788165,7606506630531⟩,⟨(-48637312451003),(-48636978608640)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨499204067387,499210889235⟩,⟨334573443872,334580265717⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-4989522380),(-4989428311)⟩,⟨3514969517,3515063587⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-8607873),(-8606804)⟩,⟨(-61389420),(-61388350)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨625401,625432⟩,⟨452386,452416⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-13920),(-13903)⟩,⟨(-4222),(-4206)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨402,418⟩,⟨281,297⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-2),14⟩,⟨(-43),(-27)⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-93903440677441312290),(-93903429816869388840)⟩,⟨(-3735200833597175977),(-3735189973025252529)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-817274263715676628040),(-817274263715676587163)⟩,⟨671020877302814041315,671020877302814082178⟩⟩
noncomputable def realAnswer : RBox := ⟨(-911177704393217940330),(-911177693532445976003)⟩
end tm0_91_0

namespace tm0_91_1
noncomputable def s0_0 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-75),75⟩,⟨(-75),75⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-88),88⟩,⟨(-88),88⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-89),89⟩,⟨(-89),89⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-74),74⟩,⟨(-74),74⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-47),47⟩,⟨(-47),47⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-21),21⟩,⟨(-21),21⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-28),28⟩,⟨(-28),28⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-38),38⟩,⟨(-38),38⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-65),65⟩,⟨(-65),65⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-79),79⟩,⟨(-79),79⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-45),45⟩,⟨(-45),45⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-31),31⟩,⟨(-31),31⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-27),27⟩,⟨(-27),27⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨0,16⟩,⟨9,25⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨2,26⟩,⟨(-3),18⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-11),16⟩,⟨(-16),6⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-553264511297970462866),(-553264462543335840857)⟩,⟨743396454164782416215,743396502919417038234⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨98501994211452405407,98502091670675602286⟩,⟨1326664406982504761762,1326664504441727958761⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨523174011679852598022,523174082199859933897⟩,⟨44377019852618987253,44377090372626323100⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-37239308552305830693),(-37239281762440091445)⟩,⟨(-83390948571577949387),(-83390921781712210136)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-301923452822103072),(-301917794850643636)⟩,⟨8075040517230922756,8075046175202382190⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-18607155338711639),(-18606506204179443)⟩,⟨(-388744382956525109),(-388743733821992912)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨6084877571116197,6084917780113226⟩,⟨8907335571254411,8907375780251441⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-187350511593242),(-187349114406553)⟩,⟨(-10305428166174),(-10304030979482)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨1069547544369,1069576735256⟩,⟨(-2059986568731),(-2059957377849)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨16055621691,16056033243⟩,⟨17693399006,17693810557⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-236725422),(-236720689)⟩,⟨66505313,66510046⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨1434030,1434110⟩,⟨(-2748343),(-2748266)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-8215),(-8194)⟩,⟨58448,58472⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨883,903⟩,⟨(-1865),(-1844)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-155),(-137)⟩,⟨(-9),8⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-19),(-3)⟩,⟨6,23⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨5142925674215880415,5142967319627994133⟩,⟨339790353925086057128,339790395570498170861⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨2576536190032726232842,2576536190032726388095⟩,⟨2825198806221956490450,2825198806221956645750⟩⟩
noncomputable def realAnswer : RBox := ⟨2581679115706842113257,2581679157352454382228⟩
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
open IntegerIntervals IntegerBasis IntegerGrid
namespace tm0_93_0
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
noncomputable def s4_0 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨0,16⟩,⟨(-9),16⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-14),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-169782436447755264085),(-169782420575044699727)⟩,⟨43395459040837378357,43395474913547942699⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-138773769502102597058),(-138773738208526136556)⟩,⟨204467545950906681288,204467577244483141796⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨69954965610931113251,69954987634860705910⟩,⟨63121142554488976908,63121164578418569570⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨3053667624693919149,3053675648458251462⟩,⟨(-15297993963254210672),(-15297985939489878361)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-741398530188913320),(-741396928286132006)⟩,⟨1062662503668564190,1062664105571345504⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨25966321956688341,25966493206084666⟩,⟨(-51615161380721383),(-51614990131325054)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨224131847428838,224141590262705⟩,⟨1445621302627072,1445631045460938⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-20936150907391),(-20935844140902)⟩,⟨(-9460247961821),(-9459941195333)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨176696301935,176702042953⟩,⟨(-183020619516),(-183014878498)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨1178990119,1179062044⟩,⟨2013177115,2013249040⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-21157269),(-21156522)⟩,⟨3127401,3128148⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨122580,122603⟩,⟨(-207898),(-207873)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-521),(-504)⟩,⟨4118,4135⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨42,58⟩,⟨(-133),(-116)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-19),(-3)⟩,⟨(-4),13⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-39377133591485712780),(-39377120425287622088)⟩,⟨49449772817552802292,49449785983750892986⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨40303502128701274783,40303502128701301437⟩,⟨725259694367050948960,725259694367050975622⟩⟩
noncomputable def realAnswer : RBox := ⟨926368537115562003,926381703513679349⟩
end tm0_93_0

namespace tm0_93_1
noncomputable def s0_0 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-75),75⟩,⟨(-75),75⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-88),88⟩,⟨(-88),88⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-89),89⟩,⟨(-89),89⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-74),74⟩,⟨(-74),74⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-47),47⟩,⟨(-47),47⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-21),21⟩,⟨(-21),21⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-28),28⟩,⟨(-28),28⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-38),38⟩,⟨(-38),38⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-65),65⟩,⟨(-65),65⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-79),79⟩,⟨(-79),79⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-45),45⟩,⟨(-45),45⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-31),31⟩,⟨(-31),31⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-27),27⟩,⟨(-27),27⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-10),16⟩,⟨(-16),1⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨189003910276100614532,189003970635930142942⟩,⟨605162798984947603595,605162859344777132058⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨767430529694277241135,767430649168915472576⟩,⟨461787524423786575392,461787643898424806814⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨214311591542100091572,214311676284093919561⟩,⟨(-267499689438290394571),(-267499604696296566589)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-56563845816068090692),(-56563814590750791170)⟩,⟨(-7552100344666499056),(-7552069119349199528)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨4101912118943528139,4101918444276965292⟩,⟨2446669103078397325,2446675428411834476⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-199183591605942045),(-199182903613407994)⟩,⟨(-81031027708666195),(-81030339716132141)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨5344249018477450,5344288933530094⟩,⟨(-1326112063510149),(-1326072148457505)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-27902359929274),(-27901076172471)⟩,⟨82999146561479,83000430318276⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-778408044166),(-778383480326)⟩,⟨(-599601890242),(-599577326401)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨7254487346,7254801971⟩,⟨(-5548379257),(-5548064634)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨23546844,23550126⟩,⟨81496114,81499392⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-897339),(-897281)⟩,⟨(-366351),(-366291)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨16868,16888⟩,⟨(-540),(-519)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-545),(-527)⟩,⟨(-127),(-108)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-3),20⟩,⟨27,45⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨0,16⟩,⟨(-9),16⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨186348371633212516171,186348422109267275423⟩,⟨132377154663860154102,132377205139914913359⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨2611363717340034072507,2611363717340034173808⟩,⟨(-281721440971747722952),(-281721440971747621688)⟩⟩
noncomputable def realAnswer : RBox := ⟨2797712088973146588678,2797712139449401449231⟩
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
open IntegerIntervals IntegerBasis IntegerGrid
namespace tm0_96_0
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
noncomputable def s4_0 : CBox := ⟨⟨(-16),16⟩,⟨(-6),16⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-9229471938811067026),(-9229450073698349587)⟩,⟨(-98735761198938700580),(-98735739333825983130)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-101293322852434896379),(-101293280375157144548)⟩,⟨(-91525970884652767710),(-91525928407375015882)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-36862335276321010374),(-36862306260458332407)⟩,⟨33348921397496919861,33348950413359597827⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨7486235270978974035,7486245370450839075⟩,⟨1842736561521615803,1842746660993480840⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-494618970329967633),(-494617076026687164)⟩,⟨(-320539734446234954),(-320537840142954486)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨22459325035902404,22459511993430324⟩,⟨7750656632694258,7750843590222181⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-490970081296686),(-490960438642469)⟩,⟨210478128310186,210487770964403⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨314823593447,315093975189⟩,⟨(-7326600711173),(-7326330329432)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨67991789004,67996224175⟩,⟨17252725645,17257160819⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-205576857),(-205528737)⟩,⟨512313315,512361436⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-3512504),(-3512067)⟩,⟨(-2547938),(-2547498)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨39018,39040⟩,⟨(-16163),(-16143)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-395),(-378)⟩,⟨494,512⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨3,21⟩,⟨(-22),(-6)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-16),0⟩,⟨(-10),10⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-16),9⟩,⟨(-1),16⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-23395257504892838545),(-23395239913408948039)⟩,⟨(-25897110005516066712),(-25897092414032176207)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-411174576857881246441),(-411174576857881239564)⟩,⟨(-44156925331022093108),(-44156925331022086234)⟩⟩
noncomputable def realAnswer : RBox := ⟨(-434569834362874084986),(-434569816771190187603)⟩
end tm0_96_0

namespace tm0_96_1
noncomputable def s0_0 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-75),75⟩,⟨(-75),75⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-88),88⟩,⟨(-88),88⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-89),89⟩,⟨(-89),89⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-74),74⟩,⟨(-74),74⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-47),47⟩,⟨(-47),47⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-21),21⟩,⟨(-21),21⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-28),28⟩,⟨(-28),28⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-38),38⟩,⟨(-38),38⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-65),65⟩,⟨(-65),65⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-79),79⟩,⟨(-79),79⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-45),45⟩,⟨(-45),45⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-31),31⟩,⟨(-31),31⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-27),27⟩,⟨(-27),27⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-7),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-354965206694668163437),(-354965123547393603286)⟩,⟨52083376905525220686,52083460052799780799⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-311196543702881554604),(-311196381532401673091)⟩,⟨384682445622020772614,384682607792500654129⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨128957218221679710163,128957329863020573912⟩,⟨126751635245331706318,126751746886672570069⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨4968586967285507722,4968626268095104843⟩,⟨(-27759598062410737193),(-27759558761601140076)⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-1048668712799081758),(-1048661233531054260)⟩,⟨1902541751914082294,1902549231182109793⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨22105110376254862,22105861394348818⟩,⟨(-85612549414889896),(-85611798396795941)⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨953812962399259,953852462186593⟩,⟨1769922641384013,1769962141171346⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-27904755741436),(-27903624392418)⟩,⟨1592141626246,1593272975262⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨37036969863,37055944015⟩,⟨(-268396439688),(-268377465535)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨2089039150,2089249602⟩,⟨552434153,552644607⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-8148425),(-8146528)⟩,⟨15158738,15160635⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-86867),(-86828)⟩,⟨(-145721),(-145682)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨2261,2279⟩,⟨1227,1246⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-69),(-49)⟩,⟨(-56),(-37)⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-8),12⟩,⟨0,16⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-9),16⟩,⟨(-14),16⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-88876930477280482692),(-88876863055473590591)⟩,⟨89596093359986695150,89596160781793587245⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-82244177775945124171),(-82244177775945098049)⟩,⟨1493053597419901400502,1493053597419901426640⟩⟩
noncomputable def realAnswer : RBox := ⟨(-171121108253325606863),(-171121040831318688640)⟩
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
open IntegerIntervals IntegerBasis IntegerGrid
namespace tm0_97_0
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
noncomputable def s4_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨43879054889285668736,43879079217996282579⟩,⟨69300279143502000324,69300303472212614173⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨108328672105163391346,108328719137332004809⟩,⟨28516509110651356820,28516556142819970277⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨13610806807528381432,13610838617368985118⟩,⟨(-37791751502056552505),(-37791719692215948816)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-5879909966956179268),(-5879899061864109930)⟩,⟨1610162589462506527,1610173494554575863⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨453035903878762269,453037907233687647⟩,⟨18213405354014061,18215408708939437⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-17184490303463004),(-17184297773596636)⟩,⟨4128763482103217,4128956011969583⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨202384572738052,202394183597373⟩,⟨(-323902361145573),(-323892750286249)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨2862602875616,2862862156668⟩,⟨4115296721768,4115556002818⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨(-41163765183),(-41159694880)⟩,⟨19789012119,19793082419⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-120933290),(-120891196)⟩,⟨(-319440738),(-319398642)⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨2516978,2517342⟩,⟨(-410301),(-409933)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨(-8034),(-8014)⟩,⟨22220,22240⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-81),(-65)⟩,⟨(-341),(-324)⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-4),13⟩,⟨2,20⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-7),16⟩,⟨(-16),0⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),13⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨26729113409081664042,26729132789343488692⟩,⟨10276203623800031046,10276223004061855695⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨320474253807146439178,320474253807146447953⟩,⟨(-121525112250316611337),(-121525112250316602569)⟩⟩
noncomputable def realAnswer : RBox := ⟨347203367216128103220,347203386596589936645⟩
end tm0_97_0

namespace tm0_97_1
noncomputable def s0_0 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-75),75⟩,⟨(-75),75⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-88),88⟩,⟨(-88),88⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-89),89⟩,⟨(-89),89⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-74),74⟩,⟨(-74),74⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-47),47⟩,⟨(-47),47⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-21),21⟩,⟨(-21),21⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-28),28⟩,⟨(-28),28⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-38),38⟩,⟨(-38),38⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-65),65⟩,⟨(-65),65⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-79),79⟩,⟨(-79),79⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-45),45⟩,⟨(-45),45⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-31),31⟩,⟨(-31),31⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-27),27⟩,⟨(-27),27⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨242043153489413671600,242043246005059972997⟩,⟨(-171680464017100754458),(-171680371501454453078)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨81773963511375802000,81774143070852991294⟩,⟨(-397678112235108986188),(-397677932675631796864)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-140132442721608754359),(-140132320331507595470)⟩,⟨(-41371069142638433853),(-41370946752537274968)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨7257689710267884177,7257732145208814683⟩,⟨21084769080647620200,21084811515588550706⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-51854634370395740),(-51846724760772302)⟩,⟨(-1670314735064635638),(-1670306825455012199)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨20399987264238983,20400760639080984⟩,⟨62526636612073772,62527409986915771⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-1282156271340354),(-1282116903374334)⟩,⟨(-650110418689889),(-650071050723872)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨14517888804691,14518973660232⟩,⟨(-12421948731350),(-12420863875807)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨93616057304,93633469777⟩,⟨149490813675,149508226151⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-1182992429),(-1182808342)⟩,⟨622999217,623183301⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-2950300),(-2948719)⟩,⟨(-9676949),(-9675367)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨92967,93005⟩,⟨18965,19002⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-1297),(-1278)⟩,⟨492,514⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨26,47⟩,⟨(-20),0⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-16),2⟩,⟨(-16),8⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨31818273632731685736,31818347903335097569⟩,⟨(-98542221132486064146),(-98542146861882652311)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-499006870191241565769),(-499006870191241532447)⟩,⟨(-1134421697277981709521),(-1134421697277981676175)⟩⟩
noncomputable def realAnswer : RBox := ⟨(-467188596558609880033),(-467188522287806434878)⟩
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
open IntegerIntervals IntegerBasis IntegerGrid
namespace tm0_99_0
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
noncomputable def s4_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨56002351629753822433,56002381749727145659⟩,⟨3580664185323347443,3580694305296670662⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨57817034443160071720,57817092103660395505⟩,⟨(-48431802000282268207),(-48431744339781944426)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-15528225975911660410),(-15528187743462859279)⟩,⟨(-21140042517911504257),(-21140004285462703127)⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨(-1077415895664683825),(-1077403180376235466)⟩,⟨3657340217123234768,3657352932411683127⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨138357350742763553,138359591681561692⟩,⟨(-230001870687564974),(-229999629748766837)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨(-1933453524169397),(-1933249311325800)⟩,⟨9590541349128604,9590745561972204⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-119154367436466),(-119144817852409)⟩,⟨(-154788434995685),(-154778885411630)⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨2210800425695,2211038910412⟩,⟨(-778354761380),(-778116276663)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨5179576552,5183005561⟩,⟨18661017518,18664446531⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨(-125786334),(-125754114)⟩,⟨35864619,35896839⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-148226),(-147965)⟩,⟨(-869055),(-868797)⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨7157,7174⟩,⟨1847,1866⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨(-101),(-84)⟩,⟨28,44⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-6),16⟩,⟨(-14),2⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),14⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨16225008526673796837,16225032057199475371⟩,⟨(-10425734498863228345),(-10425710968337549814)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨62679313250272488329,62679313250272494141⟩,⟨(-226937335747300982081),(-226937335747300976268)⟩⟩
noncomputable def realAnswer : RBox := ⟨78904321776846285166,78904345307571969512⟩
end tm0_99_0

namespace tm0_99_1
noncomputable def s0_0 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s0_1 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s0_2 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s0_3 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s0_4 : CBox := ⟨⟨(-75),75⟩,⟨(-75),75⟩⟩
noncomputable def s0_5 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_6 : CBox := ⟨⟨(-88),88⟩,⟨(-88),88⟩⟩
noncomputable def s0_7 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
noncomputable def s0_8 : CBox := ⟨⟨(-89),89⟩,⟨(-89),89⟩⟩
noncomputable def s0_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s0_10 : CBox := ⟨⟨(-74),74⟩,⟨(-74),74⟩⟩
noncomputable def s0_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s0_12 : CBox := ⟨⟨(-47),47⟩,⟨(-47),47⟩⟩
noncomputable def s0_13 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s0_14 : CBox := ⟨⟨(-21),21⟩,⟨(-21),21⟩⟩
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1_1 : CBox := ⟨⟨(-28),28⟩,⟨(-28),28⟩⟩
noncomputable def s1_2 : CBox := ⟨⟨(-38),38⟩,⟨(-38),38⟩⟩
noncomputable def s1_3 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s1_4 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
noncomputable def s1_5 : CBox := ⟨⟨(-65),65⟩,⟨(-65),65⟩⟩
noncomputable def s1_6 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_7 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_8 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
noncomputable def s1_10 : CBox := ⟨⟨(-79),79⟩,⟨(-79),79⟩⟩
noncomputable def s1_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
noncomputable def s1_12 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
noncomputable def s1_13 : CBox := ⟨⟨(-45),45⟩,⟨(-45),45⟩⟩
noncomputable def s1_14 : CBox := ⟨⟨(-31),31⟩,⟨(-31),31⟩⟩
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s2_3 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
noncomputable def s2_4 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_5 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_6 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_7 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
noncomputable def s2_8 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_9 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_10 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_11 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_12 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
noncomputable def s2_13 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
noncomputable def s2_14 : CBox := ⟨⟨(-27),27⟩,⟨(-27),27⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s4_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨2307776235439012604,2307890773617178532⟩,⟨(-203006940197812416658),(-203006825659634250710)⟩⟩
noncomputable def s5_1 : CBox := ⟨⟨(-186705896353946969358),(-186705676219431311502)⟩,⟨(-199656130740042112143),(-199655910605526454281)⟩⟩
noncomputable def s5_2 : CBox := ⟨⟨(-73454170721955799925),(-73454023623732597256)⟩,⟨60889060075462575191,60889207173685777858⟩⟩
noncomputable def s5_3 : CBox := ⟨⟨13602116595178667932,13602166072186426424⟩,⟨3074525814970366002,3074575291978124499⟩⟩
noncomputable def s5_4 : CBox := ⟨⟨(-881790792142502876),(-881781945011248350)⟩,⟨(-448379532422839069),(-448370685291584543)⟩⟩
noncomputable def s5_5 : CBox := ⟨⟨36148331391073578,36149151637420699⟩,⟨4337209805667606,4338030052014727⟩⟩
noncomputable def s5_6 : CBox := ⟨⟨(-540350778285447),(-540311664405033)⟩,⟨498525668893555,498564782773970⟩⟩
noncomputable def s5_7 : CBox := ⟨⟨(-3791951660474),(-3790953900443)⟩,⟨(-8089320679654),(-8088322919620)⟩⟩
noncomputable def s5_8 : CBox := ⟨⟨69404377758,69419045646⟩,⟨(-27897044840),(-27882376950)⟩⟩
noncomputable def s5_9 : CBox := ⟨⟨199671928,199812813⟩,⟨471332740,471473625⟩⟩
noncomputable def s5_10 : CBox := ⟨⟨(-3337332),(-3336232)⟩,⟨1043015,1044116⟩⟩
noncomputable def s5_11 : CBox := ⟨⟨3204,3232⟩,⟨(-29563),(-29532)⟩⟩
noncomputable def s5_12 : CBox := ⟨⟨194,215⟩,⟨330,351⟩⟩
noncomputable def s5_13 : CBox := ⟨⟨(-15),1⟩,⟨(-22),1⟩⟩
noncomputable def s5_14 : CBox := ⟨⟨(-16),15⟩,⟨(-16),16⟩⟩
noncomputable def s5_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
noncomputable def ans : CBox := ⟨⟨(-40849393463194291847),(-40849303303956151400)⟩,⟨(-56523839493519207727),(-56523749334281067272)⟩⟩
noncomputable def atomAnswer : CBox := ⟨⟨(-831246133391948077729),(-831246133391948055635)⟩,⟨(-183723847546026982605),(-183723847546026960516)⟩⟩
noncomputable def realAnswer : RBox := ⟨(-872095526855242369576),(-872095436695804207035)⟩
end tm0_99_1

end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TaylorControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
open Set
noncomputable def deletedPolynomial (T : ℕ → ℝ → ℝ) (ν d : ℕ) (m u : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (d+1), T (r+ν) m/((r+ν).factorial:ℝ)*u^r
end SharpPlanar

end OAI
end


