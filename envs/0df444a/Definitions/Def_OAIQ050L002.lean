-- Prove2me | Definitions.Def_OAIQ050L002
-- name    : OAIQ050L002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T09:06:36.82058+00:00
-- url     : https://prove2.me/theorems/bae5145b-fce2-4456-af33-8b6a6941aad7
-- title:
--   Definitions bundle OAIQ050L002 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 13 definitions. The definitions and types are `OAI.Laughlin.Certificate.candidateY_14`, `OAI.Laughlin.Certificate.candidateY_16`, `OAI.Laughlin.Certificate.candidateY_17`, `OAI.Laughlin.Certificate.candidateY_18`, `OAI.Laughlin.Certificate.candidateY_19`, `OAI.Laughlin.Certificate.candidateY_20`, `OAI.Laughlin.Certificate.candidateY_21`, `OAI.Laughlin.Certificate.candidateZ_10`, `OAI.Laughlin.Certificate.candidateZ_11`, `OAI.Laughlin.Certificate.candidateZ_12`, `OAI.Laughlin.Certificate.candidateZ_13`, `OAI.Laughlin.Certificate.copyLabel`, `OAI.Laughlin.Fock.RowLevel`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Laughlin_FiniteFlux_Data10`, `Laughlin_FiniteFlux_Data11`, `Laughlin_FiniteFlux_Data12`, `Laughlin_FiniteFlux_Data13`, `Laughlin_FiniteFlux_Data14`, `Laughlin_FiniteFlux_Data16`, `Laughlin_FiniteFlux_Data17`, `Laughlin_FiniteFlux_Data18`, `Laughlin_FiniteFlux_Data19`, `Laughlin_FiniteFlux_Data20`, `Laughlin_FiniteFlux_Data21`, `Laughlin_FourBody_Basic`, `Laughlin_FourBody_Square`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ050L010` and `OAIQ050L012`; the statements `OAI_Laughlin_Certificate_candidateLDL_10`, `OAI.Laughlin.Certificate.candidateLDL_10_s50`, `OAI_Laughlin_Certificate_candidateLDL_11`, `OAI.Laughlin.Certificate.candidateLDL_11_s50`, `OAI_Laughlin_Certificate_candidateLDL_12`, `OAI.Laughlin.Certificate.candidateLDL_12_s50`, `OAI_Laughlin_Certificate_candidateLDL_13`, `OAI.Laughlin.Certificate.candidateLDL_13_s50`, `OAI_Laughlin_Certificate_candidateLDL_14`, `OAI.Laughlin.Certificate.candidateLDL_14_s50`, `OAI_Laughlin_Certificate_candidateLDL_16`, `OAI.Laughlin.Certificate.candidateLDL_16_s50`, `OAI_Laughlin_Certificate_candidateLDL_17`, `OAI.Laughlin.Certificate.candidateLDL_17_s50`, `OAI_Laughlin_Certificate_candidateLDL_18`, `OAI.Laughlin.Certificate.candidateLDL_18_s50`, `OAI_Laughlin_Certificate_candidateLDL_19`, `OAI.Laughlin.Certificate.candidateLDL_19_s50`, `OAI_Laughlin_Certificate_candidateLDL_20`, `OAI.Laughlin.Certificate.candidateLDL_20_s50`, `OAI_Laughlin_Certificate_candidateLDL_21`, `OAI.Laughlin.Certificate.candidateLDL_21_s50`, `OAI_Laughlin_Certificate_computeLDL_11_5_5`, `OAI.Laughlin.Certificate.computeLDL_11_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_1_5`, `OAI.Laughlin.Certificate.computeLDL_12_1_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_0`, `OAI.Laughlin.Certificate.computeLDL_12_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_1`, `OAI.Laughlin.Certificate.computeLDL_12_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_2`, `OAI.Laughlin.Certificate.computeLDL_12_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_3`, `OAI.Laughlin.Certificate.computeLDL_12_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_4`, `OAI.Laughlin.Certificate.computeLDL_12_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_5`, `OAI.Laughlin.Certificate.computeLDL_12_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_0`, `OAI.Laughlin.Certificate.computeLDL_12_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_1`, `OAI.Laughlin.Certificate.computeLDL_12_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_2`, `OAI.Laughlin.Certificate.computeLDL_12_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_3`, `OAI.Laughlin.Certificate.computeLDL_12_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_4`, `OAI.Laughlin.Certificate.computeLDL_12_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_5`, `OAI.Laughlin.Certificate.computeLDL_12_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_0`, `OAI.Laughlin.Certificate.computeLDL_12_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_1`, `OAI.Laughlin.Certificate.computeLDL_12_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_2`, `OAI.Laughlin.Certificate.computeLDL_12_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_3`, `OAI.Laughlin.Certificate.computeLDL_12_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_4`, `OAI.Laughlin.Certificate.computeLDL_12_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_5`, `OAI.Laughlin.Certificate.computeLDL_12_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_0`, `OAI.Laughlin.Certificate.computeLDL_12_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_1`, `OAI.Laughlin.Certificate.computeLDL_12_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_2`, `OAI.Laughlin.Certificate.computeLDL_12_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_3`, `OAI.Laughlin.Certificate.computeLDL_12_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_4`, `OAI.Laughlin.Certificate.computeLDL_12_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_5`, `OAI.Laughlin.Certificate.computeLDL_12_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_13_1_6`, `OAI.Laughlin.Certificate.computeLDL_13_1_6_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_0`, `OAI.Laughlin.Certificate.computeLDL_13_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_1`, `OAI.Laughlin.Certificate.computeLDL_13_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_2`, `OAI.Laughlin.Certificate.computeLDL_13_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_3`, `OAI.Laughlin.Certificate.computeLDL_13_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_4`, `OAI.Laughlin.Certificate.computeLDL_13_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_5`, `OAI.Laughlin.Certificate.computeLDL_13_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_6`, `OAI.Laughlin.Certificate.computeLDL_13_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_0`, `OAI.Laughlin.Certificate.computeLDL_13_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_1`, `OAI.Laughlin.Certificate.computeLDL_13_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_2`, `OAI.Laughlin.Certificate.computeLDL_13_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_3`, `OAI.Laughlin.Certificate.computeLDL_13_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_4`, `OAI.Laughlin.Certificate.computeLDL_13_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_5`, `OAI.Laughlin.Certificate.computeLDL_13_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_6`, `OAI.Laughlin.Certificate.computeLDL_13_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_0`, `OAI.Laughlin.Certificate.computeLDL_13_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_1`, `OAI.Laughlin.Certificate.computeLDL_13_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_2`, `OAI.Laughlin.Certificate.computeLDL_13_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_3`, `OAI.Laughlin.Certificate.computeLDL_13_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_4`, `OAI.Laughlin.Certificate.computeLDL_13_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_5`, `OAI.Laughlin.Certificate.computeLDL_13_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_6`, `OAI.Laughlin.Certificate.computeLDL_13_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_0`, `OAI.Laughlin.Certificate.computeLDL_13_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_1`, `OAI.Laughlin.Certificate.computeLDL_13_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_2`, `OAI.Laughlin.Certificate.computeLDL_13_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_3`, `OAI.Laughlin.Certificate.computeLDL_13_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_4`, `OAI.Laughlin.Certificate.computeLDL_13_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_5`, `OAI.Laughlin.Certificate.computeLDL_13_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_6`, `OAI.Laughlin.Certificate.computeLDL_13_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_0`, `OAI.Laughlin.Certificate.computeLDL_13_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_1`, `OAI.Laughlin.Certificate.computeLDL_13_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_2`, `OAI.Laughlin.Certificate.computeLDL_13_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_3`, `OAI.Laughlin.Certificate.computeLDL_13_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_4`, `OAI.Laughlin.Certificate.computeLDL_13_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_5`, `OAI.Laughlin.Certificate.computeLDL_13_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_6`, `OAI.Laughlin.Certificate.computeLDL_13_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_14_1_6`, `OAI.Laughlin.Certificate.computeLDL_14_1_6_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_0`, `OAI.Laughlin.Certificate.computeLDL_14_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_1`, `OAI.Laughlin.Certificate.computeLDL_14_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_2`, `OAI.Laughlin.Certificate.computeLDL_14_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_3`, `OAI.Laughlin.Certificate.computeLDL_14_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_4`, `OAI.Laughlin.Certificate.computeLDL_14_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_5`, `OAI.Laughlin.Certificate.computeLDL_14_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_6`, `OAI.Laughlin.Certificate.computeLDL_14_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_0`, `OAI.Laughlin.Certificate.computeLDL_14_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_1`, `OAI.Laughlin.Certificate.computeLDL_14_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_2`, `OAI.Laughlin.Certificate.computeLDL_14_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_3`, `OAI.Laughlin.Certificate.computeLDL_14_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_4`, `OAI.Laughlin.Certificate.computeLDL_14_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_5`, `OAI.Laughlin.Certificate.computeLDL_14_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_6`, `OAI.Laughlin.Certificate.computeLDL_14_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_0`, `OAI.Laughlin.Certificate.computeLDL_14_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_1`, `OAI.Laughlin.Certificate.computeLDL_14_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_2`, `OAI.Laughlin.Certificate.computeLDL_14_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_3`, `OAI.Laughlin.Certificate.computeLDL_14_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_4`, `OAI.Laughlin.Certificate.computeLDL_14_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_5`, `OAI.Laughlin.Certificate.computeLDL_14_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_6`, `OAI.Laughlin.Certificate.computeLDL_14_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_0`, `OAI.Laughlin.Certificate.computeLDL_14_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_1`, `OAI.Laughlin.Certificate.computeLDL_14_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_2`, `OAI.Laughlin.Certificate.computeLDL_14_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_3`, `OAI.Laughlin.Certificate.computeLDL_14_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_4`, `OAI.Laughlin.Certificate.computeLDL_14_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_5`, `OAI.Laughlin.Certificate.computeLDL_14_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_6`, `OAI.Laughlin.Certificate.computeLDL_14_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_0`, `OAI.Laughlin.Certificate.computeLDL_14_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_1`, `OAI.Laughlin.Certificate.computeLDL_14_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_2`, `OAI.Laughlin.Certificate.computeLDL_14_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_3`, `OAI.Laughlin.Certificate.computeLDL_14_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_4`, `OAI.Laughlin.Certificate.computeLDL_14_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_5`, `OAI.Laughlin.Certificate.computeLDL_14_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_6`, `OAI.Laughlin.Certificate.computeLDL_14_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_1_7`, `OAI.Laughlin.Certificate.computeLDL_16_1_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_0`, `OAI.Laughlin.Certificate.computeLDL_16_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_1`, `OAI.Laughlin.Certificate.computeLDL_16_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_2`, `OAI.Laughlin.Certificate.computeLDL_16_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_3`, `OAI.Laughlin.Certificate.computeLDL_16_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_4`, `OAI.Laughlin.Certificate.computeLDL_16_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_5`, `OAI.Laughlin.Certificate.computeLDL_16_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_6`, `OAI.Laughlin.Certificate.computeLDL_16_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_7`, `OAI.Laughlin.Certificate.computeLDL_16_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_0`, `OAI.Laughlin.Certificate.computeLDL_16_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_1`, `OAI.Laughlin.Certificate.computeLDL_16_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_2`, `OAI.Laughlin.Certificate.computeLDL_16_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_3`, `OAI.Laughlin.Certificate.computeLDL_16_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_4`, `OAI.Laughlin.Certificate.computeLDL_16_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_5`, `OAI.Laughlin.Certificate.computeLDL_16_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_6`, `OAI.Laughlin.Certificate.computeLDL_16_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_7`, `OAI.Laughlin.Certificate.computeLDL_16_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_0`, `OAI.Laughlin.Certificate.computeLDL_16_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_1`, `OAI.Laughlin.Certificate.computeLDL_16_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_2`, `OAI.Laughlin.Certificate.computeLDL_16_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_3`, `OAI.Laughlin.Certificate.computeLDL_16_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_4`, `OAI.Laughlin.Certificate.computeLDL_16_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_5`, `OAI.Laughlin.Certificate.computeLDL_16_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_6`, `OAI.Laughlin.Certificate.computeLDL_16_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_7`, `OAI.Laughlin.Certificate.computeLDL_16_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_0`, `OAI.Laughlin.Certificate.computeLDL_16_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_1`, `OAI.Laughlin.Certificate.computeLDL_16_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_2`, `OAI.Laughlin.Certificate.computeLDL_16_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_3`, `OAI.Laughlin.Certificate.computeLDL_16_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_4`, `OAI.Laughlin.Certificate.computeLDL_16_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_5`, `OAI.Laughlin.Certificate.computeLDL_16_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_6`, `OAI.Laughlin.Certificate.computeLDL_16_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_7`, `OAI.Laughlin.Certificate.computeLDL_16_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_0`, `OAI.Laughlin.Certificate.computeLDL_16_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_1`, `OAI.Laughlin.Certificate.computeLDL_16_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_2`, `OAI.Laughlin.Certificate.computeLDL_16_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_3`, `OAI.Laughlin.Certificate.computeLDL_16_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_4`, `OAI.Laughlin.Certificate.computeLDL_16_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_5`, `OAI.Laughlin.Certificate.computeLDL_16_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_6`, `OAI.Laughlin.Certificate.computeLDL_16_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_7`, `OAI.Laughlin.Certificate.computeLDL_16_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_0`, `OAI.Laughlin.Certificate.computeLDL_16_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_1`, `OAI.Laughlin.Certificate.computeLDL_16_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_2`, `OAI.Laughlin.Certificate.computeLDL_16_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_3`, `OAI.Laughlin.Certificate.computeLDL_16_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_4`, `OAI.Laughlin.Certificate.computeLDL_16_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_5`, `OAI.Laughlin.Certificate.computeLDL_16_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_6`, `OAI.Laughlin.Certificate.computeLDL_16_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_7`, `OAI.Laughlin.Certificate.computeLDL_16_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_1_8`, `OAI.Laughlin.Certificate.computeLDL_17_1_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_0`, `OAI.Laughlin.Certificate.computeLDL_17_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_1`, `OAI.Laughlin.Certificate.computeLDL_17_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_2`, `OAI.Laughlin.Certificate.computeLDL_17_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_3`, `OAI.Laughlin.Certificate.computeLDL_17_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_4`, `OAI.Laughlin.Certificate.computeLDL_17_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_5`, `OAI.Laughlin.Certificate.computeLDL_17_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_6`, `OAI.Laughlin.Certificate.computeLDL_17_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_7`, `OAI.Laughlin.Certificate.computeLDL_17_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_8`, `OAI.Laughlin.Certificate.computeLDL_17_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_0`, `OAI.Laughlin.Certificate.computeLDL_17_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_1`, `OAI.Laughlin.Certificate.computeLDL_17_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_2`, `OAI.Laughlin.Certificate.computeLDL_17_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_3`, `OAI.Laughlin.Certificate.computeLDL_17_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_4`, `OAI.Laughlin.Certificate.computeLDL_17_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_5`, `OAI.Laughlin.Certificate.computeLDL_17_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_6`, `OAI.Laughlin.Certificate.computeLDL_17_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_7`, `OAI.Laughlin.Certificate.computeLDL_17_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_8`, `OAI.Laughlin.Certificate.computeLDL_17_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_0`, `OAI.Laughlin.Certificate.computeLDL_17_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_1`, `OAI.Laughlin.Certificate.computeLDL_17_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_2`, `OAI.Laughlin.Certificate.computeLDL_17_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_3`, `OAI.Laughlin.Certificate.computeLDL_17_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_4`, `OAI.Laughlin.Certificate.computeLDL_17_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_5`, `OAI.Laughlin.Certificate.computeLDL_17_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_6`, `OAI.Laughlin.Certificate.computeLDL_17_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_7`, `OAI.Laughlin.Certificate.computeLDL_17_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_8`, `OAI.Laughlin.Certificate.computeLDL_17_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_0`, `OAI.Laughlin.Certificate.computeLDL_17_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_1`, `OAI.Laughlin.Certificate.computeLDL_17_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_2`, `OAI.Laughlin.Certificate.computeLDL_17_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_3`, `OAI.Laughlin.Certificate.computeLDL_17_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_4`, `OAI.Laughlin.Certificate.computeLDL_17_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_5`, `OAI.Laughlin.Certificate.computeLDL_17_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_6`, `OAI.Laughlin.Certificate.computeLDL_17_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_7`, `OAI.Laughlin.Certificate.computeLDL_17_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_8`, `OAI.Laughlin.Certificate.computeLDL_17_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_0`, `OAI.Laughlin.Certificate.computeLDL_17_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_1`, `OAI.Laughlin.Certificate.computeLDL_17_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_2`, `OAI.Laughlin.Certificate.computeLDL_17_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_3`, `OAI.Laughlin.Certificate.computeLDL_17_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_4`, `OAI.Laughlin.Certificate.computeLDL_17_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_5`, `OAI.Laughlin.Certificate.computeLDL_17_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_6`, `OAI.Laughlin.Certificate.computeLDL_17_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_7`, `OAI.Laughlin.Certificate.computeLDL_17_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_8`, `OAI.Laughlin.Certificate.computeLDL_17_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_0`, `OAI.Laughlin.Certificate.computeLDL_17_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_1`, `OAI.Laughlin.Certificate.computeLDL_17_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_2`, `OAI.Laughlin.Certificate.computeLDL_17_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_3`, `OAI.Laughlin.Certificate.computeLDL_17_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_4`, `OAI.Laughlin.Certificate.computeLDL_17_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_5`, `OAI.Laughlin.Certificate.computeLDL_17_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_6`, `OAI.Laughlin.Certificate.computeLDL_17_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_7`, `OAI.Laughlin.Certificate.computeLDL_17_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_8`, `OAI.Laughlin.Certificate.computeLDL_17_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_0`, `OAI.Laughlin.Certificate.computeLDL_17_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_1`, `OAI.Laughlin.Certificate.computeLDL_17_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_2`, `OAI.Laughlin.Certificate.computeLDL_17_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_3`, `OAI.Laughlin.Certificate.computeLDL_17_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_4`, `OAI.Laughlin.Certificate.computeLDL_17_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_5`, `OAI.Laughlin.Certificate.computeLDL_17_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_6`, `OAI.Laughlin.Certificate.computeLDL_17_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_7`, `OAI.Laughlin.Certificate.computeLDL_17_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_8`, `OAI.Laughlin.Certificate.computeLDL_17_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_1_8`, `OAI.Laughlin.Certificate.computeLDL_18_1_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_0`, `OAI.Laughlin.Certificate.computeLDL_18_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_1`, `OAI.Laughlin.Certificate.computeLDL_18_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_2`, `OAI.Laughlin.Certificate.computeLDL_18_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_3`, `OAI.Laughlin.Certificate.computeLDL_18_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_4`, `OAI.Laughlin.Certificate.computeLDL_18_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_5`, `OAI.Laughlin.Certificate.computeLDL_18_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_6`, `OAI.Laughlin.Certificate.computeLDL_18_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_7`, `OAI.Laughlin.Certificate.computeLDL_18_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_8`, `OAI.Laughlin.Certificate.computeLDL_18_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_0`, `OAI.Laughlin.Certificate.computeLDL_18_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_1`, `OAI.Laughlin.Certificate.computeLDL_18_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_2`, `OAI.Laughlin.Certificate.computeLDL_18_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_3`, `OAI.Laughlin.Certificate.computeLDL_18_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_4`, `OAI.Laughlin.Certificate.computeLDL_18_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_5`, `OAI.Laughlin.Certificate.computeLDL_18_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_6`, `OAI.Laughlin.Certificate.computeLDL_18_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_7`, `OAI.Laughlin.Certificate.computeLDL_18_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_8`, `OAI.Laughlin.Certificate.computeLDL_18_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_0`, `OAI.Laughlin.Certificate.computeLDL_18_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_1`, `OAI.Laughlin.Certificate.computeLDL_18_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_2`, `OAI.Laughlin.Certificate.computeLDL_18_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_3`, `OAI.Laughlin.Certificate.computeLDL_18_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_4`, `OAI.Laughlin.Certificate.computeLDL_18_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_5`, `OAI.Laughlin.Certificate.computeLDL_18_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_6`, `OAI.Laughlin.Certificate.computeLDL_18_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_7`, `OAI.Laughlin.Certificate.computeLDL_18_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_8`, `OAI.Laughlin.Certificate.computeLDL_18_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_0`, `OAI.Laughlin.Certificate.computeLDL_18_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_1`, `OAI.Laughlin.Certificate.computeLDL_18_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_2`, `OAI.Laughlin.Certificate.computeLDL_18_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_3`, `OAI.Laughlin.Certificate.computeLDL_18_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_4`, `OAI.Laughlin.Certificate.computeLDL_18_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_5`, `OAI.Laughlin.Certificate.computeLDL_18_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_6`, `OAI.Laughlin.Certificate.computeLDL_18_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_7`, `OAI.Laughlin.Certificate.computeLDL_18_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_8`, `OAI.Laughlin.Certificate.computeLDL_18_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_0`, `OAI.Laughlin.Certificate.computeLDL_18_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_1`, `OAI.Laughlin.Certificate.computeLDL_18_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_2`, `OAI.Laughlin.Certificate.computeLDL_18_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_3`, `OAI.Laughlin.Certificate.computeLDL_18_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_4`, `OAI.Laughlin.Certificate.computeLDL_18_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_5`, `OAI.Laughlin.Certificate.computeLDL_18_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_6`, `OAI.Laughlin.Certificate.computeLDL_18_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_7`, `OAI.Laughlin.Certificate.computeLDL_18_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_8`, `OAI.Laughlin.Certificate.computeLDL_18_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_0`, `OAI.Laughlin.Certificate.computeLDL_18_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_1`, `OAI.Laughlin.Certificate.computeLDL_18_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_2`, `OAI.Laughlin.Certificate.computeLDL_18_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_3`, `OAI.Laughlin.Certificate.computeLDL_18_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_4`, `OAI.Laughlin.Certificate.computeLDL_18_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_5`, `OAI.Laughlin.Certificate.computeLDL_18_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_6`, `OAI.Laughlin.Certificate.computeLDL_18_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_7`, `OAI.Laughlin.Certificate.computeLDL_18_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_8`, `OAI.Laughlin.Certificate.computeLDL_18_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_0`, `OAI.Laughlin.Certificate.computeLDL_18_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_1`, `OAI.Laughlin.Certificate.computeLDL_18_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_2`, `OAI.Laughlin.Certificate.computeLDL_18_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_3`, `OAI.Laughlin.Certificate.computeLDL_18_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_4`, `OAI.Laughlin.Certificate.computeLDL_18_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_5`, `OAI.Laughlin.Certificate.computeLDL_18_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_6`, `OAI.Laughlin.Certificate.computeLDL_18_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_7`, `OAI.Laughlin.Certificate.computeLDL_18_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_8`, `OAI.Laughlin.Certificate.computeLDL_18_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_1_9`, `OAI.Laughlin.Certificate.computeLDL_19_1_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_0`, `OAI.Laughlin.Certificate.computeLDL_19_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_1`, `OAI.Laughlin.Certificate.computeLDL_19_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_2`, `OAI.Laughlin.Certificate.computeLDL_19_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_3`, `OAI.Laughlin.Certificate.computeLDL_19_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_4`, `OAI.Laughlin.Certificate.computeLDL_19_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_5`, `OAI.Laughlin.Certificate.computeLDL_19_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_6`, `OAI.Laughlin.Certificate.computeLDL_19_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_7`, `OAI.Laughlin.Certificate.computeLDL_19_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_8`, `OAI.Laughlin.Certificate.computeLDL_19_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_9`, `OAI.Laughlin.Certificate.computeLDL_19_2_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_0`, `OAI.Laughlin.Certificate.computeLDL_19_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_1`, `OAI.Laughlin.Certificate.computeLDL_19_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_2`, `OAI.Laughlin.Certificate.computeLDL_19_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_3`, `OAI.Laughlin.Certificate.computeLDL_19_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_4`, `OAI.Laughlin.Certificate.computeLDL_19_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_5`, `OAI.Laughlin.Certificate.computeLDL_19_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_6`, `OAI.Laughlin.Certificate.computeLDL_19_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_7`, `OAI.Laughlin.Certificate.computeLDL_19_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_8`, `OAI.Laughlin.Certificate.computeLDL_19_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_9`, `OAI.Laughlin.Certificate.computeLDL_19_3_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_0`, `OAI.Laughlin.Certificate.computeLDL_19_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_1`, `OAI.Laughlin.Certificate.computeLDL_19_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_2`, `OAI.Laughlin.Certificate.computeLDL_19_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_3`, `OAI.Laughlin.Certificate.computeLDL_19_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_4`, `OAI.Laughlin.Certificate.computeLDL_19_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_5`, `OAI.Laughlin.Certificate.computeLDL_19_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_6`, `OAI.Laughlin.Certificate.computeLDL_19_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_7`, `OAI.Laughlin.Certificate.computeLDL_19_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_8`, `OAI.Laughlin.Certificate.computeLDL_19_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_9`, `OAI.Laughlin.Certificate.computeLDL_19_4_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_0`, `OAI.Laughlin.Certificate.computeLDL_19_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_1`, `OAI.Laughlin.Certificate.computeLDL_19_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_2`, `OAI.Laughlin.Certificate.computeLDL_19_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_3`, `OAI.Laughlin.Certificate.computeLDL_19_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_4`, `OAI.Laughlin.Certificate.computeLDL_19_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_5`, `OAI.Laughlin.Certificate.computeLDL_19_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_6`, `OAI.Laughlin.Certificate.computeLDL_19_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_7`, `OAI.Laughlin.Certificate.computeLDL_19_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_8`, `OAI.Laughlin.Certificate.computeLDL_19_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_9`, `OAI.Laughlin.Certificate.computeLDL_19_5_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_0`, `OAI.Laughlin.Certificate.computeLDL_19_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_1`, `OAI.Laughlin.Certificate.computeLDL_19_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_2`, `OAI.Laughlin.Certificate.computeLDL_19_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_3`, `OAI.Laughlin.Certificate.computeLDL_19_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_4`, `OAI.Laughlin.Certificate.computeLDL_19_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_5`, `OAI.Laughlin.Certificate.computeLDL_19_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_6`, `OAI.Laughlin.Certificate.computeLDL_19_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_7`, `OAI.Laughlin.Certificate.computeLDL_19_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_8`, `OAI.Laughlin.Certificate.computeLDL_19_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_9`, `OAI.Laughlin.Certificate.computeLDL_19_6_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_0`, `OAI.Laughlin.Certificate.computeLDL_19_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_1`, `OAI.Laughlin.Certificate.computeLDL_19_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_2`, `OAI.Laughlin.Certificate.computeLDL_19_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_3`, `OAI.Laughlin.Certificate.computeLDL_19_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_4`, `OAI.Laughlin.Certificate.computeLDL_19_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_5`, `OAI.Laughlin.Certificate.computeLDL_19_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_6`, `OAI.Laughlin.Certificate.computeLDL_19_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_7`, `OAI.Laughlin.Certificate.computeLDL_19_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_8`, `OAI.Laughlin.Certificate.computeLDL_19_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_9`, `OAI.Laughlin.Certificate.computeLDL_19_7_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_0`, `OAI.Laughlin.Certificate.computeLDL_19_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_1`, `OAI.Laughlin.Certificate.computeLDL_19_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_2`, `OAI.Laughlin.Certificate.computeLDL_19_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_3`, `OAI.Laughlin.Certificate.computeLDL_19_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_4`, `OAI.Laughlin.Certificate.computeLDL_19_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_5`, `OAI.Laughlin.Certificate.computeLDL_19_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_6`, `OAI.Laughlin.Certificate.computeLDL_19_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_7`, `OAI.Laughlin.Certificate.computeLDL_19_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_8`, `OAI.Laughlin.Certificate.computeLDL_19_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_9`, `OAI.Laughlin.Certificate.computeLDL_19_8_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_0`, `OAI.Laughlin.Certificate.computeLDL_19_9_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_1`, `OAI.Laughlin.Certificate.computeLDL_19_9_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_2`, `OAI.Laughlin.Certificate.computeLDL_19_9_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_3`, `OAI.Laughlin.Certificate.computeLDL_19_9_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_4`, `OAI.Laughlin.Certificate.computeLDL_19_9_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_5`, `OAI.Laughlin.Certificate.computeLDL_19_9_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_6`, `OAI.Laughlin.Certificate.computeLDL_19_9_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_7`, `OAI.Laughlin.Certificate.computeLDL_19_9_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_8`, `OAI.Laughlin.Certificate.computeLDL_19_9_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_9`, `OAI.Laughlin.Certificate.computeLDL_19_9_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_1_9`, `OAI.Laughlin.Certificate.computeLDL_20_1_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_0`, `OAI.Laughlin.Certificate.computeLDL_20_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_1`, `OAI.Laughlin.Certificate.computeLDL_20_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_2`, `OAI.Laughlin.Certificate.computeLDL_20_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_3`, `OAI.Laughlin.Certificate.computeLDL_20_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_4`, `OAI.Laughlin.Certificate.computeLDL_20_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_5`, `OAI.Laughlin.Certificate.computeLDL_20_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_6`, `OAI.Laughlin.Certificate.computeLDL_20_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_7`, `OAI.Laughlin.Certificate.computeLDL_20_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_8`, `OAI.Laughlin.Certificate.computeLDL_20_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_9`, `OAI.Laughlin.Certificate.computeLDL_20_2_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_0`, `OAI.Laughlin.Certificate.computeLDL_20_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_1`, `OAI.Laughlin.Certificate.computeLDL_20_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_2`, `OAI.Laughlin.Certificate.computeLDL_20_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_3`, `OAI.Laughlin.Certificate.computeLDL_20_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_4`, `OAI.Laughlin.Certificate.computeLDL_20_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_5`, `OAI.Laughlin.Certificate.computeLDL_20_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_6`, `OAI.Laughlin.Certificate.computeLDL_20_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_7`, `OAI.Laughlin.Certificate.computeLDL_20_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_8`, `OAI.Laughlin.Certificate.computeLDL_20_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_9`, `OAI.Laughlin.Certificate.computeLDL_20_3_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_0`, `OAI.Laughlin.Certificate.computeLDL_20_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_1`, `OAI.Laughlin.Certificate.computeLDL_20_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_2`, `OAI.Laughlin.Certificate.computeLDL_20_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_3`, `OAI.Laughlin.Certificate.computeLDL_20_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_4`, `OAI.Laughlin.Certificate.computeLDL_20_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_5`, `OAI.Laughlin.Certificate.computeLDL_20_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_6`, `OAI.Laughlin.Certificate.computeLDL_20_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_7`, `OAI.Laughlin.Certificate.computeLDL_20_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_8`, `OAI.Laughlin.Certificate.computeLDL_20_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_9`, `OAI.Laughlin.Certificate.computeLDL_20_4_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_0`, `OAI.Laughlin.Certificate.computeLDL_20_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_1`, `OAI.Laughlin.Certificate.computeLDL_20_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_2`, `OAI.Laughlin.Certificate.computeLDL_20_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_3`, `OAI.Laughlin.Certificate.computeLDL_20_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_4`, `OAI.Laughlin.Certificate.computeLDL_20_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_5`, `OAI.Laughlin.Certificate.computeLDL_20_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_6`, `OAI.Laughlin.Certificate.computeLDL_20_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_7`, `OAI.Laughlin.Certificate.computeLDL_20_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_8`, `OAI.Laughlin.Certificate.computeLDL_20_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_9`, `OAI.Laughlin.Certificate.computeLDL_20_5_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_0`, `OAI.Laughlin.Certificate.computeLDL_20_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_1`, `OAI.Laughlin.Certificate.computeLDL_20_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_2`, `OAI.Laughlin.Certificate.computeLDL_20_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_3`, `OAI.Laughlin.Certificate.computeLDL_20_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_4`, `OAI.Laughlin.Certificate.computeLDL_20_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_5`, `OAI.Laughlin.Certificate.computeLDL_20_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_6`, `OAI.Laughlin.Certificate.computeLDL_20_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_7`, `OAI.Laughlin.Certificate.computeLDL_20_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_8`, `OAI.Laughlin.Certificate.computeLDL_20_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_9`, `OAI.Laughlin.Certificate.computeLDL_20_6_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_0`, `OAI.Laughlin.Certificate.computeLDL_20_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_1`, `OAI.Laughlin.Certificate.computeLDL_20_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_2`, `OAI.Laughlin.Certificate.computeLDL_20_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_3`, `OAI.Laughlin.Certificate.computeLDL_20_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_4`, `OAI.Laughlin.Certificate.computeLDL_20_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_5`, `OAI.Laughlin.Certificate.computeLDL_20_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_6`, `OAI.Laughlin.Certificate.computeLDL_20_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_7`, `OAI.Laughlin.Certificate.computeLDL_20_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_8`, `OAI.Laughlin.Certificate.computeLDL_20_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_9`, `OAI.Laughlin.Certificate.computeLDL_20_7_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_0`, `OAI.Laughlin.Certificate.computeLDL_20_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_1`, `OAI.Laughlin.Certificate.computeLDL_20_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_2`, `OAI.Laughlin.Certificate.computeLDL_20_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_3`, `OAI.Laughlin.Certificate.computeLDL_20_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_4`, `OAI.Laughlin.Certificate.computeLDL_20_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_5`, `OAI.Laughlin.Certificate.computeLDL_20_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_6`, `OAI.Laughlin.Certificate.computeLDL_20_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_7`, `OAI.Laughlin.Certificate.computeLDL_20_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_8`, `OAI.Laughlin.Certificate.computeLDL_20_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_9`, `OAI.Laughlin.Certificate.computeLDL_20_8_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_0`, `OAI.Laughlin.Certificate.computeLDL_20_9_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_1`, `OAI.Laughlin.Certificate.computeLDL_20_9_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_2`, `OAI.Laughlin.Certificate.computeLDL_20_9_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_3`, `OAI.Laughlin.Certificate.computeLDL_20_9_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_4`, `OAI.Laughlin.Certificate.computeLDL_20_9_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_5`, `OAI.Laughlin.Certificate.computeLDL_20_9_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_6`, `OAI.Laughlin.Certificate.computeLDL_20_9_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_7`, `OAI.Laughlin.Certificate.computeLDL_20_9_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_8`, `OAI.Laughlin.Certificate.computeLDL_20_9_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_9`, `OAI.Laughlin.Certificate.computeLDL_20_9_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_0_10`, `OAI.Laughlin.Certificate.computeLDL_21_0_10_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_0`, `OAI.Laughlin.Certificate.computeLDL_21_10_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_1`, `OAI_Laughlin_Certificate_computeLDL_21_10_10`, `OAI.Laughlin.Certificate.computeLDL_21_10_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_10_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_2`, `OAI.Laughlin.Certificate.computeLDL_21_10_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_3`, `OAI.Laughlin.Certificate.computeLDL_21_10_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_4`, `OAI.Laughlin.Certificate.computeLDL_21_10_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_5`, `OAI.Laughlin.Certificate.computeLDL_21_10_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_6`, `OAI.Laughlin.Certificate.computeLDL_21_10_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_7`, `OAI.Laughlin.Certificate.computeLDL_21_10_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_8`, `OAI.Laughlin.Certificate.computeLDL_21_10_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_9`, `OAI.Laughlin.Certificate.computeLDL_21_10_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_1_10`, `OAI.Laughlin.Certificate.computeLDL_21_1_10_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_1`, `OAI_Laughlin_Certificate_computeLDL_21_2_10`, `OAI.Laughlin.Certificate.computeLDL_21_2_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_2`, `OAI.Laughlin.Certificate.computeLDL_21_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_3`, `OAI.Laughlin.Certificate.computeLDL_21_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_4`, `OAI.Laughlin.Certificate.computeLDL_21_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_5`, `OAI.Laughlin.Certificate.computeLDL_21_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_6`, `OAI.Laughlin.Certificate.computeLDL_21_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_7`, `OAI.Laughlin.Certificate.computeLDL_21_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_8`, `OAI.Laughlin.Certificate.computeLDL_21_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_9`, `OAI.Laughlin.Certificate.computeLDL_21_2_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_0`, `OAI.Laughlin.Certificate.computeLDL_21_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_1`, `OAI_Laughlin_Certificate_computeLDL_21_3_10`, `OAI.Laughlin.Certificate.computeLDL_21_3_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_2`, `OAI.Laughlin.Certificate.computeLDL_21_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_3`, `OAI.Laughlin.Certificate.computeLDL_21_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_4`, `OAI.Laughlin.Certificate.computeLDL_21_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_5`, `OAI.Laughlin.Certificate.computeLDL_21_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_6`, `OAI.Laughlin.Certificate.computeLDL_21_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_7`, `OAI.Laughlin.Certificate.computeLDL_21_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_8`, `OAI.Laughlin.Certificate.computeLDL_21_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_9`, `OAI.Laughlin.Certificate.computeLDL_21_3_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_0`, `OAI.Laughlin.Certificate.computeLDL_21_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_1`, `OAI_Laughlin_Certificate_computeLDL_21_4_10`, `OAI.Laughlin.Certificate.computeLDL_21_4_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_2`, `OAI.Laughlin.Certificate.computeLDL_21_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_3`, `OAI.Laughlin.Certificate.computeLDL_21_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_4`, `OAI.Laughlin.Certificate.computeLDL_21_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_5`, `OAI.Laughlin.Certificate.computeLDL_21_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_6`, `OAI.Laughlin.Certificate.computeLDL_21_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_7`, `OAI.Laughlin.Certificate.computeLDL_21_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_8`, `OAI.Laughlin.Certificate.computeLDL_21_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_9`, `OAI.Laughlin.Certificate.computeLDL_21_4_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_0`, `OAI.Laughlin.Certificate.computeLDL_21_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_1`, `OAI_Laughlin_Certificate_computeLDL_21_5_10`, `OAI.Laughlin.Certificate.computeLDL_21_5_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_2`, `OAI.Laughlin.Certificate.computeLDL_21_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_3`, `OAI.Laughlin.Certificate.computeLDL_21_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_4`, `OAI.Laughlin.Certificate.computeLDL_21_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_5`, `OAI.Laughlin.Certificate.computeLDL_21_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_6`, `OAI.Laughlin.Certificate.computeLDL_21_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_7`, `OAI.Laughlin.Certificate.computeLDL_21_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_8`, `OAI.Laughlin.Certificate.computeLDL_21_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_9`, `OAI.Laughlin.Certificate.computeLDL_21_5_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_0`, `OAI.Laughlin.Certificate.computeLDL_21_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_1`, `OAI_Laughlin_Certificate_computeLDL_21_6_10`, `OAI.Laughlin.Certificate.computeLDL_21_6_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_2`, `OAI.Laughlin.Certificate.computeLDL_21_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_3`, `OAI.Laughlin.Certificate.computeLDL_21_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_4`, `OAI.Laughlin.Certificate.computeLDL_21_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_5`, `OAI.Laughlin.Certificate.computeLDL_21_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_6`, `OAI.Laughlin.Certificate.computeLDL_21_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_7`, `OAI.Laughlin.Certificate.computeLDL_21_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_8`, `OAI.Laughlin.Certificate.computeLDL_21_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_9`, `OAI.Laughlin.Certificate.computeLDL_21_6_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_0`, `OAI.Laughlin.Certificate.computeLDL_21_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_1`, `OAI_Laughlin_Certificate_computeLDL_21_7_10`, `OAI.Laughlin.Certificate.computeLDL_21_7_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_2`, `OAI.Laughlin.Certificate.computeLDL_21_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_3`, `OAI.Laughlin.Certificate.computeLDL_21_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_4`, `OAI.Laughlin.Certificate.computeLDL_21_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_5`, `OAI.Laughlin.Certificate.computeLDL_21_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_6`, `OAI.Laughlin.Certificate.computeLDL_21_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_7`, `OAI.Laughlin.Certificate.computeLDL_21_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_8`, `OAI.Laughlin.Certificate.computeLDL_21_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_9`, `OAI.Laughlin.Certificate.computeLDL_21_7_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_0`, `OAI.Laughlin.Certificate.computeLDL_21_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_1`, `OAI_Laughlin_Certificate_computeLDL_21_8_10`, `OAI.Laughlin.Certificate.computeLDL_21_8_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_2`, `OAI.Laughlin.Certificate.computeLDL_21_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_3`, `OAI.Laughlin.Certificate.computeLDL_21_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_4`, `OAI.Laughlin.Certificate.computeLDL_21_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_5`, `OAI.Laughlin.Certificate.computeLDL_21_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_6`, `OAI.Laughlin.Certificate.computeLDL_21_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_7`, `OAI.Laughlin.Certificate.computeLDL_21_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_8`, `OAI.Laughlin.Certificate.computeLDL_21_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_9`, `OAI.Laughlin.Certificate.computeLDL_21_8_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_0`, `OAI.Laughlin.Certificate.computeLDL_21_9_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_1`, `OAI_Laughlin_Certificate_computeLDL_21_9_10`, `OAI.Laughlin.Certificate.computeLDL_21_9_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_9_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_2`, `OAI.Laughlin.Certificate.computeLDL_21_9_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_3`, `OAI.Laughlin.Certificate.computeLDL_21_9_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_4`, `OAI.Laughlin.Certificate.computeLDL_21_9_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_5`, `OAI.Laughlin.Certificate.computeLDL_21_9_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_6`, `OAI.Laughlin.Certificate.computeLDL_21_9_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_7`, `OAI.Laughlin.Certificate.computeLDL_21_9_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_8`, `OAI.Laughlin.Certificate.computeLDL_21_9_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_9`, `OAI.Laughlin.Certificate.computeLDL_21_9_9_s50`, `OAI_Laughlin_Fock_fourCopyForm_scaled_haar`, `OAI_Laughlin_Fock_physical_fock_square_eventually_sharp`, `OAI_Laughlin_Fock_physical_fourBody_total_haar_transfer`, `OAI_Laughlin_Fock_source_fourBody_physical_L` and `OAI_Laughlin_Spin_source_threeBody_physical_traces_strict_eventually`; the proofs of `OAI_Laughlin_Certificate_candidateLDL_10`, `OAI.Laughlin.Certificate.candidateLDL_10_s50`, `OAI_Laughlin_Certificate_candidateLDL_11`, `OAI.Laughlin.Certificate.candidateLDL_11_s50`, `OAI_Laughlin_Certificate_candidateLDL_12`, `OAI.Laughlin.Certificate.candidateLDL_12_s50`, `OAI_Laughlin_Certificate_candidateLDL_13`, `OAI.Laughlin.Certificate.candidateLDL_13_s50`, `OAI_Laughlin_Certificate_candidateLDL_14`, `OAI.Laughlin.Certificate.candidateLDL_14_s50`, `OAI_Laughlin_Certificate_candidateLDL_16`, `OAI.Laughlin.Certificate.candidateLDL_16_s50`, `OAI_Laughlin_Certificate_candidateLDL_17`, `OAI.Laughlin.Certificate.candidateLDL_17_s50`, `OAI_Laughlin_Certificate_candidateLDL_18`, `OAI.Laughlin.Certificate.candidateLDL_18_s50`, `OAI_Laughlin_Certificate_candidateLDL_19`, `OAI.Laughlin.Certificate.candidateLDL_19_s50`, `OAI_Laughlin_Certificate_candidateLDL_20`, `OAI.Laughlin.Certificate.candidateLDL_20_s50`, `OAI_Laughlin_Certificate_candidateLDL_21`, `OAI.Laughlin.Certificate.candidateLDL_21_s50`, `OAI_Laughlin_Certificate_computeLDL_11_5_5`, `OAI.Laughlin.Certificate.computeLDL_11_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_1_5`, `OAI.Laughlin.Certificate.computeLDL_12_1_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_0`, `OAI.Laughlin.Certificate.computeLDL_12_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_1`, `OAI.Laughlin.Certificate.computeLDL_12_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_2`, `OAI.Laughlin.Certificate.computeLDL_12_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_3`, `OAI.Laughlin.Certificate.computeLDL_12_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_4`, `OAI.Laughlin.Certificate.computeLDL_12_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_5`, `OAI.Laughlin.Certificate.computeLDL_12_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_0`, `OAI.Laughlin.Certificate.computeLDL_12_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_1`, `OAI.Laughlin.Certificate.computeLDL_12_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_2`, `OAI.Laughlin.Certificate.computeLDL_12_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_3`, `OAI.Laughlin.Certificate.computeLDL_12_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_4`, `OAI.Laughlin.Certificate.computeLDL_12_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_5`, `OAI.Laughlin.Certificate.computeLDL_12_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_0`, `OAI.Laughlin.Certificate.computeLDL_12_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_1`, `OAI.Laughlin.Certificate.computeLDL_12_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_2`, `OAI.Laughlin.Certificate.computeLDL_12_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_3`, `OAI.Laughlin.Certificate.computeLDL_12_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_4`, `OAI.Laughlin.Certificate.computeLDL_12_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_5`, `OAI.Laughlin.Certificate.computeLDL_12_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_0`, `OAI.Laughlin.Certificate.computeLDL_12_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_1`, `OAI.Laughlin.Certificate.computeLDL_12_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_2`, `OAI.Laughlin.Certificate.computeLDL_12_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_3`, `OAI.Laughlin.Certificate.computeLDL_12_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_4`, `OAI.Laughlin.Certificate.computeLDL_12_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_5`, `OAI.Laughlin.Certificate.computeLDL_12_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_13_1_6`, `OAI.Laughlin.Certificate.computeLDL_13_1_6_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_0`, `OAI.Laughlin.Certificate.computeLDL_13_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_1`, `OAI.Laughlin.Certificate.computeLDL_13_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_2`, `OAI.Laughlin.Certificate.computeLDL_13_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_3`, `OAI.Laughlin.Certificate.computeLDL_13_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_4`, `OAI.Laughlin.Certificate.computeLDL_13_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_5`, `OAI.Laughlin.Certificate.computeLDL_13_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_6`, `OAI.Laughlin.Certificate.computeLDL_13_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_0`, `OAI.Laughlin.Certificate.computeLDL_13_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_1`, `OAI.Laughlin.Certificate.computeLDL_13_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_2`, `OAI.Laughlin.Certificate.computeLDL_13_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_3`, `OAI.Laughlin.Certificate.computeLDL_13_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_4`, `OAI.Laughlin.Certificate.computeLDL_13_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_5`, `OAI.Laughlin.Certificate.computeLDL_13_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_6`, `OAI.Laughlin.Certificate.computeLDL_13_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_0`, `OAI.Laughlin.Certificate.computeLDL_13_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_1`, `OAI.Laughlin.Certificate.computeLDL_13_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_2`, `OAI.Laughlin.Certificate.computeLDL_13_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_3`, `OAI.Laughlin.Certificate.computeLDL_13_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_4`, `OAI.Laughlin.Certificate.computeLDL_13_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_5`, `OAI.Laughlin.Certificate.computeLDL_13_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_6`, `OAI.Laughlin.Certificate.computeLDL_13_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_0`, `OAI.Laughlin.Certificate.computeLDL_13_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_1`, `OAI.Laughlin.Certificate.computeLDL_13_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_2`, `OAI.Laughlin.Certificate.computeLDL_13_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_3`, `OAI.Laughlin.Certificate.computeLDL_13_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_4`, `OAI.Laughlin.Certificate.computeLDL_13_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_5`, `OAI.Laughlin.Certificate.computeLDL_13_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_6`, `OAI.Laughlin.Certificate.computeLDL_13_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_0`, `OAI.Laughlin.Certificate.computeLDL_13_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_1`, `OAI.Laughlin.Certificate.computeLDL_13_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_2`, `OAI.Laughlin.Certificate.computeLDL_13_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_3`, `OAI.Laughlin.Certificate.computeLDL_13_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_4`, `OAI.Laughlin.Certificate.computeLDL_13_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_5`, `OAI.Laughlin.Certificate.computeLDL_13_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_6`, `OAI.Laughlin.Certificate.computeLDL_13_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_14_1_6`, `OAI.Laughlin.Certificate.computeLDL_14_1_6_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_0`, `OAI.Laughlin.Certificate.computeLDL_14_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_1`, `OAI.Laughlin.Certificate.computeLDL_14_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_2`, `OAI.Laughlin.Certificate.computeLDL_14_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_3`, `OAI.Laughlin.Certificate.computeLDL_14_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_4`, `OAI.Laughlin.Certificate.computeLDL_14_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_5`, `OAI.Laughlin.Certificate.computeLDL_14_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_6`, `OAI.Laughlin.Certificate.computeLDL_14_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_0`, `OAI.Laughlin.Certificate.computeLDL_14_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_1`, `OAI.Laughlin.Certificate.computeLDL_14_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_2`, `OAI.Laughlin.Certificate.computeLDL_14_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_3`, `OAI.Laughlin.Certificate.computeLDL_14_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_4`, `OAI.Laughlin.Certificate.computeLDL_14_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_5`, `OAI.Laughlin.Certificate.computeLDL_14_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_6`, `OAI.Laughlin.Certificate.computeLDL_14_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_0`, `OAI.Laughlin.Certificate.computeLDL_14_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_1`, `OAI.Laughlin.Certificate.computeLDL_14_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_2`, `OAI.Laughlin.Certificate.computeLDL_14_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_3`, `OAI.Laughlin.Certificate.computeLDL_14_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_4`, `OAI.Laughlin.Certificate.computeLDL_14_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_5`, `OAI.Laughlin.Certificate.computeLDL_14_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_6`, `OAI.Laughlin.Certificate.computeLDL_14_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_0`, `OAI.Laughlin.Certificate.computeLDL_14_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_1`, `OAI.Laughlin.Certificate.computeLDL_14_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_2`, `OAI.Laughlin.Certificate.computeLDL_14_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_3`, `OAI.Laughlin.Certificate.computeLDL_14_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_4`, `OAI.Laughlin.Certificate.computeLDL_14_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_5`, `OAI.Laughlin.Certificate.computeLDL_14_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_6`, `OAI.Laughlin.Certificate.computeLDL_14_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_0`, `OAI.Laughlin.Certificate.computeLDL_14_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_1`, `OAI.Laughlin.Certificate.computeLDL_14_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_2`, `OAI.Laughlin.Certificate.computeLDL_14_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_3`, `OAI.Laughlin.Certificate.computeLDL_14_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_4`, `OAI.Laughlin.Certificate.computeLDL_14_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_5`, `OAI.Laughlin.Certificate.computeLDL_14_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_6`, `OAI.Laughlin.Certificate.computeLDL_14_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_1_7`, `OAI.Laughlin.Certificate.computeLDL_16_1_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_0`, `OAI.Laughlin.Certificate.computeLDL_16_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_1`, `OAI.Laughlin.Certificate.computeLDL_16_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_2`, `OAI.Laughlin.Certificate.computeLDL_16_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_3`, `OAI.Laughlin.Certificate.computeLDL_16_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_4`, `OAI.Laughlin.Certificate.computeLDL_16_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_5`, `OAI.Laughlin.Certificate.computeLDL_16_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_6`, `OAI.Laughlin.Certificate.computeLDL_16_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_7`, `OAI.Laughlin.Certificate.computeLDL_16_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_0`, `OAI.Laughlin.Certificate.computeLDL_16_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_1`, `OAI.Laughlin.Certificate.computeLDL_16_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_2`, `OAI.Laughlin.Certificate.computeLDL_16_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_3`, `OAI.Laughlin.Certificate.computeLDL_16_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_4`, `OAI.Laughlin.Certificate.computeLDL_16_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_5`, `OAI.Laughlin.Certificate.computeLDL_16_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_6`, `OAI.Laughlin.Certificate.computeLDL_16_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_7`, `OAI.Laughlin.Certificate.computeLDL_16_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_0`, `OAI.Laughlin.Certificate.computeLDL_16_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_1`, `OAI.Laughlin.Certificate.computeLDL_16_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_2`, `OAI.Laughlin.Certificate.computeLDL_16_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_3`, `OAI.Laughlin.Certificate.computeLDL_16_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_4`, `OAI.Laughlin.Certificate.computeLDL_16_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_5`, `OAI.Laughlin.Certificate.computeLDL_16_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_6`, `OAI.Laughlin.Certificate.computeLDL_16_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_7`, `OAI.Laughlin.Certificate.computeLDL_16_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_0`, `OAI.Laughlin.Certificate.computeLDL_16_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_1`, `OAI.Laughlin.Certificate.computeLDL_16_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_2`, `OAI.Laughlin.Certificate.computeLDL_16_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_3`, `OAI.Laughlin.Certificate.computeLDL_16_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_4`, `OAI.Laughlin.Certificate.computeLDL_16_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_5`, `OAI.Laughlin.Certificate.computeLDL_16_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_6`, `OAI.Laughlin.Certificate.computeLDL_16_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_7`, `OAI.Laughlin.Certificate.computeLDL_16_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_0`, `OAI.Laughlin.Certificate.computeLDL_16_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_1`, `OAI.Laughlin.Certificate.computeLDL_16_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_2`, `OAI.Laughlin.Certificate.computeLDL_16_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_3`, `OAI.Laughlin.Certificate.computeLDL_16_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_4`, `OAI.Laughlin.Certificate.computeLDL_16_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_5`, `OAI.Laughlin.Certificate.computeLDL_16_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_6`, `OAI.Laughlin.Certificate.computeLDL_16_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_7`, `OAI.Laughlin.Certificate.computeLDL_16_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_0`, `OAI.Laughlin.Certificate.computeLDL_16_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_1`, `OAI.Laughlin.Certificate.computeLDL_16_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_2`, `OAI.Laughlin.Certificate.computeLDL_16_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_3`, `OAI.Laughlin.Certificate.computeLDL_16_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_4`, `OAI.Laughlin.Certificate.computeLDL_16_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_5`, `OAI.Laughlin.Certificate.computeLDL_16_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_6`, `OAI.Laughlin.Certificate.computeLDL_16_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_7`, `OAI.Laughlin.Certificate.computeLDL_16_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_1_8`, `OAI.Laughlin.Certificate.computeLDL_17_1_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_0`, `OAI.Laughlin.Certificate.computeLDL_17_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_1`, `OAI.Laughlin.Certificate.computeLDL_17_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_2`, `OAI.Laughlin.Certificate.computeLDL_17_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_3`, `OAI.Laughlin.Certificate.computeLDL_17_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_4`, `OAI.Laughlin.Certificate.computeLDL_17_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_5`, `OAI.Laughlin.Certificate.computeLDL_17_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_6`, `OAI.Laughlin.Certificate.computeLDL_17_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_7`, `OAI.Laughlin.Certificate.computeLDL_17_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_8`, `OAI.Laughlin.Certificate.computeLDL_17_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_0`, `OAI.Laughlin.Certificate.computeLDL_17_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_1`, `OAI.Laughlin.Certificate.computeLDL_17_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_2`, `OAI.Laughlin.Certificate.computeLDL_17_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_3`, `OAI.Laughlin.Certificate.computeLDL_17_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_4`, `OAI.Laughlin.Certificate.computeLDL_17_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_5`, `OAI.Laughlin.Certificate.computeLDL_17_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_6`, `OAI.Laughlin.Certificate.computeLDL_17_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_7`, `OAI.Laughlin.Certificate.computeLDL_17_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_8`, `OAI.Laughlin.Certificate.computeLDL_17_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_0`, `OAI.Laughlin.Certificate.computeLDL_17_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_1`, `OAI.Laughlin.Certificate.computeLDL_17_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_2`, `OAI.Laughlin.Certificate.computeLDL_17_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_3`, `OAI.Laughlin.Certificate.computeLDL_17_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_4`, `OAI.Laughlin.Certificate.computeLDL_17_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_5`, `OAI.Laughlin.Certificate.computeLDL_17_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_6`, `OAI.Laughlin.Certificate.computeLDL_17_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_7`, `OAI.Laughlin.Certificate.computeLDL_17_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_8`, `OAI.Laughlin.Certificate.computeLDL_17_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_0`, `OAI.Laughlin.Certificate.computeLDL_17_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_1`, `OAI.Laughlin.Certificate.computeLDL_17_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_2`, `OAI.Laughlin.Certificate.computeLDL_17_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_3`, `OAI.Laughlin.Certificate.computeLDL_17_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_4`, `OAI.Laughlin.Certificate.computeLDL_17_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_5`, `OAI.Laughlin.Certificate.computeLDL_17_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_6`, `OAI.Laughlin.Certificate.computeLDL_17_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_7`, `OAI.Laughlin.Certificate.computeLDL_17_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_8`, `OAI.Laughlin.Certificate.computeLDL_17_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_0`, `OAI.Laughlin.Certificate.computeLDL_17_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_1`, `OAI.Laughlin.Certificate.computeLDL_17_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_2`, `OAI.Laughlin.Certificate.computeLDL_17_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_3`, `OAI.Laughlin.Certificate.computeLDL_17_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_4`, `OAI.Laughlin.Certificate.computeLDL_17_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_5`, `OAI.Laughlin.Certificate.computeLDL_17_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_6`, `OAI.Laughlin.Certificate.computeLDL_17_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_7`, `OAI.Laughlin.Certificate.computeLDL_17_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_8`, `OAI.Laughlin.Certificate.computeLDL_17_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_0`, `OAI.Laughlin.Certificate.computeLDL_17_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_1`, `OAI.Laughlin.Certificate.computeLDL_17_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_2`, `OAI.Laughlin.Certificate.computeLDL_17_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_3`, `OAI.Laughlin.Certificate.computeLDL_17_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_4`, `OAI.Laughlin.Certificate.computeLDL_17_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_5`, `OAI.Laughlin.Certificate.computeLDL_17_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_6`, `OAI.Laughlin.Certificate.computeLDL_17_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_7`, `OAI.Laughlin.Certificate.computeLDL_17_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_8`, `OAI.Laughlin.Certificate.computeLDL_17_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_0`, `OAI.Laughlin.Certificate.computeLDL_17_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_1`, `OAI.Laughlin.Certificate.computeLDL_17_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_2`, `OAI.Laughlin.Certificate.computeLDL_17_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_3`, `OAI.Laughlin.Certificate.computeLDL_17_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_4`, `OAI.Laughlin.Certificate.computeLDL_17_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_5`, `OAI.Laughlin.Certificate.computeLDL_17_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_6`, `OAI.Laughlin.Certificate.computeLDL_17_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_7`, `OAI.Laughlin.Certificate.computeLDL_17_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_8`, `OAI.Laughlin.Certificate.computeLDL_17_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_1_8`, `OAI.Laughlin.Certificate.computeLDL_18_1_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_0`, `OAI.Laughlin.Certificate.computeLDL_18_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_1`, `OAI.Laughlin.Certificate.computeLDL_18_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_2`, `OAI.Laughlin.Certificate.computeLDL_18_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_3`, `OAI.Laughlin.Certificate.computeLDL_18_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_4`, `OAI.Laughlin.Certificate.computeLDL_18_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_5`, `OAI.Laughlin.Certificate.computeLDL_18_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_6`, `OAI.Laughlin.Certificate.computeLDL_18_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_7`, `OAI.Laughlin.Certificate.computeLDL_18_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_8`, `OAI.Laughlin.Certificate.computeLDL_18_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_0`, `OAI.Laughlin.Certificate.computeLDL_18_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_1`, `OAI.Laughlin.Certificate.computeLDL_18_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_2`, `OAI.Laughlin.Certificate.computeLDL_18_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_3`, `OAI.Laughlin.Certificate.computeLDL_18_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_4`, `OAI.Laughlin.Certificate.computeLDL_18_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_5`, `OAI.Laughlin.Certificate.computeLDL_18_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_6`, `OAI.Laughlin.Certificate.computeLDL_18_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_7`, `OAI.Laughlin.Certificate.computeLDL_18_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_8`, `OAI.Laughlin.Certificate.computeLDL_18_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_0`, `OAI.Laughlin.Certificate.computeLDL_18_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_1`, `OAI.Laughlin.Certificate.computeLDL_18_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_2`, `OAI.Laughlin.Certificate.computeLDL_18_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_3`, `OAI.Laughlin.Certificate.computeLDL_18_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_4`, `OAI.Laughlin.Certificate.computeLDL_18_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_5`, `OAI.Laughlin.Certificate.computeLDL_18_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_6`, `OAI.Laughlin.Certificate.computeLDL_18_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_7`, `OAI.Laughlin.Certificate.computeLDL_18_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_8`, `OAI.Laughlin.Certificate.computeLDL_18_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_0`, `OAI.Laughlin.Certificate.computeLDL_18_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_1`, `OAI.Laughlin.Certificate.computeLDL_18_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_2`, `OAI.Laughlin.Certificate.computeLDL_18_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_3`, `OAI.Laughlin.Certificate.computeLDL_18_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_4`, `OAI.Laughlin.Certificate.computeLDL_18_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_5`, `OAI.Laughlin.Certificate.computeLDL_18_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_6`, `OAI.Laughlin.Certificate.computeLDL_18_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_7`, `OAI.Laughlin.Certificate.computeLDL_18_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_8`, `OAI.Laughlin.Certificate.computeLDL_18_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_0`, `OAI.Laughlin.Certificate.computeLDL_18_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_1`, `OAI.Laughlin.Certificate.computeLDL_18_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_2`, `OAI.Laughlin.Certificate.computeLDL_18_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_3`, `OAI.Laughlin.Certificate.computeLDL_18_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_4`, `OAI.Laughlin.Certificate.computeLDL_18_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_5`, `OAI.Laughlin.Certificate.computeLDL_18_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_6`, `OAI.Laughlin.Certificate.computeLDL_18_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_7`, `OAI.Laughlin.Certificate.computeLDL_18_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_8`, `OAI.Laughlin.Certificate.computeLDL_18_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_0`, `OAI.Laughlin.Certificate.computeLDL_18_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_1`, `OAI.Laughlin.Certificate.computeLDL_18_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_2`, `OAI.Laughlin.Certificate.computeLDL_18_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_3`, `OAI.Laughlin.Certificate.computeLDL_18_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_4`, `OAI.Laughlin.Certificate.computeLDL_18_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_5`, `OAI.Laughlin.Certificate.computeLDL_18_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_6`, `OAI.Laughlin.Certificate.computeLDL_18_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_7`, `OAI.Laughlin.Certificate.computeLDL_18_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_8`, `OAI.Laughlin.Certificate.computeLDL_18_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_0`, `OAI.Laughlin.Certificate.computeLDL_18_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_1`, `OAI.Laughlin.Certificate.computeLDL_18_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_2`, `OAI.Laughlin.Certificate.computeLDL_18_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_3`, `OAI.Laughlin.Certificate.computeLDL_18_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_4`, `OAI.Laughlin.Certificate.computeLDL_18_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_5`, `OAI.Laughlin.Certificate.computeLDL_18_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_6`, `OAI.Laughlin.Certificate.computeLDL_18_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_7`, `OAI.Laughlin.Certificate.computeLDL_18_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_8`, `OAI.Laughlin.Certificate.computeLDL_18_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_1_9`, `OAI.Laughlin.Certificate.computeLDL_19_1_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_0`, `OAI.Laughlin.Certificate.computeLDL_19_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_1`, `OAI.Laughlin.Certificate.computeLDL_19_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_2`, `OAI.Laughlin.Certificate.computeLDL_19_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_3`, `OAI.Laughlin.Certificate.computeLDL_19_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_4`, `OAI.Laughlin.Certificate.computeLDL_19_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_5`, `OAI.Laughlin.Certificate.computeLDL_19_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_6`, `OAI.Laughlin.Certificate.computeLDL_19_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_7`, `OAI.Laughlin.Certificate.computeLDL_19_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_8`, `OAI.Laughlin.Certificate.computeLDL_19_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_9`, `OAI.Laughlin.Certificate.computeLDL_19_2_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_0`, `OAI.Laughlin.Certificate.computeLDL_19_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_1`, `OAI.Laughlin.Certificate.computeLDL_19_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_2`, `OAI.Laughlin.Certificate.computeLDL_19_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_3`, `OAI.Laughlin.Certificate.computeLDL_19_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_4`, `OAI.Laughlin.Certificate.computeLDL_19_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_5`, `OAI.Laughlin.Certificate.computeLDL_19_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_6`, `OAI.Laughlin.Certificate.computeLDL_19_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_7`, `OAI.Laughlin.Certificate.computeLDL_19_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_8`, `OAI.Laughlin.Certificate.computeLDL_19_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_9`, `OAI.Laughlin.Certificate.computeLDL_19_3_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_0`, `OAI.Laughlin.Certificate.computeLDL_19_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_1`, `OAI.Laughlin.Certificate.computeLDL_19_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_2`, `OAI.Laughlin.Certificate.computeLDL_19_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_3`, `OAI.Laughlin.Certificate.computeLDL_19_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_4`, `OAI.Laughlin.Certificate.computeLDL_19_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_5`, `OAI.Laughlin.Certificate.computeLDL_19_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_6`, `OAI.Laughlin.Certificate.computeLDL_19_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_7`, `OAI.Laughlin.Certificate.computeLDL_19_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_8`, `OAI.Laughlin.Certificate.computeLDL_19_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_9`, `OAI.Laughlin.Certificate.computeLDL_19_4_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_0`, `OAI.Laughlin.Certificate.computeLDL_19_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_1`, `OAI.Laughlin.Certificate.computeLDL_19_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_2`, `OAI.Laughlin.Certificate.computeLDL_19_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_3`, `OAI.Laughlin.Certificate.computeLDL_19_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_4`, `OAI.Laughlin.Certificate.computeLDL_19_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_5`, `OAI.Laughlin.Certificate.computeLDL_19_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_6`, `OAI.Laughlin.Certificate.computeLDL_19_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_7`, `OAI.Laughlin.Certificate.computeLDL_19_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_8`, `OAI.Laughlin.Certificate.computeLDL_19_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_9`, `OAI.Laughlin.Certificate.computeLDL_19_5_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_0`, `OAI.Laughlin.Certificate.computeLDL_19_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_1`, `OAI.Laughlin.Certificate.computeLDL_19_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_2`, `OAI.Laughlin.Certificate.computeLDL_19_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_3`, `OAI.Laughlin.Certificate.computeLDL_19_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_4`, `OAI.Laughlin.Certificate.computeLDL_19_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_5`, `OAI.Laughlin.Certificate.computeLDL_19_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_6`, `OAI.Laughlin.Certificate.computeLDL_19_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_7`, `OAI.Laughlin.Certificate.computeLDL_19_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_8`, `OAI.Laughlin.Certificate.computeLDL_19_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_9`, `OAI.Laughlin.Certificate.computeLDL_19_6_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_0`, `OAI.Laughlin.Certificate.computeLDL_19_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_1`, `OAI.Laughlin.Certificate.computeLDL_19_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_2`, `OAI.Laughlin.Certificate.computeLDL_19_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_3`, `OAI.Laughlin.Certificate.computeLDL_19_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_4`, `OAI.Laughlin.Certificate.computeLDL_19_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_5`, `OAI.Laughlin.Certificate.computeLDL_19_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_6`, `OAI.Laughlin.Certificate.computeLDL_19_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_7`, `OAI.Laughlin.Certificate.computeLDL_19_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_8`, `OAI.Laughlin.Certificate.computeLDL_19_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_9`, `OAI.Laughlin.Certificate.computeLDL_19_7_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_0`, `OAI.Laughlin.Certificate.computeLDL_19_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_1`, `OAI.Laughlin.Certificate.computeLDL_19_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_2`, `OAI.Laughlin.Certificate.computeLDL_19_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_3`, `OAI.Laughlin.Certificate.computeLDL_19_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_4`, `OAI.Laughlin.Certificate.computeLDL_19_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_5`, `OAI.Laughlin.Certificate.computeLDL_19_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_6`, `OAI.Laughlin.Certificate.computeLDL_19_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_7`, `OAI.Laughlin.Certificate.computeLDL_19_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_8`, `OAI.Laughlin.Certificate.computeLDL_19_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_9`, `OAI.Laughlin.Certificate.computeLDL_19_8_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_0`, `OAI.Laughlin.Certificate.computeLDL_19_9_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_1`, `OAI.Laughlin.Certificate.computeLDL_19_9_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_2`, `OAI.Laughlin.Certificate.computeLDL_19_9_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_3`, `OAI.Laughlin.Certificate.computeLDL_19_9_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_4`, `OAI.Laughlin.Certificate.computeLDL_19_9_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_5`, `OAI.Laughlin.Certificate.computeLDL_19_9_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_6`, `OAI.Laughlin.Certificate.computeLDL_19_9_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_7`, `OAI.Laughlin.Certificate.computeLDL_19_9_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_8`, `OAI.Laughlin.Certificate.computeLDL_19_9_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_9`, `OAI.Laughlin.Certificate.computeLDL_19_9_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_1_9`, `OAI.Laughlin.Certificate.computeLDL_20_1_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_0`, `OAI.Laughlin.Certificate.computeLDL_20_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_1`, `OAI.Laughlin.Certificate.computeLDL_20_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_2`, `OAI.Laughlin.Certificate.computeLDL_20_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_3`, `OAI.Laughlin.Certificate.computeLDL_20_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_4`, `OAI.Laughlin.Certificate.computeLDL_20_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_5`, `OAI.Laughlin.Certificate.computeLDL_20_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_6`, `OAI.Laughlin.Certificate.computeLDL_20_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_7`, `OAI.Laughlin.Certificate.computeLDL_20_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_8`, `OAI.Laughlin.Certificate.computeLDL_20_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_9`, `OAI.Laughlin.Certificate.computeLDL_20_2_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_0`, `OAI.Laughlin.Certificate.computeLDL_20_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_1`, `OAI.Laughlin.Certificate.computeLDL_20_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_2`, `OAI.Laughlin.Certificate.computeLDL_20_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_3`, `OAI.Laughlin.Certificate.computeLDL_20_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_4`, `OAI.Laughlin.Certificate.computeLDL_20_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_5`, `OAI.Laughlin.Certificate.computeLDL_20_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_6`, `OAI.Laughlin.Certificate.computeLDL_20_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_7`, `OAI.Laughlin.Certificate.computeLDL_20_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_8`, `OAI.Laughlin.Certificate.computeLDL_20_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_9`, `OAI.Laughlin.Certificate.computeLDL_20_3_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_0`, `OAI.Laughlin.Certificate.computeLDL_20_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_1`, `OAI.Laughlin.Certificate.computeLDL_20_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_2`, `OAI.Laughlin.Certificate.computeLDL_20_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_3`, `OAI.Laughlin.Certificate.computeLDL_20_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_4`, `OAI.Laughlin.Certificate.computeLDL_20_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_5`, `OAI.Laughlin.Certificate.computeLDL_20_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_6`, `OAI.Laughlin.Certificate.computeLDL_20_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_7`, `OAI.Laughlin.Certificate.computeLDL_20_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_8`, `OAI.Laughlin.Certificate.computeLDL_20_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_9`, `OAI.Laughlin.Certificate.computeLDL_20_4_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_0`, `OAI.Laughlin.Certificate.computeLDL_20_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_1`, `OAI.Laughlin.Certificate.computeLDL_20_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_2`, `OAI.Laughlin.Certificate.computeLDL_20_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_3`, `OAI.Laughlin.Certificate.computeLDL_20_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_4`, `OAI.Laughlin.Certificate.computeLDL_20_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_5`, `OAI.Laughlin.Certificate.computeLDL_20_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_6`, `OAI.Laughlin.Certificate.computeLDL_20_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_7`, `OAI.Laughlin.Certificate.computeLDL_20_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_8`, `OAI.Laughlin.Certificate.computeLDL_20_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_9`, `OAI.Laughlin.Certificate.computeLDL_20_5_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_0`, `OAI.Laughlin.Certificate.computeLDL_20_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_1`, `OAI.Laughlin.Certificate.computeLDL_20_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_2`, `OAI.Laughlin.Certificate.computeLDL_20_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_3`, `OAI.Laughlin.Certificate.computeLDL_20_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_4`, `OAI.Laughlin.Certificate.computeLDL_20_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_5`, `OAI.Laughlin.Certificate.computeLDL_20_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_6`, `OAI.Laughlin.Certificate.computeLDL_20_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_7`, `OAI.Laughlin.Certificate.computeLDL_20_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_8`, `OAI.Laughlin.Certificate.computeLDL_20_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_9`, `OAI.Laughlin.Certificate.computeLDL_20_6_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_0`, `OAI.Laughlin.Certificate.computeLDL_20_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_1`, `OAI.Laughlin.Certificate.computeLDL_20_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_2`, `OAI.Laughlin.Certificate.computeLDL_20_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_3`, `OAI.Laughlin.Certificate.computeLDL_20_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_4`, `OAI.Laughlin.Certificate.computeLDL_20_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_5`, `OAI.Laughlin.Certificate.computeLDL_20_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_6`, `OAI.Laughlin.Certificate.computeLDL_20_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_7`, `OAI.Laughlin.Certificate.computeLDL_20_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_8`, `OAI.Laughlin.Certificate.computeLDL_20_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_9`, `OAI.Laughlin.Certificate.computeLDL_20_7_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_0`, `OAI.Laughlin.Certificate.computeLDL_20_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_1`, `OAI.Laughlin.Certificate.computeLDL_20_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_2`, `OAI.Laughlin.Certificate.computeLDL_20_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_3`, `OAI.Laughlin.Certificate.computeLDL_20_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_4`, `OAI.Laughlin.Certificate.computeLDL_20_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_5`, `OAI.Laughlin.Certificate.computeLDL_20_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_6`, `OAI.Laughlin.Certificate.computeLDL_20_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_7`, `OAI.Laughlin.Certificate.computeLDL_20_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_8`, `OAI.Laughlin.Certificate.computeLDL_20_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_9`, `OAI.Laughlin.Certificate.computeLDL_20_8_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_0`, `OAI.Laughlin.Certificate.computeLDL_20_9_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_1`, `OAI.Laughlin.Certificate.computeLDL_20_9_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_2`, `OAI.Laughlin.Certificate.computeLDL_20_9_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_3`, `OAI.Laughlin.Certificate.computeLDL_20_9_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_4`, `OAI.Laughlin.Certificate.computeLDL_20_9_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_5`, `OAI.Laughlin.Certificate.computeLDL_20_9_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_6`, `OAI.Laughlin.Certificate.computeLDL_20_9_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_7`, `OAI.Laughlin.Certificate.computeLDL_20_9_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_8`, `OAI.Laughlin.Certificate.computeLDL_20_9_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_9`, `OAI.Laughlin.Certificate.computeLDL_20_9_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_0_10`, `OAI.Laughlin.Certificate.computeLDL_21_0_10_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_0`, `OAI.Laughlin.Certificate.computeLDL_21_10_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_1`, `OAI_Laughlin_Certificate_computeLDL_21_10_10`, `OAI.Laughlin.Certificate.computeLDL_21_10_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_10_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_2`, `OAI.Laughlin.Certificate.computeLDL_21_10_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_3`, `OAI.Laughlin.Certificate.computeLDL_21_10_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_4`, `OAI.Laughlin.Certificate.computeLDL_21_10_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_5`, `OAI.Laughlin.Certificate.computeLDL_21_10_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_6`, `OAI.Laughlin.Certificate.computeLDL_21_10_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_7`, `OAI.Laughlin.Certificate.computeLDL_21_10_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_8`, `OAI.Laughlin.Certificate.computeLDL_21_10_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_9`, `OAI.Laughlin.Certificate.computeLDL_21_10_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_1_10`, `OAI.Laughlin.Certificate.computeLDL_21_1_10_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_1`, `OAI_Laughlin_Certificate_computeLDL_21_2_10`, `OAI.Laughlin.Certificate.computeLDL_21_2_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_2`, `OAI.Laughlin.Certificate.computeLDL_21_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_3`, `OAI.Laughlin.Certificate.computeLDL_21_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_4`, `OAI.Laughlin.Certificate.computeLDL_21_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_5`, `OAI.Laughlin.Certificate.computeLDL_21_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_6`, `OAI.Laughlin.Certificate.computeLDL_21_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_7`, `OAI.Laughlin.Certificate.computeLDL_21_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_8`, `OAI.Laughlin.Certificate.computeLDL_21_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_9`, `OAI.Laughlin.Certificate.computeLDL_21_2_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_0`, `OAI.Laughlin.Certificate.computeLDL_21_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_1`, `OAI_Laughlin_Certificate_computeLDL_21_3_10`, `OAI.Laughlin.Certificate.computeLDL_21_3_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_2`, `OAI.Laughlin.Certificate.computeLDL_21_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_3`, `OAI.Laughlin.Certificate.computeLDL_21_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_4`, `OAI.Laughlin.Certificate.computeLDL_21_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_5`, `OAI.Laughlin.Certificate.computeLDL_21_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_6`, `OAI.Laughlin.Certificate.computeLDL_21_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_7`, `OAI.Laughlin.Certificate.computeLDL_21_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_8`, `OAI.Laughlin.Certificate.computeLDL_21_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_9`, `OAI.Laughlin.Certificate.computeLDL_21_3_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_0`, `OAI.Laughlin.Certificate.computeLDL_21_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_1`, `OAI_Laughlin_Certificate_computeLDL_21_4_10`, `OAI.Laughlin.Certificate.computeLDL_21_4_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_2`, `OAI.Laughlin.Certificate.computeLDL_21_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_3`, `OAI.Laughlin.Certificate.computeLDL_21_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_4`, `OAI.Laughlin.Certificate.computeLDL_21_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_5`, `OAI.Laughlin.Certificate.computeLDL_21_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_6`, `OAI.Laughlin.Certificate.computeLDL_21_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_7`, `OAI.Laughlin.Certificate.computeLDL_21_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_8`, `OAI.Laughlin.Certificate.computeLDL_21_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_9`, `OAI.Laughlin.Certificate.computeLDL_21_4_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_0`, `OAI.Laughlin.Certificate.computeLDL_21_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_1`, `OAI_Laughlin_Certificate_computeLDL_21_5_10`, `OAI.Laughlin.Certificate.computeLDL_21_5_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_2`, `OAI.Laughlin.Certificate.computeLDL_21_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_3`, `OAI.Laughlin.Certificate.computeLDL_21_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_4`, `OAI.Laughlin.Certificate.computeLDL_21_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_5`, `OAI.Laughlin.Certificate.computeLDL_21_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_6`, `OAI.Laughlin.Certificate.computeLDL_21_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_7`, `OAI.Laughlin.Certificate.computeLDL_21_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_8`, `OAI.Laughlin.Certificate.computeLDL_21_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_9`, `OAI.Laughlin.Certificate.computeLDL_21_5_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_0`, `OAI.Laughlin.Certificate.computeLDL_21_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_1`, `OAI_Laughlin_Certificate_computeLDL_21_6_10`, `OAI.Laughlin.Certificate.computeLDL_21_6_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_2`, `OAI.Laughlin.Certificate.computeLDL_21_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_3`, `OAI.Laughlin.Certificate.computeLDL_21_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_4`, `OAI.Laughlin.Certificate.computeLDL_21_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_5`, `OAI.Laughlin.Certificate.computeLDL_21_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_6`, `OAI.Laughlin.Certificate.computeLDL_21_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_7`, `OAI.Laughlin.Certificate.computeLDL_21_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_8`, `OAI.Laughlin.Certificate.computeLDL_21_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_9`, `OAI.Laughlin.Certificate.computeLDL_21_6_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_0`, `OAI.Laughlin.Certificate.computeLDL_21_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_1`, `OAI_Laughlin_Certificate_computeLDL_21_7_10`, `OAI.Laughlin.Certificate.computeLDL_21_7_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_2`, `OAI.Laughlin.Certificate.computeLDL_21_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_3`, `OAI.Laughlin.Certificate.computeLDL_21_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_4`, `OAI.Laughlin.Certificate.computeLDL_21_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_5`, `OAI.Laughlin.Certificate.computeLDL_21_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_6`, `OAI.Laughlin.Certificate.computeLDL_21_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_7`, `OAI.Laughlin.Certificate.computeLDL_21_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_8`, `OAI.Laughlin.Certificate.computeLDL_21_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_9`, `OAI.Laughlin.Certificate.computeLDL_21_7_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_0`, `OAI.Laughlin.Certificate.computeLDL_21_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_1`, `OAI_Laughlin_Certificate_computeLDL_21_8_10`, `OAI.Laughlin.Certificate.computeLDL_21_8_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_2`, `OAI.Laughlin.Certificate.computeLDL_21_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_3`, `OAI.Laughlin.Certificate.computeLDL_21_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_4`, `OAI.Laughlin.Certificate.computeLDL_21_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_5`, `OAI.Laughlin.Certificate.computeLDL_21_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_6`, `OAI.Laughlin.Certificate.computeLDL_21_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_7`, `OAI.Laughlin.Certificate.computeLDL_21_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_8`, `OAI.Laughlin.Certificate.computeLDL_21_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_9`, `OAI.Laughlin.Certificate.computeLDL_21_8_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_0`, `OAI.Laughlin.Certificate.computeLDL_21_9_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_1`, `OAI_Laughlin_Certificate_computeLDL_21_9_10`, `OAI.Laughlin.Certificate.computeLDL_21_9_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_9_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_2`, `OAI.Laughlin.Certificate.computeLDL_21_9_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_3`, `OAI.Laughlin.Certificate.computeLDL_21_9_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_4`, `OAI.Laughlin.Certificate.computeLDL_21_9_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_5`, `OAI.Laughlin.Certificate.computeLDL_21_9_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_6`, `OAI.Laughlin.Certificate.computeLDL_21_9_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_7`, `OAI.Laughlin.Certificate.computeLDL_21_9_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_8`, `OAI.Laughlin.Certificate.computeLDL_21_9_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_9`, `OAI.Laughlin.Certificate.computeLDL_21_9_9_s50`, `OAI_Laughlin_Certificate_ldl_10`, `OAI_Laughlin_Certificate_ldl_11`, `OAI_Laughlin_Certificate_ldl_9`, `OAI_Laughlin_Fock_complexThreeSpinProjector_eigen`, `OAI_Laughlin_Fock_physical_fock_square_eventually_sharp`, `OAI_Laughlin_Fock_physical_fourBody_total_haar_transfer` and `OAI_Laughlin_Spin_source_fourBody_radical_coefficient`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Data10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
def candidateZ_10 : Matrix (Fin 5) (Fin 5) ℚ := fun i j =>
  match i.val, j.val with
  | 1, 1 => 30240
  | 1, 3 => -22680
  | 1, 4 => 90720
  | 3, 1 => -22680
  | 3, 3 => 17010
  | 3, 4 => -68040
  | 4, 1 => 90720
  | 4, 3 => -68040
  | 4, 4 => 272160
  | _, _ => 0

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Data11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
def candidateZ_11 : Matrix (Fin 6) (Fin 6) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 7257600
  | 0, 4 => -453600
  | 0, 5 => 9979200
  | 1, 1 => 241920
  | 1, 3 => -60480
  | 1, 5 => 2494800
  | 2, 2 => 54000
  | 2, 3 => -75600
  | 2, 4 => 113400
  | 3, 1 => -60480
  | 3, 2 => -75600
  | 3, 3 => 120960
  | 3, 4 => -158760
  | 3, 5 => -623700
  | 4, 0 => -453600
  | 4, 2 => 113400
  | 4, 3 => -158760
  | 4, 4 => 266490
  | 4, 5 => -623700
  | 5, 0 => 9979200
  | 5, 1 => 2494800
  | 5, 3 => -623700
  | 5, 4 => -623700
  | 5, 5 => 39449025
  | _, _ => 0

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Data12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
def candidateZ_12 : Matrix (Fin 6) (Fin 6) ℚ := fun i j =>
  match i.val, j.val with
  | 1, 1 => 2177280
  | 1, 4 => -1088640
  | 1, 5 => 7484400
  | 2, 2 => 604800
  | 2, 3 => -453600
  | 2, 5 => 2494800
  | 3, 2 => -453600
  | 3, 3 => 340200
  | 3, 5 => -1871100
  | 4, 1 => -1088640
  | 4, 4 => 544320
  | 4, 5 => -3742200
  | 5, 1 => 7484400
  | 5, 2 => 2494800
  | 5, 3 => -1871100
  | 5, 4 => -3742200
  | 5, 5 => 36018675
  | _, _ => 0

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Data13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
def candidateZ_13 : Matrix (Fin 7) (Fin 7) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 958003200
  | 0, 5 => -29937600
  | 0, 6 => 972972000
  | 1, 1 => 21772800
  | 1, 4 => -2721600
  | 1, 6 => 291891600
  | 2, 2 => 4838400
  | 2, 3 => -907200
  | 2, 4 => -4082400
  | 2, 5 => 12474000
  | 2, 6 => 48648600
  | 3, 2 => -907200
  | 3, 3 => 453600
  | 3, 6 => -24324300
  | 4, 1 => -2721600
  | 4, 2 => -4082400
  | 4, 4 => 5851440
  | 4, 5 => -16839900
  | 4, 6 => -36486450
  | 5, 0 => -29937600
  | 5, 2 => 12474000
  | 5, 4 => -16839900
  | 5, 5 => 52390800
  | 5, 6 => -30405375
  | 6, 0 => 972972000
  | 6, 1 => 291891600
  | 6, 2 => 48648600
  | 6, 3 => -24324300
  | 6, 4 => -36486450
  | 6, 5 => -30405375
  | 6, 6 => 12411474075/2
  | _, _ => 0

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Data14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
def candidateY_14 : Matrix (Fin 7) (Fin 7) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 165377041672743964897444611/4194304000000000000
  | 0, 1 => -99652836936417746642331957/4194304000000000000
  | 0, 2 => 198343656225197394663337443/8388608000000000000
  | 0, 3 => -10805495312804179528323783/4194304000000000000
  | 0, 4 => 21398938288605875882996397/1048576000000000000
  | 0, 5 => 3160468299521670425437149/104857600000000000
  | 0, 6 => -12750872962864833675394659/524288000000000000
  | 1, 0 => -99652836936417746642331957/4194304000000000000
  | 1, 1 => 23310418524081657499377/524288000000000000
  | 1, 2 => -347065711842922353039231/419430400000000000
  | 1, 3 => -138985253242272601987977/104857600000000000
  | 1, 4 => -567150585351068471238783/131072000000000000
  | 1, 5 => -141724874857705188581763/32768000000000000
  | 1, 6 => -841622022843306152134401/26214400000000000
  | 2, 0 => 198343656225197394663337443/8388608000000000000
  | 2, 1 => -347065711842922353039231/419430400000000000
  | 2, 2 => -948697485826720805007561/1677721600000000000
  | 2, 3 => 1776603855966711095862153/4194304000000000000
  | 2, 4 => 932798387166894000074907/1048576000000000000
  | 2, 5 => 269131392507015595229211/524288000000000000
  | 2, 6 => 6370357421543107418633493/524288000000000000
  | 3, 0 => -10805495312804179528323783/4194304000000000000
  | 3, 1 => -138985253242272601987977/104857600000000000
  | 3, 2 => 1776603855966711095862153/4194304000000000000
  | 3, 3 => -2225592748224580792706397/2097152000000000000
  | 3, 4 => 1701251773125333268329/20971520000000000
  | 3, 5 => -41108078112253038740007/52428800000000000
  | 3, 6 => -1332400286315383367619537/262144000000000000
  | 4, 0 => 21398938288605875882996397/1048576000000000000
  | 4, 1 => -567150585351068471238783/131072000000000000
  | 4, 2 => 932798387166894000074907/1048576000000000000
  | 4, 3 => 1701251773125333268329/20971520000000000
  | 4, 4 => 1451654095595659568163/26214400000000000
  | 4, 5 => 56731873890489317051103/65536000000000000
  | 4, 6 => 702921905295609015979677/65536000000000000
  | 5, 0 => 3160468299521670425437149/104857600000000000
  | 5, 1 => -141724874857705188581763/32768000000000000
  | 5, 2 => 269131392507015595229211/524288000000000000
  | 5, 3 => -41108078112253038740007/52428800000000000
  | 5, 4 => 56731873890489317051103/65536000000000000
  | 5, 5 => 15883626629942625122019/32768000000000000
  | 5, 6 => -304589521531696266272979/32768000000000000
  | 6, 0 => -12750872962864833675394659/524288000000000000
  | 6, 1 => -841622022843306152134401/26214400000000000
  | 6, 2 => 6370357421543107418633493/524288000000000000
  | 6, 3 => -1332400286315383367619537/262144000000000000
  | 6, 4 => 702921905295609015979677/65536000000000000
  | 6, 5 => -304589521531696266272979/32768000000000000
  | 6, 6 => -10250896235928348183825213/32768000000000000
  | _, _ => 0

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Data16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
def candidateY_16 : Matrix (Fin 8) (Fin 8) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => -2276708101299057121652517561/52428800000000000
  | 0, 1 => -39034614015379387104670971/13107200000000000
  | 0, 2 => 78202406241711463127687271/83886080000000000
  | 0, 3 => 23832834670493732956060989/209715200000000000
  | 0, 4 => 22048584820368310367604441/52428800000000000
  | 0, 5 => 2553473034802720354150827/26214400000000000
  | 0, 6 => 108255415269241130506236621/26214400000000000
  | 0, 7 => -41435755574383986458435793/2621440000000000
  | 1, 0 => -39034614015379387104670971/13107200000000000
  | 1, 1 => -374098046732570322778463991/1048576000000000000
  | 1, 2 => 2737552373685628655395239/41943040000000000
  | 1, 3 => 22736583113602023500964129/524288000000000000
  | 1, 4 => 1851780972244557042321633/131072000000000000
  | 1, 5 => 507618379345280460543/1310720000000000
  | 1, 6 => 32584839756386941473215337/65536000000000000
  | 1, 7 => -12977256793584317385992841/6553600000000000
  | 2, 0 => 78202406241711463127687271/83886080000000000
  | 2, 1 => 2737552373685628655395239/41943040000000000
  | 2, 2 => -2533363535515609982834649/83886080000000000
  | 2, 3 => 1549750421445905525422653/209715200000000000
  | 2, 4 => -611154627229412014141701/52428800000000000
  | 2, 5 => -578745616368603039939/41943040000000
  | 2, 6 => -64505141078209101647091/1048576000000000
  | 2, 7 => -99002192076248555811717/524288000000000
  | 3, 0 => 23832834670493732956060989/209715200000000000
  | 3, 1 => 22736583113602023500964129/524288000000000000
  | 3, 2 => 1549750421445905525422653/209715200000000000
  | 3, 3 => -11434119007650938281635057/524288000000000000
  | 3, 4 => 1484433801775108633948569/131072000000000000
  | 3, 5 => 207943103777772680639091/13107200000000000
  | 3, 6 => -8974467290230038089021529/65536000000000000
  | 3, 7 => 4777756237785689667105597/6553600000000000
  | 4, 0 => 22048584820368310367604441/52428800000000000
  | 4, 1 => 1851780972244557042321633/131072000000000000
  | 4, 2 => -611154627229412014141701/52428800000000000
  | 4, 3 => 1484433801775108633948569/131072000000000000
  | 4, 4 => -621920505954394918130013/32768000000000000
  | 4, 5 => -28769175431642817466911/3276800000000000
  | 4, 6 => 1147904288009241919132977/16384000000000000
  | 4, 7 => 68877548037338038801803/1638400000000000
  | 5, 0 => 2553473034802720354150827/26214400000000000
  | 5, 1 => 507618379345280460543/1310720000000000
  | 5, 2 => -578745616368603039939/41943040000000
  | 5, 3 => 207943103777772680639091/13107200000000000
  | 5, 4 => -28769175431642817466911/3276800000000000
  | 5, 5 => -47586420975452552673183/1638400000000000
  | 5, 6 => 189274484540778686288811/1638400000000000
  | 5, 7 => -71581303517955662317887/163840000000000
  | 6, 0 => 108255415269241130506236621/26214400000000000
  | 6, 1 => 32584839756386941473215337/65536000000000000
  | 6, 2 => -64505141078209101647091/1048576000000000
  | 6, 3 => -8974467290230038089021529/65536000000000000
  | 6, 4 => 1147904288009241919132977/16384000000000000
  | 6, 5 => 189274484540778686288811/1638400000000000
  | 6, 6 => -7689933670205658822668289/8192000000000000
  | 6, 7 => 384276867404942369454597/819200000000000
  | 7, 0 => -41435755574383986458435793/2621440000000000
  | 7, 1 => -12977256793584317385992841/6553600000000000
  | 7, 2 => -99002192076248555811717/524288000000000
  | 7, 3 => 4777756237785689667105597/6553600000000000
  | 7, 4 => 68877548037338038801803/1638400000000000
  | 7, 5 => -71581303517955662317887/163840000000000
  | 7, 6 => 384276867404942369454597/819200000000000
  | 7, 7 => -2280462391086995129495481/81920000000000
  | _, _ => 0

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Data17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
def candidateY_17 : Matrix (Fin 9) (Fin 9) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => -27062893468327394953193285367/419430400000000000
  | 0, 1 => -34150355623889743675914477/104857600000000000
  | 0, 2 => 260924265129905899387586721/83886080000000000
  | 0, 3 => -67528457531024325424642053/41943040000000000
  | 0, 4 => -30137637143983305054521403/52428800000000000
  | 0, 5 => 95166999960067286140262373/26214400000000000
  | 0, 6 => -175538440354363800262225677/26214400000000000
  | 0, 7 => 69154353838247955125781933/2621440000000000
  | 1, 0 => -34150355623889743675914477/104857600000000000
  | 1, 1 => -259433233939629173544831711/1048576000000000000
  | 1, 2 => 10972785710270109216153663/104857600000000000
  | 1, 3 => -408068525315759942414781/13107200000000000
  | 1, 4 => 729849806595543331244547/65536000000000000
  | 1, 5 => 11113201543710491752527/13107200000000000
  | 1, 6 => -12885057439514659527475347/32768000000000000
  | 1, 7 => 1281998470570534260875331/1638400000000000
  | 2, 0 => 260924265129905899387586721/83886080000000000
  | 2, 1 => 10972785710270109216153663/104857600000000000
  | 2, 2 => -16291154585525363835188931/83886080000000000
  | 2, 3 => 4351689332062192591003071/41943040000000000
  | 2, 4 => 83301302217472013622717/10485760000000000
  | 2, 5 => -203973650747133817508343/1048576000000000
  | 2, 6 => 16866893128958580992747463/26214400000000000
  | 2, 7 => -99471136192512553900431/104857600000000
  | 3, 0 => -67528457531024325424642053/41943040000000000
  | 3, 1 => -408068525315759942414781/13107200000000000
  | 3, 2 => 4351689332062192591003071/41943040000000000
  | 3, 3 => -1404556469174930860536363/20971520000000000
  | 3, 4 => 138574461584170298662731/26214400000000000
  | 3, 5 => 322312699672503215100579/2621440000000000
  | 3, 6 => -5414374042135146758937267/13107200000000000
  | 3, 7 => 53455862611083189243987/1310720000000000
  | 4, 0 => -30137637143983305054521403/52428800000000000
  | 4, 1 => 729849806595543331244547/65536000000000000
  | 4, 2 => 83301302217472013622717/10485760000000000
  | 4, 3 => 138574461584170298662731/26214400000000000
  | 4, 4 => -560195899211802719046699/32768000000000000
  | 4, 5 => 1543576781120216089401/131072000000000
  | 4, 6 => 727025046163822366323363/16384000000000000
  | 4, 7 => 948970636189602992298333/1638400000000000
  | 5, 0 => 95166999960067286140262373/26214400000000000
  | 5, 1 => 11113201543710491752527/13107200000000000
  | 5, 2 => -203973650747133817508343/1048576000000000
  | 5, 3 => 322312699672503215100579/2621440000000000
  | 5, 4 => 1543576781120216089401/131072000000000
  | 5, 5 => -428477431290639456169917/1638400000000000
  | 5, 6 => 1054078060656605687920503/1638400000000000
  | 5, 7 => -99701519947816820212179/163840000000000
  | 6, 0 => -175538440354363800262225677/26214400000000000
  | 6, 1 => -12885057439514659527475347/32768000000000000
  | 6, 2 => 16866893128958580992747463/26214400000000000
  | 6, 3 => -5414374042135146758937267/13107200000000000
  | 6, 4 => 727025046163822366323363/16384000000000000
  | 6, 5 => 1054078060656605687920503/1638400000000000
  | 6, 6 => -13417206537411611280214011/8192000000000000
  | 6, 7 => 797255391734832796032267/819200000000000
  | 7, 0 => 69154353838247955125781933/2621440000000000
  | 7, 1 => 1281998470570534260875331/1638400000000000
  | 7, 2 => -99471136192512553900431/104857600000000
  | 7, 3 => 53455862611083189243987/1310720000000000
  | 7, 4 => 948970636189602992298333/1638400000000000
  | 7, 5 => -99701519947816820212179/163840000000000
  | 7, 6 => 797255391734832796032267/819200000000000
  | 7, 7 => -2081041110780259193873307/81920000000000
  | _, _ => 0

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Data18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
def candidateY_18 : Matrix (Fin 9) (Fin 9) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => -3559166385880423516847027379/41943040000000000
  | 0, 1 => 43700029260178412251303173/3276800000000000
  | 0, 2 => -157097886646298732847063351/41943040000000000
  | 0, 3 => 45795850251189055946275347/20971520000000000
  | 0, 4 => -15768543277252499592049191/5242880000000000
  | 0, 5 => 15774590706413201698776741/2621440000000000
  | 0, 6 => -111481601475376052708801013/13107200000000000
  | 0, 7 => -58408977661685586058262139/1310720000000000
  | 1, 0 => 43700029260178412251303173/3276800000000000
  | 1, 1 => -81940194402186836366199549/26214400000000000
  | 1, 2 => 5636036629375968042063837/5242880000000000
  | 1, 3 => -2298714004872189626128407/5242880000000000
  | 1, 4 => 297813059860269307535181/1638400000000000
  | 1, 5 => -427966983073658698687017/3276800000000000
  | 1, 6 => 460639052423449997118021/1638400000000000
  | 1, 7 => 856489912851915268585659/327680000000000
  | 2, 0 => -157097886646298732847063351/41943040000000000
  | 2, 1 => 5636036629375968042063837/5242880000000000
  | 2, 2 => -17038127051364859101889227/41943040000000000
  | 2, 3 => 3236875371562490528333463/20971520000000000
  | 2, 4 => 109159200441997398693/5242880000000000
  | 2, 5 => -76974792598120601955771/524288000000000
  | 2, 6 => 525900691396984091231043/2621440000000000
  | 2, 7 => 166478085484275751174989/262144000000000
  | 3, 0 => 45795850251189055946275347/20971520000000000
  | 3, 1 => -2298714004872189626128407/5242880000000000
  | 3, 2 => 3236875371562490528333463/20971520000000000
  | 3, 3 => -152920142255560594957119/2097152000000000
  | 3, 4 => 76480320836604209603463/2621440000000000
  | 3, 5 => 34507713700153945513647/1310720000000000
  | 3, 6 => -126720387057916007218863/1310720000000000
  | 3, 7 => -293804443074929463225549/655360000000000
  | 4, 0 => -15768543277252499592049191/5242880000000000
  | 4, 1 => 297813059860269307535181/1638400000000000
  | 4, 2 => 109159200441997398693/5242880000000000
  | 4, 3 => 76480320836604209603463/2621440000000000
  | 4, 4 => -59366777784768563477067/655360000000000
  | 4, 5 => 50562764756881342854273/327680000000000
  | 4, 6 => -141645844790470070219169/1638400000000000
  | 4, 7 => -70438571087878610696079/163840000000000
  | 5, 0 => 15774590706413201698776741/2621440000000000
  | 5, 1 => -427966983073658698687017/3276800000000000
  | 5, 2 => -76974792598120601955771/524288000000000
  | 5, 3 => 34507713700153945513647/1310720000000000
  | 5, 4 => 50562764756881342854273/327680000000000
  | 5, 5 => -60223184109272615717979/163840000000000
  | 5, 6 => 241267392281008969222347/819200000000000
  | 5, 7 => 153598002652096074585513/81920000000000
  | 6, 0 => -111481601475376052708801013/13107200000000000
  | 6, 1 => 460639052423449997118021/1638400000000000
  | 6, 2 => 525900691396984091231043/2621440000000000
  | 6, 3 => -126720387057916007218863/1310720000000000
  | 6, 4 => -141645844790470070219169/1638400000000000
  | 6, 5 => 241267392281008969222347/819200000000000
  | 6, 6 => -149658956021574385833447/819200000000000
  | 6, 7 => -32035926190597582065813/16384000000000
  | 7, 0 => -58408977661685586058262139/1310720000000000
  | 7, 1 => 856489912851915268585659/327680000000000
  | 7, 2 => 166478085484275751174989/262144000000000
  | 7, 3 => -293804443074929463225549/655360000000000
  | 7, 4 => -70438571087878610696079/163840000000000
  | 7, 5 => 153598002652096074585513/81920000000000
  | 7, 6 => -32035926190597582065813/16384000000000
  | 7, 7 => -884740548279231685308267/40960000000000
  | _, _ => 0

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Data19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
def candidateY_19 : Matrix (Fin 10) (Fin 10) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => -22693099803596038799039320263/209715200000000000
  | 0, 1 => 2702377258995069402702006051/104857600000000000
  | 0, 2 => -75142211033583596476200627/8388608000000000
  | 0, 3 => 14766383937965483058974739/4194304000000000
  | 0, 4 => -5511147190592216732622063/5242880000000000
  | 0, 5 => 7980474838179577610603727/13107200000000000
  | 0, 6 => -114214449015342819092842893/13107200000000000
  | 0, 7 => 15237169390990960795194813/262144000000000
  | 1, 0 => 2702377258995069402702006051/104857600000000000
  | 1, 1 => -333726928481320238730768903/52428800000000000
  | 1, 2 => 48289254450191241887451051/20971520000000000
  | 1, 3 => -10153357419755611709274627/10485760000000000
  | 1, 4 => 908184765784913635277259/2621440000000000
  | 1, 5 => -1019757214709519396489379/6553600000000000
  | 1, 6 => 11402120818106472624739569/6553600000000000
  | 1, 7 => -8025292448927789565871341/655360000000000
  | 2, 0 => -75142211033583596476200627/8388608000000000
  | 2, 1 => 48289254450191241887451051/20971520000000000
  | 2, 2 => -37648602224655100714998963/41943040000000000
  | 2, 3 => 9278879137014220083120771/20971520000000000
  | 2, 4 => -1279464695992326165509187/5242880000000000
  | 2, 5 => 488068742424207599021367/2621440000000000
  | 2, 6 => -1577990685084360947348949/2621440000000000
  | 2, 7 => 4397077893934901813915277/1310720000000000
  | 3, 0 => 14766383937965483058974739/4194304000000000
  | 3, 1 => -10153357419755611709274627/10485760000000000
  | 3, 2 => 9278879137014220083120771/20971520000000000
  | 3, 3 => -601273345026853390678479/2097152000000000
  | 3, 4 => 5095867887885096310527/20971520000000
  | 3, 5 => -66971412540394818930243/262144000000000
  | 3, 6 => 423492380929481504822181/1310720000000000
  | 3, 7 => -316097984120195393369253/655360000000000
  | 4, 0 => -5511147190592216732622063/5242880000000000
  | 4, 1 => 908184765784913635277259/2621440000000000
  | 4, 2 => -1279464695992326165509187/5242880000000000
  | 4, 3 => 5095867887885096310527/20971520000000
  | 4, 4 => -38268821834268590378583/131072000000000
  | 4, 5 => 120716948708384445134487/327680000000000
  | 4, 6 => -96794549499067619556357/327680000000000
  | 4, 7 => -152177568634600729759539/163840000000000
  | 5, 0 => 7980474838179577610603727/13107200000000000
  | 5, 1 => -1019757214709519396489379/6553600000000000
  | 5, 2 => 488068742424207599021367/2621440000000000
  | 5, 3 => -66971412540394818930243/262144000000000
  | 5, 4 => 120716948708384445134487/327680000000000
  | 5, 5 => -433804997186099031291183/819200000000000
  | 5, 6 => 429290867351544749347797/819200000000000
  | 5, 7 => 90088259697128585251359/81920000000000
  | 6, 0 => -114214449015342819092842893/13107200000000000
  | 6, 1 => 11402120818106472624739569/6553600000000000
  | 6, 2 => -1577990685084360947348949/2621440000000000
  | 6, 3 => 423492380929481504822181/1310720000000000
  | 6, 4 => -96794549499067619556357/327680000000000
  | 6, 5 => 429290867351544749347797/819200000000000
  | 6, 6 => -1253076332636888755282287/819200000000000
  | 6, 7 => 415758366080515083757131/81920000000000
  | 7, 0 => 15237169390990960795194813/262144000000000
  | 7, 1 => -8025292448927789565871341/655360000000000
  | 7, 2 => 4397077893934901813915277/1310720000000000
  | 7, 3 => -316097984120195393369253/655360000000000
  | 7, 4 => -152177568634600729759539/163840000000000
  | 7, 5 => 90088259697128585251359/81920000000000
  | 7, 6 => 415758366080515083757131/81920000000000
  | 7, 7 => -68818433127534301774563/1638400000000
  | _, _ => 0

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Data20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
def candidateY_20 : Matrix (Fin 10) (Fin 10) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => -864345790529147882613755097/1638400000000000
  | 0, 1 => 21667622927027497262745903/204800000000000
  | 0, 2 => -11712315275254254792460329/327680000000000
  | 0, 3 => 665376664948039201360203/40960000000000
  | 0, 4 => -316262058979922913891033/40960000000000
  | 0, 5 => 5363979077413683764037/25600000000000
  | 0, 6 => 1356924469605003889899309/102400000000000
  | 0, 7 => -99760004425375579574289/2560000000000
  | 1, 0 => 21667622927027497262745903/204800000000000
  | 1, 1 => -23371021993295094552757323/819200000000000
  | 1, 2 => 1943037668945799386453493/163840000000000
  | 1, 3 => -1013982585631618048647201/163840000000000
  | 1, 4 => 30613754919741298283979/10240000000000
  | 1, 5 => 107082038149227953680869/102400000000000
  | 1, 6 => -520977417754125297368403/51200000000000
  | 1, 7 => 304457703228940211619669/10240000000000
  | 2, 0 => -11712315275254254792460329/327680000000000
  | 2, 1 => 1943037668945799386453493/163840000000000
  | 2, 2 => -355964824312558132018347/65536000000000
  | 2, 3 => 97684912586085571093347/32768000000000
  | 2, 4 => -11858364672253510424013/8192000000000
  | 2, 5 => -14013038479459638758139/20480000000000
  | 2, 6 => 117196994897535165704091/20480000000000
  | 2, 7 => -34211653005025978665183/2048000000000
  | 3, 0 => 665376664948039201360203/40960000000000
  | 3, 1 => -1013982585631618048647201/163840000000000
  | 3, 2 => 97684912586085571093347/32768000000000
  | 3, 3 => -54884862420967333061307/32768000000000
  | 3, 4 => 333816883149802681629/409600000000
  | 3, 5 => 8819254098389714698719/20480000000000
  | 3, 6 => -35062147478835063928341/10240000000000
  | 3, 7 => 20460760081953150590631/2048000000000
  | 4, 0 => -316262058979922913891033/40960000000000
  | 4, 1 => 30613754919741298283979/10240000000000
  | 4, 2 => -11858364672253510424013/8192000000000
  | 4, 3 => 333816883149802681629/409600000000
  | 4, 4 => -405636934175189416161/1024000000000
  | 4, 5 => -272920889814962733729/1280000000000
  | 4, 6 => 4300425691175779286121/2560000000000
  | 4, 7 => -627014474788464764001/128000000000
  | 5, 0 => 5363979077413683764037/25600000000000
  | 5, 1 => 107082038149227953680869/102400000000000
  | 5, 2 => -14013038479459638758139/20480000000000
  | 5, 3 => 8819254098389714698719/20480000000000
  | 5, 4 => -272920889814962733729/1280000000000
  | 5, 5 => -2024204103566300379339/12800000000000
  | 5, 6 => 7072091643721157882829/6400000000000
  | 5, 7 => -4132909998582898800267/1280000000000
  | 6, 0 => 1356924469605003889899309/102400000000000
  | 6, 1 => -520977417754125297368403/51200000000000
  | 6, 2 => 117196994897535165704091/20480000000000
  | 6, 3 => -35062147478835063928341/10240000000000
  | 6, 4 => 4300425691175779286121/2560000000000
  | 6, 5 => 7072091643721157882829/6400000000000
  | 6, 6 => -51489116962575084283491/6400000000000
  | 6, 7 => 15026634633786455969289/640000000000
  | 7, 0 => -99760004425375579574289/2560000000000
  | 7, 1 => 304457703228940211619669/10240000000000
  | 7, 2 => -34211653005025978665183/2048000000000
  | 7, 3 => 20460760081953150590631/2048000000000
  | 7, 4 => -627014474788464764001/128000000000
  | 7, 5 => -4132909998582898800267/1280000000000
  | 7, 6 => 15026634633786455969289/640000000000
  | 7, 7 => -8768897177979921681699/128000000000
  | _, _ => 0

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Data21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
def candidateY_21 : Matrix (Fin 11) (Fin 11) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => -96711588542532735223983531/32768000000000
  | 0, 1 => 57038851132594341185352177/163840000000000
  | 0, 2 => -5636036476590197124447/327680000000
  | 0, 3 => -1952083051117812873373113/32768000000000
  | 0, 4 => 418641912860774562758799/4096000000000
  | 0, 5 => -644220666819787412766411/4096000000000
  | 0, 6 => 1256376941124933712895811/5120000000000
  | 0, 7 => -135618250205634004439631/409600000000
  | 1, 0 => 57038851132594341185352177/163840000000000
  | 1, 1 => -44082193767443568976121883/819200000000000
  | 1, 2 => 492577388419375083797973/40960000000000
  | 1, 3 => -281862084701495601299997/163840000000000
  | 1, 4 => -57918765188790724575357/20480000000000
  | 1, 5 => 143714000293113981147417/20480000000000
  | 1, 6 => -331513340018520454483689/25600000000000
  | 1, 7 => 195188481739185067894761/10240000000000
  | 2, 0 => -5636036476590197124447/327680000000
  | 2, 1 => 492577388419375083797973/40960000000000
  | 2, 2 => -16263180195796078115571/2048000000000
  | 2, 3 => 53358620528514863973411/8192000000000
  | 2, 4 => -6801410828588460561477/1024000000000
  | 2, 5 => 1665119090212013288853/204800000000
  | 2, 6 => -14227460106212415583521/1280000000000
  | 2, 7 => 7041025764192505558473/512000000000
  | 3, 0 => -1952083051117812873373113/32768000000000
  | 3, 1 => -281862084701495601299997/163840000000000
  | 3, 2 => 53358620528514863973411/8192000000000
  | 3, 3 => -9444449794627227102723/1310720000000
  | 3, 4 => 34389795345971868711909/4096000000000
  | 3, 5 => -45427929111821472609393/4096000000000
  | 3, 6 => 81562090823302666065489/5120000000000
  | 3, 7 => -41788312207893754536033/2048000000000
  | 4, 0 => 418641912860774562758799/4096000000000
  | 4, 1 => -57918765188790724575357/20480000000000
  | 4, 2 => -6801410828588460561477/1024000000000
  | 4, 3 => 34389795345971868711909/4096000000000
  | 4, 4 => -1046564151268430692359/102400000000
  | 4, 5 => 7064452961983792435599/512000000000
  | 4, 6 => -12849900797681178702471/640000000000
  | 4, 7 => 6640967897736757856271/256000000000
  | 5, 0 => -644220666819787412766411/4096000000000
  | 5, 1 => 143714000293113981147417/20480000000000
  | 5, 2 => 1665119090212013288853/204800000000
  | 5, 3 => -45427929111821472609393/4096000000000
  | 5, 4 => 7064452961983792435599/512000000000
  | 5, 5 => -9636033814007219448291/512000000000
  | 5, 6 => 17633221184266489332531/640000000000
  | 5, 7 => -365961031875624676491/10240000000
  | 6, 0 => 1256376941124933712895811/5120000000000
  | 6, 1 => -331513340018520454483689/25600000000000
  | 6, 2 => -14227460106212415583521/1280000000000
  | 6, 3 => 81562090823302666065489/5120000000000
  | 6, 4 => -12849900797681178702471/640000000000
  | 6, 5 => 17633221184266489332531/640000000000
  | 6, 6 => -32379448935674822168187/800000000000
  | 6, 7 => 16838009783175354176403/320000000000
  | 7, 0 => -135618250205634004439631/409600000000
  | 7, 1 => 195188481739185067894761/10240000000000
  | 7, 2 => 7041025764192505558473/512000000000
  | 7, 3 => -41788312207893754536033/2048000000000
  | 7, 4 => 6640967897736757856271/256000000000
  | 7, 5 => -365961031875624676491/10240000000
  | 7, 6 => 16838009783175354176403/320000000000
  | 7, 7 => -8768897177979921681699/128000000000
  | _, _ => 0

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped BigOperators Matrix

def copyLabel {D : ℕ} (i : Fin ((D+1)/2)) : ℕ := 2*i.val+1

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Square
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix

abbrev RowLevel (t : ℕ) := {T : Fin 16 // t ≤ T.val}

end Laughlin.Fock

end OAI
end


