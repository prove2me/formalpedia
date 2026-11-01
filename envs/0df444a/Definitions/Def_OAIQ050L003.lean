-- Prove2me | Definitions.Def_OAIQ050L003
-- name    : OAIQ050L003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T09:06:35.137205+00:00
-- url     : https://prove2.me/theorems/515f2ab2-039c-405b-abe0-06e913bfec04
-- title:
--   Definitions bundle OAIQ050L003 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 20 definitions. The definitions and types are `OAI.Laughlin.Certificate.candidateY_9`, `OAI.Laughlin.Certificate.candidateZ_14`, `OAI.Laughlin.Certificate.candidateZ_15`, `OAI.Laughlin.Certificate.candidateZ_16`, `OAI.Laughlin.Certificate.candidateZ_17`, `OAI.Laughlin.Certificate.candidateZ_18`, `OAI.Laughlin.Certificate.candidateZ_19`, `OAI.Laughlin.Certificate.candidateZ_20`, `OAI.Laughlin.Certificate.candidateZ_21`, `OAI.Laughlin.Certificate.candidateZ_22`, `OAI.Laughlin.Certificate.candidateZ_23`, `OAI.Laughlin.Certificate.candidateZ_9`, `OAI.Laughlin.Certificate.integerCouplingPolynomial`, `OAI.Laughlin.Certificate.limitBound`, `OAI.Laughlin.Certificate.lowerFive`, `OAI.Laughlin.Certificate.lower_10`, `OAI.Laughlin.Certificate.lower_11`, `OAI.Laughlin.Certificate.lower_12`, `OAI.Laughlin.Certificate.lower_9`, `OAI.Laughlin.Spin.Orbital`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Laughlin_FiniteFlux_Data09`, `Laughlin_FiniteFlux_Data10`, `Laughlin_FiniteFlux_Data11`, `Laughlin_FiniteFlux_Data12`, `Laughlin_FiniteFlux_Data14`, `Laughlin_FiniteFlux_Data15`, `Laughlin_FiniteFlux_Data16`, `Laughlin_FiniteFlux_Data17`, `Laughlin_FiniteFlux_Data18`, `Laughlin_FiniteFlux_Data19`, `Laughlin_FiniteFlux_Data20`, `Laughlin_FiniteFlux_Data21`, `Laughlin_FiniteFlux_Data22`, `Laughlin_FiniteFlux_Data23`, `Laughlin_FiniteFlux_Positive05`, `Laughlin_Operators_Certificate`, `Laughlin_Polynomial_SourceIntegerPolynomial`, `Laughlin_Spin_TripleLadderIntertwining`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ050L011`; the statements `OAI_Laughlin_Certificate_candidateLDL_10`, `OAI.Laughlin.Certificate.candidateLDL_10_s50`, `OAI_Laughlin_Certificate_candidateLDL_11`, `OAI.Laughlin.Certificate.candidateLDL_11_s50`, `OAI_Laughlin_Certificate_candidateLDL_12`, `OAI.Laughlin.Certificate.candidateLDL_12_s50`, `OAI_Laughlin_Certificate_candidateLDL_14`, `OAI.Laughlin.Certificate.candidateLDL_14_s50`, `OAI_Laughlin_Certificate_candidateLDL_15`, `OAI.Laughlin.Certificate.candidateLDL_15_s50`, `OAI_Laughlin_Certificate_candidateLDL_16`, `OAI.Laughlin.Certificate.candidateLDL_16_s50`, `OAI_Laughlin_Certificate_candidateLDL_17`, `OAI.Laughlin.Certificate.candidateLDL_17_s50`, `OAI_Laughlin_Certificate_candidateLDL_18`, `OAI.Laughlin.Certificate.candidateLDL_18_s50`, `OAI_Laughlin_Certificate_candidateLDL_19`, `OAI.Laughlin.Certificate.candidateLDL_19_s50`, `OAI_Laughlin_Certificate_candidateLDL_20`, `OAI.Laughlin.Certificate.candidateLDL_20_s50`, `OAI_Laughlin_Certificate_candidateLDL_21`, `OAI.Laughlin.Certificate.candidateLDL_21_s50`, `OAI_Laughlin_Certificate_candidateLDL_22`, `OAI.Laughlin.Certificate.candidateLDL_22_s50`, `OAI_Laughlin_Certificate_candidateLDL_23`, `OAI.Laughlin.Certificate.candidateLDL_23_s50`, `OAI_Laughlin_Certificate_candidateLDL_9`, `OAI.Laughlin.Certificate.candidateLDL_9_s50`, `OAI_Laughlin_Certificate_computeLDL_11_5_5`, `OAI.Laughlin.Certificate.computeLDL_11_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_1_5`, `OAI.Laughlin.Certificate.computeLDL_12_1_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_0`, `OAI.Laughlin.Certificate.computeLDL_12_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_1`, `OAI.Laughlin.Certificate.computeLDL_12_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_2`, `OAI.Laughlin.Certificate.computeLDL_12_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_3`, `OAI.Laughlin.Certificate.computeLDL_12_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_4`, `OAI.Laughlin.Certificate.computeLDL_12_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_5`, `OAI.Laughlin.Certificate.computeLDL_12_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_0`, `OAI.Laughlin.Certificate.computeLDL_12_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_1`, `OAI.Laughlin.Certificate.computeLDL_12_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_2`, `OAI.Laughlin.Certificate.computeLDL_12_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_3`, `OAI.Laughlin.Certificate.computeLDL_12_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_4`, `OAI.Laughlin.Certificate.computeLDL_12_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_5`, `OAI.Laughlin.Certificate.computeLDL_12_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_0`, `OAI.Laughlin.Certificate.computeLDL_12_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_1`, `OAI.Laughlin.Certificate.computeLDL_12_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_2`, `OAI.Laughlin.Certificate.computeLDL_12_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_3`, `OAI.Laughlin.Certificate.computeLDL_12_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_4`, `OAI.Laughlin.Certificate.computeLDL_12_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_5`, `OAI.Laughlin.Certificate.computeLDL_12_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_0`, `OAI.Laughlin.Certificate.computeLDL_12_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_1`, `OAI.Laughlin.Certificate.computeLDL_12_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_2`, `OAI.Laughlin.Certificate.computeLDL_12_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_3`, `OAI.Laughlin.Certificate.computeLDL_12_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_4`, `OAI.Laughlin.Certificate.computeLDL_12_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_5`, `OAI.Laughlin.Certificate.computeLDL_12_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_14_1_6`, `OAI.Laughlin.Certificate.computeLDL_14_1_6_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_0`, `OAI.Laughlin.Certificate.computeLDL_14_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_1`, `OAI.Laughlin.Certificate.computeLDL_14_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_2`, `OAI.Laughlin.Certificate.computeLDL_14_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_3`, `OAI.Laughlin.Certificate.computeLDL_14_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_4`, `OAI.Laughlin.Certificate.computeLDL_14_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_5`, `OAI.Laughlin.Certificate.computeLDL_14_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_6`, `OAI.Laughlin.Certificate.computeLDL_14_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_0`, `OAI.Laughlin.Certificate.computeLDL_14_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_1`, `OAI.Laughlin.Certificate.computeLDL_14_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_2`, `OAI.Laughlin.Certificate.computeLDL_14_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_3`, `OAI.Laughlin.Certificate.computeLDL_14_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_4`, `OAI.Laughlin.Certificate.computeLDL_14_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_5`, `OAI.Laughlin.Certificate.computeLDL_14_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_6`, `OAI.Laughlin.Certificate.computeLDL_14_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_0`, `OAI.Laughlin.Certificate.computeLDL_14_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_1`, `OAI.Laughlin.Certificate.computeLDL_14_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_2`, `OAI.Laughlin.Certificate.computeLDL_14_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_3`, `OAI.Laughlin.Certificate.computeLDL_14_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_4`, `OAI.Laughlin.Certificate.computeLDL_14_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_5`, `OAI.Laughlin.Certificate.computeLDL_14_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_6`, `OAI.Laughlin.Certificate.computeLDL_14_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_0`, `OAI.Laughlin.Certificate.computeLDL_14_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_1`, `OAI.Laughlin.Certificate.computeLDL_14_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_2`, `OAI.Laughlin.Certificate.computeLDL_14_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_3`, `OAI.Laughlin.Certificate.computeLDL_14_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_4`, `OAI.Laughlin.Certificate.computeLDL_14_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_5`, `OAI.Laughlin.Certificate.computeLDL_14_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_6`, `OAI.Laughlin.Certificate.computeLDL_14_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_0`, `OAI.Laughlin.Certificate.computeLDL_14_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_1`, `OAI.Laughlin.Certificate.computeLDL_14_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_2`, `OAI.Laughlin.Certificate.computeLDL_14_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_3`, `OAI.Laughlin.Certificate.computeLDL_14_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_4`, `OAI.Laughlin.Certificate.computeLDL_14_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_5`, `OAI.Laughlin.Certificate.computeLDL_14_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_6`, `OAI.Laughlin.Certificate.computeLDL_14_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_1_7`, `OAI.Laughlin.Certificate.computeLDL_15_1_7_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_0`, `OAI.Laughlin.Certificate.computeLDL_15_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_1`, `OAI.Laughlin.Certificate.computeLDL_15_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_2`, `OAI.Laughlin.Certificate.computeLDL_15_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_3`, `OAI.Laughlin.Certificate.computeLDL_15_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_4`, `OAI.Laughlin.Certificate.computeLDL_15_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_5`, `OAI.Laughlin.Certificate.computeLDL_15_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_6`, `OAI.Laughlin.Certificate.computeLDL_15_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_7`, `OAI.Laughlin.Certificate.computeLDL_15_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_0`, `OAI.Laughlin.Certificate.computeLDL_15_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_1`, `OAI.Laughlin.Certificate.computeLDL_15_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_2`, `OAI.Laughlin.Certificate.computeLDL_15_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_3`, `OAI.Laughlin.Certificate.computeLDL_15_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_4`, `OAI.Laughlin.Certificate.computeLDL_15_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_5`, `OAI.Laughlin.Certificate.computeLDL_15_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_6`, `OAI.Laughlin.Certificate.computeLDL_15_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_7`, `OAI.Laughlin.Certificate.computeLDL_15_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_0`, `OAI.Laughlin.Certificate.computeLDL_15_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_1`, `OAI.Laughlin.Certificate.computeLDL_15_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_2`, `OAI.Laughlin.Certificate.computeLDL_15_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_3`, `OAI.Laughlin.Certificate.computeLDL_15_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_4`, `OAI.Laughlin.Certificate.computeLDL_15_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_5`, `OAI.Laughlin.Certificate.computeLDL_15_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_6`, `OAI.Laughlin.Certificate.computeLDL_15_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_7`, `OAI.Laughlin.Certificate.computeLDL_15_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_0`, `OAI.Laughlin.Certificate.computeLDL_15_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_1`, `OAI.Laughlin.Certificate.computeLDL_15_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_2`, `OAI.Laughlin.Certificate.computeLDL_15_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_3`, `OAI.Laughlin.Certificate.computeLDL_15_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_4`, `OAI.Laughlin.Certificate.computeLDL_15_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_5`, `OAI.Laughlin.Certificate.computeLDL_15_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_6`, `OAI.Laughlin.Certificate.computeLDL_15_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_7`, `OAI.Laughlin.Certificate.computeLDL_15_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_0`, `OAI.Laughlin.Certificate.computeLDL_15_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_1`, `OAI.Laughlin.Certificate.computeLDL_15_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_2`, `OAI.Laughlin.Certificate.computeLDL_15_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_3`, `OAI.Laughlin.Certificate.computeLDL_15_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_4`, `OAI.Laughlin.Certificate.computeLDL_15_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_5`, `OAI.Laughlin.Certificate.computeLDL_15_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_6`, `OAI.Laughlin.Certificate.computeLDL_15_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_7`, `OAI.Laughlin.Certificate.computeLDL_15_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_0`, `OAI.Laughlin.Certificate.computeLDL_15_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_1`, `OAI.Laughlin.Certificate.computeLDL_15_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_2`, `OAI.Laughlin.Certificate.computeLDL_15_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_3`, `OAI.Laughlin.Certificate.computeLDL_15_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_4`, `OAI.Laughlin.Certificate.computeLDL_15_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_5`, `OAI.Laughlin.Certificate.computeLDL_15_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_6`, `OAI.Laughlin.Certificate.computeLDL_15_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_7`, `OAI.Laughlin.Certificate.computeLDL_15_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_1_7`, `OAI.Laughlin.Certificate.computeLDL_16_1_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_0`, `OAI.Laughlin.Certificate.computeLDL_16_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_1`, `OAI.Laughlin.Certificate.computeLDL_16_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_2`, `OAI.Laughlin.Certificate.computeLDL_16_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_3`, `OAI.Laughlin.Certificate.computeLDL_16_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_4`, `OAI.Laughlin.Certificate.computeLDL_16_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_5`, `OAI.Laughlin.Certificate.computeLDL_16_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_6`, `OAI.Laughlin.Certificate.computeLDL_16_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_7`, `OAI.Laughlin.Certificate.computeLDL_16_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_0`, `OAI.Laughlin.Certificate.computeLDL_16_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_1`, `OAI.Laughlin.Certificate.computeLDL_16_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_2`, `OAI.Laughlin.Certificate.computeLDL_16_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_3`, `OAI.Laughlin.Certificate.computeLDL_16_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_4`, `OAI.Laughlin.Certificate.computeLDL_16_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_5`, `OAI.Laughlin.Certificate.computeLDL_16_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_6`, `OAI.Laughlin.Certificate.computeLDL_16_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_7`, `OAI.Laughlin.Certificate.computeLDL_16_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_0`, `OAI.Laughlin.Certificate.computeLDL_16_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_1`, `OAI.Laughlin.Certificate.computeLDL_16_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_2`, `OAI.Laughlin.Certificate.computeLDL_16_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_3`, `OAI.Laughlin.Certificate.computeLDL_16_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_4`, `OAI.Laughlin.Certificate.computeLDL_16_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_5`, `OAI.Laughlin.Certificate.computeLDL_16_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_6`, `OAI.Laughlin.Certificate.computeLDL_16_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_7`, `OAI.Laughlin.Certificate.computeLDL_16_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_0`, `OAI.Laughlin.Certificate.computeLDL_16_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_1`, `OAI.Laughlin.Certificate.computeLDL_16_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_2`, `OAI.Laughlin.Certificate.computeLDL_16_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_3`, `OAI.Laughlin.Certificate.computeLDL_16_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_4`, `OAI.Laughlin.Certificate.computeLDL_16_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_5`, `OAI.Laughlin.Certificate.computeLDL_16_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_6`, `OAI.Laughlin.Certificate.computeLDL_16_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_7`, `OAI.Laughlin.Certificate.computeLDL_16_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_0`, `OAI.Laughlin.Certificate.computeLDL_16_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_1`, `OAI.Laughlin.Certificate.computeLDL_16_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_2`, `OAI.Laughlin.Certificate.computeLDL_16_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_3`, `OAI.Laughlin.Certificate.computeLDL_16_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_4`, `OAI.Laughlin.Certificate.computeLDL_16_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_5`, `OAI.Laughlin.Certificate.computeLDL_16_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_6`, `OAI.Laughlin.Certificate.computeLDL_16_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_7`, `OAI.Laughlin.Certificate.computeLDL_16_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_0`, `OAI.Laughlin.Certificate.computeLDL_16_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_1`, `OAI.Laughlin.Certificate.computeLDL_16_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_2`, `OAI.Laughlin.Certificate.computeLDL_16_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_3`, `OAI.Laughlin.Certificate.computeLDL_16_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_4`, `OAI.Laughlin.Certificate.computeLDL_16_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_5`, `OAI.Laughlin.Certificate.computeLDL_16_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_6`, `OAI.Laughlin.Certificate.computeLDL_16_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_7`, `OAI.Laughlin.Certificate.computeLDL_16_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_1_8`, `OAI.Laughlin.Certificate.computeLDL_17_1_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_0`, `OAI.Laughlin.Certificate.computeLDL_17_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_1`, `OAI.Laughlin.Certificate.computeLDL_17_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_2`, `OAI.Laughlin.Certificate.computeLDL_17_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_3`, `OAI.Laughlin.Certificate.computeLDL_17_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_4`, `OAI.Laughlin.Certificate.computeLDL_17_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_5`, `OAI.Laughlin.Certificate.computeLDL_17_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_6`, `OAI.Laughlin.Certificate.computeLDL_17_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_7`, `OAI.Laughlin.Certificate.computeLDL_17_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_8`, `OAI.Laughlin.Certificate.computeLDL_17_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_0`, `OAI.Laughlin.Certificate.computeLDL_17_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_1`, `OAI.Laughlin.Certificate.computeLDL_17_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_2`, `OAI.Laughlin.Certificate.computeLDL_17_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_3`, `OAI.Laughlin.Certificate.computeLDL_17_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_4`, `OAI.Laughlin.Certificate.computeLDL_17_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_5`, `OAI.Laughlin.Certificate.computeLDL_17_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_6`, `OAI.Laughlin.Certificate.computeLDL_17_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_7`, `OAI.Laughlin.Certificate.computeLDL_17_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_8`, `OAI.Laughlin.Certificate.computeLDL_17_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_0`, `OAI.Laughlin.Certificate.computeLDL_17_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_1`, `OAI.Laughlin.Certificate.computeLDL_17_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_2`, `OAI.Laughlin.Certificate.computeLDL_17_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_3`, `OAI.Laughlin.Certificate.computeLDL_17_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_4`, `OAI.Laughlin.Certificate.computeLDL_17_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_5`, `OAI.Laughlin.Certificate.computeLDL_17_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_6`, `OAI.Laughlin.Certificate.computeLDL_17_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_7`, `OAI.Laughlin.Certificate.computeLDL_17_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_8`, `OAI.Laughlin.Certificate.computeLDL_17_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_0`, `OAI.Laughlin.Certificate.computeLDL_17_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_1`, `OAI.Laughlin.Certificate.computeLDL_17_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_2`, `OAI.Laughlin.Certificate.computeLDL_17_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_3`, `OAI.Laughlin.Certificate.computeLDL_17_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_4`, `OAI.Laughlin.Certificate.computeLDL_17_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_5`, `OAI.Laughlin.Certificate.computeLDL_17_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_6`, `OAI.Laughlin.Certificate.computeLDL_17_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_7`, `OAI.Laughlin.Certificate.computeLDL_17_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_8`, `OAI.Laughlin.Certificate.computeLDL_17_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_0`, `OAI.Laughlin.Certificate.computeLDL_17_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_1`, `OAI.Laughlin.Certificate.computeLDL_17_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_2`, `OAI.Laughlin.Certificate.computeLDL_17_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_3`, `OAI.Laughlin.Certificate.computeLDL_17_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_4`, `OAI.Laughlin.Certificate.computeLDL_17_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_5`, `OAI.Laughlin.Certificate.computeLDL_17_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_6`, `OAI.Laughlin.Certificate.computeLDL_17_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_7`, `OAI.Laughlin.Certificate.computeLDL_17_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_8`, `OAI.Laughlin.Certificate.computeLDL_17_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_0`, `OAI.Laughlin.Certificate.computeLDL_17_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_1`, `OAI.Laughlin.Certificate.computeLDL_17_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_2`, `OAI.Laughlin.Certificate.computeLDL_17_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_3`, `OAI.Laughlin.Certificate.computeLDL_17_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_4`, `OAI.Laughlin.Certificate.computeLDL_17_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_5`, `OAI.Laughlin.Certificate.computeLDL_17_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_6`, `OAI.Laughlin.Certificate.computeLDL_17_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_7`, `OAI.Laughlin.Certificate.computeLDL_17_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_8`, `OAI.Laughlin.Certificate.computeLDL_17_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_0`, `OAI.Laughlin.Certificate.computeLDL_17_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_1`, `OAI.Laughlin.Certificate.computeLDL_17_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_2`, `OAI.Laughlin.Certificate.computeLDL_17_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_3`, `OAI.Laughlin.Certificate.computeLDL_17_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_4`, `OAI.Laughlin.Certificate.computeLDL_17_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_5`, `OAI.Laughlin.Certificate.computeLDL_17_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_6`, `OAI.Laughlin.Certificate.computeLDL_17_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_7`, `OAI.Laughlin.Certificate.computeLDL_17_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_8`, `OAI.Laughlin.Certificate.computeLDL_17_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_1_8`, `OAI.Laughlin.Certificate.computeLDL_18_1_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_0`, `OAI.Laughlin.Certificate.computeLDL_18_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_1`, `OAI.Laughlin.Certificate.computeLDL_18_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_2`, `OAI.Laughlin.Certificate.computeLDL_18_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_3`, `OAI.Laughlin.Certificate.computeLDL_18_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_4`, `OAI.Laughlin.Certificate.computeLDL_18_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_5`, `OAI.Laughlin.Certificate.computeLDL_18_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_6`, `OAI.Laughlin.Certificate.computeLDL_18_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_7`, `OAI.Laughlin.Certificate.computeLDL_18_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_8`, `OAI.Laughlin.Certificate.computeLDL_18_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_0`, `OAI.Laughlin.Certificate.computeLDL_18_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_1`, `OAI.Laughlin.Certificate.computeLDL_18_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_2`, `OAI.Laughlin.Certificate.computeLDL_18_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_3`, `OAI.Laughlin.Certificate.computeLDL_18_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_4`, `OAI.Laughlin.Certificate.computeLDL_18_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_5`, `OAI.Laughlin.Certificate.computeLDL_18_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_6`, `OAI.Laughlin.Certificate.computeLDL_18_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_7`, `OAI.Laughlin.Certificate.computeLDL_18_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_8`, `OAI.Laughlin.Certificate.computeLDL_18_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_0`, `OAI.Laughlin.Certificate.computeLDL_18_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_1`, `OAI.Laughlin.Certificate.computeLDL_18_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_2`, `OAI.Laughlin.Certificate.computeLDL_18_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_3`, `OAI.Laughlin.Certificate.computeLDL_18_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_4`, `OAI.Laughlin.Certificate.computeLDL_18_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_5`, `OAI.Laughlin.Certificate.computeLDL_18_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_6`, `OAI.Laughlin.Certificate.computeLDL_18_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_7`, `OAI.Laughlin.Certificate.computeLDL_18_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_8`, `OAI.Laughlin.Certificate.computeLDL_18_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_0`, `OAI.Laughlin.Certificate.computeLDL_18_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_1`, `OAI.Laughlin.Certificate.computeLDL_18_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_2`, `OAI.Laughlin.Certificate.computeLDL_18_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_3`, `OAI.Laughlin.Certificate.computeLDL_18_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_4`, `OAI.Laughlin.Certificate.computeLDL_18_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_5`, `OAI.Laughlin.Certificate.computeLDL_18_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_6`, `OAI.Laughlin.Certificate.computeLDL_18_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_7`, `OAI.Laughlin.Certificate.computeLDL_18_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_8`, `OAI.Laughlin.Certificate.computeLDL_18_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_0`, `OAI.Laughlin.Certificate.computeLDL_18_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_1`, `OAI.Laughlin.Certificate.computeLDL_18_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_2`, `OAI.Laughlin.Certificate.computeLDL_18_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_3`, `OAI.Laughlin.Certificate.computeLDL_18_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_4`, `OAI.Laughlin.Certificate.computeLDL_18_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_5`, `OAI.Laughlin.Certificate.computeLDL_18_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_6`, `OAI.Laughlin.Certificate.computeLDL_18_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_7`, `OAI.Laughlin.Certificate.computeLDL_18_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_8`, `OAI.Laughlin.Certificate.computeLDL_18_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_0`, `OAI.Laughlin.Certificate.computeLDL_18_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_1`, `OAI.Laughlin.Certificate.computeLDL_18_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_2`, `OAI.Laughlin.Certificate.computeLDL_18_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_3`, `OAI.Laughlin.Certificate.computeLDL_18_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_4`, `OAI.Laughlin.Certificate.computeLDL_18_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_5`, `OAI.Laughlin.Certificate.computeLDL_18_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_6`, `OAI.Laughlin.Certificate.computeLDL_18_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_7`, `OAI.Laughlin.Certificate.computeLDL_18_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_8`, `OAI.Laughlin.Certificate.computeLDL_18_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_0`, `OAI.Laughlin.Certificate.computeLDL_18_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_1`, `OAI.Laughlin.Certificate.computeLDL_18_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_2`, `OAI.Laughlin.Certificate.computeLDL_18_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_3`, `OAI.Laughlin.Certificate.computeLDL_18_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_4`, `OAI.Laughlin.Certificate.computeLDL_18_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_5`, `OAI.Laughlin.Certificate.computeLDL_18_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_6`, `OAI.Laughlin.Certificate.computeLDL_18_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_7`, `OAI.Laughlin.Certificate.computeLDL_18_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_8`, `OAI.Laughlin.Certificate.computeLDL_18_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_1_9`, `OAI.Laughlin.Certificate.computeLDL_19_1_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_0`, `OAI.Laughlin.Certificate.computeLDL_19_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_1`, `OAI.Laughlin.Certificate.computeLDL_19_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_2`, `OAI.Laughlin.Certificate.computeLDL_19_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_3`, `OAI.Laughlin.Certificate.computeLDL_19_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_4`, `OAI.Laughlin.Certificate.computeLDL_19_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_5`, `OAI.Laughlin.Certificate.computeLDL_19_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_6`, `OAI.Laughlin.Certificate.computeLDL_19_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_7`, `OAI.Laughlin.Certificate.computeLDL_19_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_8`, `OAI.Laughlin.Certificate.computeLDL_19_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_9`, `OAI.Laughlin.Certificate.computeLDL_19_2_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_0`, `OAI.Laughlin.Certificate.computeLDL_19_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_1`, `OAI.Laughlin.Certificate.computeLDL_19_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_2`, `OAI.Laughlin.Certificate.computeLDL_19_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_3`, `OAI.Laughlin.Certificate.computeLDL_19_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_4`, `OAI.Laughlin.Certificate.computeLDL_19_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_5`, `OAI.Laughlin.Certificate.computeLDL_19_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_6`, `OAI.Laughlin.Certificate.computeLDL_19_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_7`, `OAI.Laughlin.Certificate.computeLDL_19_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_8`, `OAI.Laughlin.Certificate.computeLDL_19_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_9`, `OAI.Laughlin.Certificate.computeLDL_19_3_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_0`, `OAI.Laughlin.Certificate.computeLDL_19_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_1`, `OAI.Laughlin.Certificate.computeLDL_19_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_2`, `OAI.Laughlin.Certificate.computeLDL_19_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_3`, `OAI.Laughlin.Certificate.computeLDL_19_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_4`, `OAI.Laughlin.Certificate.computeLDL_19_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_5`, `OAI.Laughlin.Certificate.computeLDL_19_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_6`, `OAI.Laughlin.Certificate.computeLDL_19_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_7`, `OAI.Laughlin.Certificate.computeLDL_19_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_8`, `OAI.Laughlin.Certificate.computeLDL_19_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_9`, `OAI.Laughlin.Certificate.computeLDL_19_4_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_0`, `OAI.Laughlin.Certificate.computeLDL_19_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_1`, `OAI.Laughlin.Certificate.computeLDL_19_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_2`, `OAI.Laughlin.Certificate.computeLDL_19_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_3`, `OAI.Laughlin.Certificate.computeLDL_19_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_4`, `OAI.Laughlin.Certificate.computeLDL_19_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_5`, `OAI.Laughlin.Certificate.computeLDL_19_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_6`, `OAI.Laughlin.Certificate.computeLDL_19_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_7`, `OAI.Laughlin.Certificate.computeLDL_19_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_8`, `OAI.Laughlin.Certificate.computeLDL_19_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_9`, `OAI.Laughlin.Certificate.computeLDL_19_5_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_0`, `OAI.Laughlin.Certificate.computeLDL_19_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_1`, `OAI.Laughlin.Certificate.computeLDL_19_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_2`, `OAI.Laughlin.Certificate.computeLDL_19_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_3`, `OAI.Laughlin.Certificate.computeLDL_19_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_4`, `OAI.Laughlin.Certificate.computeLDL_19_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_5`, `OAI.Laughlin.Certificate.computeLDL_19_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_6`, `OAI.Laughlin.Certificate.computeLDL_19_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_7`, `OAI.Laughlin.Certificate.computeLDL_19_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_8`, `OAI.Laughlin.Certificate.computeLDL_19_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_9`, `OAI.Laughlin.Certificate.computeLDL_19_6_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_0`, `OAI.Laughlin.Certificate.computeLDL_19_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_1`, `OAI.Laughlin.Certificate.computeLDL_19_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_2`, `OAI.Laughlin.Certificate.computeLDL_19_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_3`, `OAI.Laughlin.Certificate.computeLDL_19_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_4`, `OAI.Laughlin.Certificate.computeLDL_19_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_5`, `OAI.Laughlin.Certificate.computeLDL_19_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_6`, `OAI.Laughlin.Certificate.computeLDL_19_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_7`, `OAI.Laughlin.Certificate.computeLDL_19_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_8`, `OAI.Laughlin.Certificate.computeLDL_19_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_9`, `OAI.Laughlin.Certificate.computeLDL_19_7_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_0`, `OAI.Laughlin.Certificate.computeLDL_19_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_1`, `OAI.Laughlin.Certificate.computeLDL_19_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_2`, `OAI.Laughlin.Certificate.computeLDL_19_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_3`, `OAI.Laughlin.Certificate.computeLDL_19_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_4`, `OAI.Laughlin.Certificate.computeLDL_19_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_5`, `OAI.Laughlin.Certificate.computeLDL_19_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_6`, `OAI.Laughlin.Certificate.computeLDL_19_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_7`, `OAI.Laughlin.Certificate.computeLDL_19_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_8`, `OAI.Laughlin.Certificate.computeLDL_19_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_9`, `OAI.Laughlin.Certificate.computeLDL_19_8_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_0`, `OAI.Laughlin.Certificate.computeLDL_19_9_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_1`, `OAI.Laughlin.Certificate.computeLDL_19_9_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_2`, `OAI.Laughlin.Certificate.computeLDL_19_9_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_3`, `OAI.Laughlin.Certificate.computeLDL_19_9_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_4`, `OAI.Laughlin.Certificate.computeLDL_19_9_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_5`, `OAI.Laughlin.Certificate.computeLDL_19_9_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_6`, `OAI.Laughlin.Certificate.computeLDL_19_9_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_7`, `OAI.Laughlin.Certificate.computeLDL_19_9_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_8`, `OAI.Laughlin.Certificate.computeLDL_19_9_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_9`, `OAI.Laughlin.Certificate.computeLDL_19_9_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_1_9`, `OAI.Laughlin.Certificate.computeLDL_20_1_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_0`, `OAI.Laughlin.Certificate.computeLDL_20_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_1`, `OAI.Laughlin.Certificate.computeLDL_20_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_2`, `OAI.Laughlin.Certificate.computeLDL_20_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_3`, `OAI.Laughlin.Certificate.computeLDL_20_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_4`, `OAI.Laughlin.Certificate.computeLDL_20_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_5`, `OAI.Laughlin.Certificate.computeLDL_20_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_6`, `OAI.Laughlin.Certificate.computeLDL_20_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_7`, `OAI.Laughlin.Certificate.computeLDL_20_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_8`, `OAI.Laughlin.Certificate.computeLDL_20_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_9`, `OAI.Laughlin.Certificate.computeLDL_20_2_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_0`, `OAI.Laughlin.Certificate.computeLDL_20_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_1`, `OAI.Laughlin.Certificate.computeLDL_20_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_2`, `OAI.Laughlin.Certificate.computeLDL_20_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_3`, `OAI.Laughlin.Certificate.computeLDL_20_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_4`, `OAI.Laughlin.Certificate.computeLDL_20_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_5`, `OAI.Laughlin.Certificate.computeLDL_20_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_6`, `OAI.Laughlin.Certificate.computeLDL_20_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_7`, `OAI.Laughlin.Certificate.computeLDL_20_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_8`, `OAI.Laughlin.Certificate.computeLDL_20_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_9`, `OAI.Laughlin.Certificate.computeLDL_20_3_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_0`, `OAI.Laughlin.Certificate.computeLDL_20_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_1`, `OAI.Laughlin.Certificate.computeLDL_20_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_2`, `OAI.Laughlin.Certificate.computeLDL_20_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_3`, `OAI.Laughlin.Certificate.computeLDL_20_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_4`, `OAI.Laughlin.Certificate.computeLDL_20_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_5`, `OAI.Laughlin.Certificate.computeLDL_20_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_6`, `OAI.Laughlin.Certificate.computeLDL_20_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_7`, `OAI.Laughlin.Certificate.computeLDL_20_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_8`, `OAI.Laughlin.Certificate.computeLDL_20_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_9`, `OAI.Laughlin.Certificate.computeLDL_20_4_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_0`, `OAI.Laughlin.Certificate.computeLDL_20_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_1`, `OAI.Laughlin.Certificate.computeLDL_20_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_2`, `OAI.Laughlin.Certificate.computeLDL_20_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_3`, `OAI.Laughlin.Certificate.computeLDL_20_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_4`, `OAI.Laughlin.Certificate.computeLDL_20_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_5`, `OAI.Laughlin.Certificate.computeLDL_20_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_6`, `OAI.Laughlin.Certificate.computeLDL_20_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_7`, `OAI.Laughlin.Certificate.computeLDL_20_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_8`, `OAI.Laughlin.Certificate.computeLDL_20_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_9`, `OAI.Laughlin.Certificate.computeLDL_20_5_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_0`, `OAI.Laughlin.Certificate.computeLDL_20_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_1`, `OAI.Laughlin.Certificate.computeLDL_20_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_2`, `OAI.Laughlin.Certificate.computeLDL_20_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_3`, `OAI.Laughlin.Certificate.computeLDL_20_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_4`, `OAI.Laughlin.Certificate.computeLDL_20_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_5`, `OAI.Laughlin.Certificate.computeLDL_20_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_6`, `OAI.Laughlin.Certificate.computeLDL_20_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_7`, `OAI.Laughlin.Certificate.computeLDL_20_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_8`, `OAI.Laughlin.Certificate.computeLDL_20_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_9`, `OAI.Laughlin.Certificate.computeLDL_20_6_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_0`, `OAI.Laughlin.Certificate.computeLDL_20_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_1`, `OAI.Laughlin.Certificate.computeLDL_20_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_2`, `OAI.Laughlin.Certificate.computeLDL_20_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_3`, `OAI.Laughlin.Certificate.computeLDL_20_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_4`, `OAI.Laughlin.Certificate.computeLDL_20_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_5`, `OAI.Laughlin.Certificate.computeLDL_20_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_6`, `OAI.Laughlin.Certificate.computeLDL_20_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_7`, `OAI.Laughlin.Certificate.computeLDL_20_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_8`, `OAI.Laughlin.Certificate.computeLDL_20_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_9`, `OAI.Laughlin.Certificate.computeLDL_20_7_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_0`, `OAI.Laughlin.Certificate.computeLDL_20_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_1`, `OAI.Laughlin.Certificate.computeLDL_20_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_2`, `OAI.Laughlin.Certificate.computeLDL_20_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_3`, `OAI.Laughlin.Certificate.computeLDL_20_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_4`, `OAI.Laughlin.Certificate.computeLDL_20_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_5`, `OAI.Laughlin.Certificate.computeLDL_20_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_6`, `OAI.Laughlin.Certificate.computeLDL_20_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_7`, `OAI.Laughlin.Certificate.computeLDL_20_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_8`, `OAI.Laughlin.Certificate.computeLDL_20_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_9`, `OAI.Laughlin.Certificate.computeLDL_20_8_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_0`, `OAI.Laughlin.Certificate.computeLDL_20_9_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_1`, `OAI.Laughlin.Certificate.computeLDL_20_9_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_2`, `OAI.Laughlin.Certificate.computeLDL_20_9_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_3`, `OAI.Laughlin.Certificate.computeLDL_20_9_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_4`, `OAI.Laughlin.Certificate.computeLDL_20_9_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_5`, `OAI.Laughlin.Certificate.computeLDL_20_9_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_6`, `OAI.Laughlin.Certificate.computeLDL_20_9_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_7`, `OAI.Laughlin.Certificate.computeLDL_20_9_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_8`, `OAI.Laughlin.Certificate.computeLDL_20_9_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_9`, `OAI.Laughlin.Certificate.computeLDL_20_9_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_0_10`, `OAI.Laughlin.Certificate.computeLDL_21_0_10_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_0`, `OAI.Laughlin.Certificate.computeLDL_21_10_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_1`, `OAI_Laughlin_Certificate_computeLDL_21_10_10`, `OAI.Laughlin.Certificate.computeLDL_21_10_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_10_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_2`, `OAI.Laughlin.Certificate.computeLDL_21_10_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_3`, `OAI.Laughlin.Certificate.computeLDL_21_10_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_4`, `OAI.Laughlin.Certificate.computeLDL_21_10_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_5`, `OAI.Laughlin.Certificate.computeLDL_21_10_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_6`, `OAI.Laughlin.Certificate.computeLDL_21_10_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_7`, `OAI.Laughlin.Certificate.computeLDL_21_10_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_8`, `OAI.Laughlin.Certificate.computeLDL_21_10_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_9`, `OAI.Laughlin.Certificate.computeLDL_21_10_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_1_10`, `OAI.Laughlin.Certificate.computeLDL_21_1_10_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_1`, `OAI_Laughlin_Certificate_computeLDL_21_2_10`, `OAI.Laughlin.Certificate.computeLDL_21_2_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_2`, `OAI.Laughlin.Certificate.computeLDL_21_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_3`, `OAI.Laughlin.Certificate.computeLDL_21_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_4`, `OAI.Laughlin.Certificate.computeLDL_21_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_5`, `OAI.Laughlin.Certificate.computeLDL_21_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_6`, `OAI.Laughlin.Certificate.computeLDL_21_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_7`, `OAI.Laughlin.Certificate.computeLDL_21_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_8`, `OAI.Laughlin.Certificate.computeLDL_21_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_9`, `OAI.Laughlin.Certificate.computeLDL_21_2_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_0`, `OAI.Laughlin.Certificate.computeLDL_21_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_1`, `OAI_Laughlin_Certificate_computeLDL_21_3_10`, `OAI.Laughlin.Certificate.computeLDL_21_3_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_2`, `OAI.Laughlin.Certificate.computeLDL_21_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_3`, `OAI.Laughlin.Certificate.computeLDL_21_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_4`, `OAI.Laughlin.Certificate.computeLDL_21_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_5`, `OAI.Laughlin.Certificate.computeLDL_21_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_6`, `OAI.Laughlin.Certificate.computeLDL_21_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_7`, `OAI.Laughlin.Certificate.computeLDL_21_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_8`, `OAI.Laughlin.Certificate.computeLDL_21_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_9`, `OAI.Laughlin.Certificate.computeLDL_21_3_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_0`, `OAI.Laughlin.Certificate.computeLDL_21_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_1`, `OAI_Laughlin_Certificate_computeLDL_21_4_10`, `OAI.Laughlin.Certificate.computeLDL_21_4_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_2`, `OAI.Laughlin.Certificate.computeLDL_21_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_3`, `OAI.Laughlin.Certificate.computeLDL_21_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_4`, `OAI.Laughlin.Certificate.computeLDL_21_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_5`, `OAI.Laughlin.Certificate.computeLDL_21_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_6`, `OAI.Laughlin.Certificate.computeLDL_21_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_7`, `OAI.Laughlin.Certificate.computeLDL_21_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_8`, `OAI.Laughlin.Certificate.computeLDL_21_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_9`, `OAI.Laughlin.Certificate.computeLDL_21_4_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_0`, `OAI.Laughlin.Certificate.computeLDL_21_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_1`, `OAI_Laughlin_Certificate_computeLDL_21_5_10`, `OAI.Laughlin.Certificate.computeLDL_21_5_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_2`, `OAI.Laughlin.Certificate.computeLDL_21_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_3`, `OAI.Laughlin.Certificate.computeLDL_21_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_4`, `OAI.Laughlin.Certificate.computeLDL_21_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_5`, `OAI.Laughlin.Certificate.computeLDL_21_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_6`, `OAI.Laughlin.Certificate.computeLDL_21_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_7`, `OAI.Laughlin.Certificate.computeLDL_21_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_8`, `OAI.Laughlin.Certificate.computeLDL_21_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_9`, `OAI.Laughlin.Certificate.computeLDL_21_5_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_0`, `OAI.Laughlin.Certificate.computeLDL_21_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_1`, `OAI_Laughlin_Certificate_computeLDL_21_6_10`, `OAI.Laughlin.Certificate.computeLDL_21_6_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_2`, `OAI.Laughlin.Certificate.computeLDL_21_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_3`, `OAI.Laughlin.Certificate.computeLDL_21_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_4`, `OAI.Laughlin.Certificate.computeLDL_21_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_5`, `OAI.Laughlin.Certificate.computeLDL_21_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_6`, `OAI.Laughlin.Certificate.computeLDL_21_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_7`, `OAI.Laughlin.Certificate.computeLDL_21_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_8`, `OAI.Laughlin.Certificate.computeLDL_21_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_9`, `OAI.Laughlin.Certificate.computeLDL_21_6_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_0`, `OAI.Laughlin.Certificate.computeLDL_21_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_1`, `OAI_Laughlin_Certificate_computeLDL_21_7_10`, `OAI.Laughlin.Certificate.computeLDL_21_7_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_2`, `OAI.Laughlin.Certificate.computeLDL_21_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_3`, `OAI.Laughlin.Certificate.computeLDL_21_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_4`, `OAI.Laughlin.Certificate.computeLDL_21_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_5`, `OAI.Laughlin.Certificate.computeLDL_21_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_6`, `OAI.Laughlin.Certificate.computeLDL_21_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_7`, `OAI.Laughlin.Certificate.computeLDL_21_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_8`, `OAI.Laughlin.Certificate.computeLDL_21_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_9`, `OAI.Laughlin.Certificate.computeLDL_21_7_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_0`, `OAI.Laughlin.Certificate.computeLDL_21_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_1`, `OAI_Laughlin_Certificate_computeLDL_21_8_10`, `OAI.Laughlin.Certificate.computeLDL_21_8_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_2`, `OAI.Laughlin.Certificate.computeLDL_21_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_3`, `OAI.Laughlin.Certificate.computeLDL_21_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_4`, `OAI.Laughlin.Certificate.computeLDL_21_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_5`, `OAI.Laughlin.Certificate.computeLDL_21_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_6`, `OAI.Laughlin.Certificate.computeLDL_21_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_7`, `OAI.Laughlin.Certificate.computeLDL_21_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_8`, `OAI.Laughlin.Certificate.computeLDL_21_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_9`, `OAI.Laughlin.Certificate.computeLDL_21_8_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_0`, `OAI.Laughlin.Certificate.computeLDL_21_9_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_1`, `OAI_Laughlin_Certificate_computeLDL_21_9_10`, `OAI.Laughlin.Certificate.computeLDL_21_9_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_9_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_2`, `OAI.Laughlin.Certificate.computeLDL_21_9_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_3`, `OAI.Laughlin.Certificate.computeLDL_21_9_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_4`, `OAI.Laughlin.Certificate.computeLDL_21_9_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_5`, `OAI.Laughlin.Certificate.computeLDL_21_9_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_6`, `OAI.Laughlin.Certificate.computeLDL_21_9_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_7`, `OAI.Laughlin.Certificate.computeLDL_21_9_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_8`, `OAI.Laughlin.Certificate.computeLDL_21_9_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_9`, `OAI.Laughlin.Certificate.computeLDL_21_9_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_0_10`, `OAI.Laughlin.Certificate.computeLDL_22_0_10_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_0`, `OAI.Laughlin.Certificate.computeLDL_22_10_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_1`, `OAI_Laughlin_Certificate_computeLDL_22_10_10`, `OAI.Laughlin.Certificate.computeLDL_22_10_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_10_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_2`, `OAI.Laughlin.Certificate.computeLDL_22_10_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_3`, `OAI.Laughlin.Certificate.computeLDL_22_10_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_4`, `OAI.Laughlin.Certificate.computeLDL_22_10_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_5`, `OAI.Laughlin.Certificate.computeLDL_22_10_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_6`, `OAI.Laughlin.Certificate.computeLDL_22_10_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_7`, `OAI.Laughlin.Certificate.computeLDL_22_10_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_8`, `OAI.Laughlin.Certificate.computeLDL_22_10_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_9`, `OAI.Laughlin.Certificate.computeLDL_22_10_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_1_10`, `OAI.Laughlin.Certificate.computeLDL_22_1_10_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_1`, `OAI_Laughlin_Certificate_computeLDL_22_2_10`, `OAI.Laughlin.Certificate.computeLDL_22_2_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_2`, `OAI.Laughlin.Certificate.computeLDL_22_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_3`, `OAI.Laughlin.Certificate.computeLDL_22_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_4`, `OAI.Laughlin.Certificate.computeLDL_22_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_5`, `OAI.Laughlin.Certificate.computeLDL_22_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_6`, `OAI.Laughlin.Certificate.computeLDL_22_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_7`, `OAI.Laughlin.Certificate.computeLDL_22_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_8`, `OAI.Laughlin.Certificate.computeLDL_22_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_9`, `OAI.Laughlin.Certificate.computeLDL_22_2_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_0`, `OAI.Laughlin.Certificate.computeLDL_22_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_1`, `OAI_Laughlin_Certificate_computeLDL_22_3_10`, `OAI.Laughlin.Certificate.computeLDL_22_3_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_2`, `OAI.Laughlin.Certificate.computeLDL_22_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_3`, `OAI.Laughlin.Certificate.computeLDL_22_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_4`, `OAI.Laughlin.Certificate.computeLDL_22_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_5`, `OAI.Laughlin.Certificate.computeLDL_22_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_6`, `OAI.Laughlin.Certificate.computeLDL_22_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_7`, `OAI.Laughlin.Certificate.computeLDL_22_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_8`, `OAI.Laughlin.Certificate.computeLDL_22_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_9`, `OAI.Laughlin.Certificate.computeLDL_22_3_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_0`, `OAI.Laughlin.Certificate.computeLDL_22_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_1`, `OAI_Laughlin_Certificate_computeLDL_22_4_10`, `OAI.Laughlin.Certificate.computeLDL_22_4_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_2`, `OAI.Laughlin.Certificate.computeLDL_22_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_3`, `OAI.Laughlin.Certificate.computeLDL_22_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_4`, `OAI.Laughlin.Certificate.computeLDL_22_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_5`, `OAI.Laughlin.Certificate.computeLDL_22_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_6`, `OAI.Laughlin.Certificate.computeLDL_22_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_7`, `OAI.Laughlin.Certificate.computeLDL_22_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_8`, `OAI.Laughlin.Certificate.computeLDL_22_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_9`, `OAI.Laughlin.Certificate.computeLDL_22_4_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_0`, `OAI.Laughlin.Certificate.computeLDL_22_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_1`, `OAI_Laughlin_Certificate_computeLDL_22_5_10`, `OAI.Laughlin.Certificate.computeLDL_22_5_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_2`, `OAI.Laughlin.Certificate.computeLDL_22_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_3`, `OAI.Laughlin.Certificate.computeLDL_22_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_4`, `OAI.Laughlin.Certificate.computeLDL_22_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_5`, `OAI.Laughlin.Certificate.computeLDL_22_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_6`, `OAI.Laughlin.Certificate.computeLDL_22_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_7`, `OAI.Laughlin.Certificate.computeLDL_22_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_8`, `OAI.Laughlin.Certificate.computeLDL_22_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_9`, `OAI.Laughlin.Certificate.computeLDL_22_5_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_0`, `OAI.Laughlin.Certificate.computeLDL_22_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_1`, `OAI_Laughlin_Certificate_computeLDL_22_6_10`, `OAI.Laughlin.Certificate.computeLDL_22_6_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_2`, `OAI.Laughlin.Certificate.computeLDL_22_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_3`, `OAI.Laughlin.Certificate.computeLDL_22_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_4`, `OAI.Laughlin.Certificate.computeLDL_22_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_5`, `OAI.Laughlin.Certificate.computeLDL_22_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_6`, `OAI.Laughlin.Certificate.computeLDL_22_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_7`, `OAI.Laughlin.Certificate.computeLDL_22_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_8`, `OAI.Laughlin.Certificate.computeLDL_22_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_9`, `OAI.Laughlin.Certificate.computeLDL_22_6_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_0`, `OAI.Laughlin.Certificate.computeLDL_22_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_1`, `OAI_Laughlin_Certificate_computeLDL_22_7_10`, `OAI.Laughlin.Certificate.computeLDL_22_7_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_2`, `OAI.Laughlin.Certificate.computeLDL_22_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_3`, `OAI.Laughlin.Certificate.computeLDL_22_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_4`, `OAI.Laughlin.Certificate.computeLDL_22_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_5`, `OAI.Laughlin.Certificate.computeLDL_22_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_6`, `OAI.Laughlin.Certificate.computeLDL_22_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_7`, `OAI.Laughlin.Certificate.computeLDL_22_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_8`, `OAI.Laughlin.Certificate.computeLDL_22_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_9`, `OAI.Laughlin.Certificate.computeLDL_22_7_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_0`, `OAI.Laughlin.Certificate.computeLDL_22_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_1`, `OAI_Laughlin_Certificate_computeLDL_22_8_10`, `OAI.Laughlin.Certificate.computeLDL_22_8_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_2`, `OAI.Laughlin.Certificate.computeLDL_22_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_3`, `OAI.Laughlin.Certificate.computeLDL_22_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_4`, `OAI.Laughlin.Certificate.computeLDL_22_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_5`, `OAI.Laughlin.Certificate.computeLDL_22_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_6`, `OAI.Laughlin.Certificate.computeLDL_22_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_7`, `OAI.Laughlin.Certificate.computeLDL_22_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_8`, `OAI.Laughlin.Certificate.computeLDL_22_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_9`, `OAI.Laughlin.Certificate.computeLDL_22_8_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_0`, `OAI.Laughlin.Certificate.computeLDL_22_9_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_1`, `OAI_Laughlin_Certificate_computeLDL_22_9_10`, `OAI.Laughlin.Certificate.computeLDL_22_9_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_9_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_2`, `OAI.Laughlin.Certificate.computeLDL_22_9_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_3`, `OAI.Laughlin.Certificate.computeLDL_22_9_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_4`, `OAI.Laughlin.Certificate.computeLDL_22_9_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_5`, `OAI.Laughlin.Certificate.computeLDL_22_9_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_6`, `OAI.Laughlin.Certificate.computeLDL_22_9_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_7`, `OAI.Laughlin.Certificate.computeLDL_22_9_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_8`, `OAI.Laughlin.Certificate.computeLDL_22_9_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_9`, `OAI.Laughlin.Certificate.computeLDL_22_9_9_s50`, `OAI_Laughlin_Certificate_computeLDL_23_0_10`, `OAI.Laughlin.Certificate.computeLDL_23_0_10_s50`, `OAI_Laughlin_Certificate_computeLDL_23_0_11`, `OAI.Laughlin.Certificate.computeLDL_23_0_11_s50`, `OAI_Laughlin_Certificate_computeLDL_23_10_0`, `OAI.Laughlin.Certificate.computeLDL_23_10_0_s50`, `OAI_Laughlin_Certificate_computeLDL_23_10_1`, `OAI_Laughlin_Certificate_computeLDL_23_10_10`, `OAI.Laughlin.Certificate.computeLDL_23_10_10_s50`, `OAI_Laughlin_Certificate_computeLDL_23_10_11`, `OAI.Laughlin.Certificate.computeLDL_23_10_11_s50`, `OAI.Laughlin.Certificate.computeLDL_23_10_1_s50`, `OAI_Laughlin_Certificate_computeLDL_23_10_2`, `OAI.Laughlin.Certificate.computeLDL_23_10_2_s50`, `OAI_Laughlin_Certificate_computeLDL_23_10_3`, `OAI.Laughlin.Certificate.computeLDL_23_10_3_s50`, `OAI_Laughlin_Certificate_computeLDL_23_10_4`, `OAI.Laughlin.Certificate.computeLDL_23_10_4_s50`, `OAI_Laughlin_Certificate_computeLDL_23_10_5`, `OAI.Laughlin.Certificate.computeLDL_23_10_5_s50`, `OAI_Laughlin_Certificate_computeLDL_23_10_6`, `OAI.Laughlin.Certificate.computeLDL_23_10_6_s50`, `OAI_Laughlin_Certificate_computeLDL_23_10_7`, `OAI.Laughlin.Certificate.computeLDL_23_10_7_s50`, `OAI_Laughlin_Certificate_computeLDL_23_10_8`, `OAI.Laughlin.Certificate.computeLDL_23_10_8_s50`, `OAI_Laughlin_Certificate_computeLDL_23_10_9`, `OAI.Laughlin.Certificate.computeLDL_23_10_9_s50`, `OAI_Laughlin_Certificate_computeLDL_23_11_0`, `OAI.Laughlin.Certificate.computeLDL_23_11_0_s50`, `OAI_Laughlin_Certificate_computeLDL_23_11_1`, `OAI_Laughlin_Certificate_computeLDL_23_11_10`, `OAI.Laughlin.Certificate.computeLDL_23_11_10_s50`, `OAI_Laughlin_Certificate_computeLDL_23_11_11`, `OAI.Laughlin.Certificate.computeLDL_23_11_11_s50`, `OAI.Laughlin.Certificate.computeLDL_23_11_1_s50`, `OAI_Laughlin_Certificate_computeLDL_23_11_2`, `OAI.Laughlin.Certificate.computeLDL_23_11_2_s50`, `OAI_Laughlin_Certificate_computeLDL_23_11_3`, `OAI.Laughlin.Certificate.computeLDL_23_11_3_s50`, `OAI_Laughlin_Certificate_computeLDL_23_11_4`, `OAI.Laughlin.Certificate.computeLDL_23_11_4_s50`, `OAI_Laughlin_Certificate_computeLDL_23_11_5`, `OAI.Laughlin.Certificate.computeLDL_23_11_5_s50`, `OAI_Laughlin_Certificate_computeLDL_23_11_6`, `OAI.Laughlin.Certificate.computeLDL_23_11_6_s50`, `OAI_Laughlin_Certificate_computeLDL_23_11_7`, `OAI.Laughlin.Certificate.computeLDL_23_11_7_s50`, `OAI_Laughlin_Certificate_computeLDL_23_11_8`, `OAI.Laughlin.Certificate.computeLDL_23_11_8_s50`, `OAI_Laughlin_Certificate_computeLDL_23_11_9`, `OAI.Laughlin.Certificate.computeLDL_23_11_9_s50`, `OAI_Laughlin_Certificate_computeLDL_23_1_10`, `OAI.Laughlin.Certificate.computeLDL_23_1_10_s50`, `OAI_Laughlin_Certificate_computeLDL_23_1_11`, `OAI.Laughlin.Certificate.computeLDL_23_1_11_s50`, `OAI_Laughlin_Certificate_computeLDL_23_2_10`, `OAI.Laughlin.Certificate.computeLDL_23_2_10_s50`, `OAI_Laughlin_Certificate_computeLDL_23_2_11`, `OAI.Laughlin.Certificate.computeLDL_23_2_11_s50`, `OAI_Laughlin_Certificate_computeLDL_23_2_3`, `OAI.Laughlin.Certificate.computeLDL_23_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_23_2_4`, `OAI.Laughlin.Certificate.computeLDL_23_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_23_2_5`, `OAI.Laughlin.Certificate.computeLDL_23_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_23_2_6`, `OAI.Laughlin.Certificate.computeLDL_23_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_23_2_7`, `OAI.Laughlin.Certificate.computeLDL_23_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_23_2_8`, `OAI.Laughlin.Certificate.computeLDL_23_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_23_2_9`, `OAI.Laughlin.Certificate.computeLDL_23_2_9_s50`, `OAI_Laughlin_Certificate_computeLDL_23_3_0`, `OAI.Laughlin.Certificate.computeLDL_23_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_23_3_1`, `OAI_Laughlin_Certificate_computeLDL_23_3_10`, `OAI.Laughlin.Certificate.computeLDL_23_3_10_s50`, `OAI_Laughlin_Certificate_computeLDL_23_3_11`, `OAI.Laughlin.Certificate.computeLDL_23_3_11_s50`, `OAI.Laughlin.Certificate.computeLDL_23_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_23_3_2`, `OAI.Laughlin.Certificate.computeLDL_23_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_23_3_3`, `OAI.Laughlin.Certificate.computeLDL_23_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_23_3_4`, `OAI.Laughlin.Certificate.computeLDL_23_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_23_3_5`, `OAI.Laughlin.Certificate.computeLDL_23_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_23_3_6`, `OAI.Laughlin.Certificate.computeLDL_23_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_23_3_7`, `OAI.Laughlin.Certificate.computeLDL_23_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_23_3_8`, `OAI.Laughlin.Certificate.computeLDL_23_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_23_3_9`, `OAI.Laughlin.Certificate.computeLDL_23_3_9_s50`, `OAI_Laughlin_Certificate_computeLDL_23_4_0`, `OAI.Laughlin.Certificate.computeLDL_23_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_23_4_1`, `OAI_Laughlin_Certificate_computeLDL_23_4_10`, `OAI.Laughlin.Certificate.computeLDL_23_4_10_s50`, `OAI_Laughlin_Certificate_computeLDL_23_4_11`, `OAI.Laughlin.Certificate.computeLDL_23_4_11_s50`, `OAI.Laughlin.Certificate.computeLDL_23_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_23_4_2`, `OAI.Laughlin.Certificate.computeLDL_23_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_23_4_3`, `OAI.Laughlin.Certificate.computeLDL_23_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_23_4_4`, `OAI.Laughlin.Certificate.computeLDL_23_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_23_4_5`, `OAI.Laughlin.Certificate.computeLDL_23_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_23_4_6`, `OAI.Laughlin.Certificate.computeLDL_23_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_23_4_7`, `OAI.Laughlin.Certificate.computeLDL_23_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_23_4_8`, `OAI.Laughlin.Certificate.computeLDL_23_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_23_4_9`, `OAI.Laughlin.Certificate.computeLDL_23_4_9_s50`, `OAI_Laughlin_Certificate_computeLDL_23_5_0`, `OAI.Laughlin.Certificate.computeLDL_23_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_23_5_1`, `OAI_Laughlin_Certificate_computeLDL_23_5_10`, `OAI.Laughlin.Certificate.computeLDL_23_5_10_s50`, `OAI_Laughlin_Certificate_computeLDL_23_5_11`, `OAI.Laughlin.Certificate.computeLDL_23_5_11_s50`, `OAI.Laughlin.Certificate.computeLDL_23_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_23_5_2`, `OAI.Laughlin.Certificate.computeLDL_23_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_23_5_3`, `OAI.Laughlin.Certificate.computeLDL_23_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_23_5_4`, `OAI.Laughlin.Certificate.computeLDL_23_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_23_5_5`, `OAI.Laughlin.Certificate.computeLDL_23_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_23_5_6`, `OAI.Laughlin.Certificate.computeLDL_23_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_23_5_7`, `OAI.Laughlin.Certificate.computeLDL_23_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_23_5_8`, `OAI.Laughlin.Certificate.computeLDL_23_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_23_5_9`, `OAI.Laughlin.Certificate.computeLDL_23_5_9_s50`, `OAI_Laughlin_Certificate_computeLDL_23_6_0`, `OAI.Laughlin.Certificate.computeLDL_23_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_23_6_1`, `OAI_Laughlin_Certificate_computeLDL_23_6_10`, `OAI.Laughlin.Certificate.computeLDL_23_6_10_s50`, `OAI_Laughlin_Certificate_computeLDL_23_6_11`, `OAI.Laughlin.Certificate.computeLDL_23_6_11_s50`, `OAI.Laughlin.Certificate.computeLDL_23_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_23_6_2`, `OAI.Laughlin.Certificate.computeLDL_23_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_23_6_3`, `OAI.Laughlin.Certificate.computeLDL_23_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_23_6_4`, `OAI.Laughlin.Certificate.computeLDL_23_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_23_6_5`, `OAI.Laughlin.Certificate.computeLDL_23_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_23_6_6`, `OAI.Laughlin.Certificate.computeLDL_23_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_23_6_7`, `OAI.Laughlin.Certificate.computeLDL_23_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_23_6_8`, `OAI.Laughlin.Certificate.computeLDL_23_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_23_6_9`, `OAI.Laughlin.Certificate.computeLDL_23_6_9_s50`, `OAI_Laughlin_Certificate_computeLDL_23_7_0`, `OAI.Laughlin.Certificate.computeLDL_23_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_23_7_1`, `OAI_Laughlin_Certificate_computeLDL_23_7_10`, `OAI.Laughlin.Certificate.computeLDL_23_7_10_s50`, `OAI_Laughlin_Certificate_computeLDL_23_7_11`, `OAI.Laughlin.Certificate.computeLDL_23_7_11_s50`, `OAI.Laughlin.Certificate.computeLDL_23_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_23_7_2`, `OAI.Laughlin.Certificate.computeLDL_23_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_23_7_3`, `OAI.Laughlin.Certificate.computeLDL_23_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_23_7_4`, `OAI.Laughlin.Certificate.computeLDL_23_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_23_7_5`, `OAI.Laughlin.Certificate.computeLDL_23_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_23_7_6`, `OAI.Laughlin.Certificate.computeLDL_23_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_23_7_7`, `OAI.Laughlin.Certificate.computeLDL_23_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_23_7_8`, `OAI.Laughlin.Certificate.computeLDL_23_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_23_7_9`, `OAI.Laughlin.Certificate.computeLDL_23_7_9_s50`, `OAI_Laughlin_Certificate_computeLDL_23_8_0`, `OAI.Laughlin.Certificate.computeLDL_23_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_23_8_1`, `OAI_Laughlin_Certificate_computeLDL_23_8_10`, `OAI.Laughlin.Certificate.computeLDL_23_8_10_s50`, `OAI_Laughlin_Certificate_computeLDL_23_8_11`, `OAI.Laughlin.Certificate.computeLDL_23_8_11_s50`, `OAI.Laughlin.Certificate.computeLDL_23_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_23_8_2`, `OAI.Laughlin.Certificate.computeLDL_23_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_23_8_3`, `OAI.Laughlin.Certificate.computeLDL_23_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_23_8_4`, `OAI.Laughlin.Certificate.computeLDL_23_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_23_8_5`, `OAI.Laughlin.Certificate.computeLDL_23_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_23_8_6`, `OAI.Laughlin.Certificate.computeLDL_23_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_23_8_7`, `OAI.Laughlin.Certificate.computeLDL_23_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_23_8_8`, `OAI.Laughlin.Certificate.computeLDL_23_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_23_8_9`, `OAI.Laughlin.Certificate.computeLDL_23_8_9_s50`, `OAI_Laughlin_Certificate_computeLDL_23_9_0`, `OAI.Laughlin.Certificate.computeLDL_23_9_0_s50`, `OAI_Laughlin_Certificate_computeLDL_23_9_1`, `OAI_Laughlin_Certificate_computeLDL_23_9_10`, `OAI.Laughlin.Certificate.computeLDL_23_9_10_s50`, `OAI_Laughlin_Certificate_computeLDL_23_9_11`, `OAI.Laughlin.Certificate.computeLDL_23_9_11_s50`, `OAI.Laughlin.Certificate.computeLDL_23_9_1_s50`, `OAI_Laughlin_Certificate_computeLDL_23_9_2`, `OAI.Laughlin.Certificate.computeLDL_23_9_2_s50`, `OAI_Laughlin_Certificate_computeLDL_23_9_3`, `OAI.Laughlin.Certificate.computeLDL_23_9_3_s50`, `OAI_Laughlin_Certificate_computeLDL_23_9_4`, `OAI.Laughlin.Certificate.computeLDL_23_9_4_s50`, `OAI_Laughlin_Certificate_computeLDL_23_9_5`, `OAI.Laughlin.Certificate.computeLDL_23_9_5_s50`, `OAI_Laughlin_Certificate_computeLDL_23_9_6`, `OAI.Laughlin.Certificate.computeLDL_23_9_6_s50`, `OAI_Laughlin_Certificate_computeLDL_23_9_7`, `OAI.Laughlin.Certificate.computeLDL_23_9_7_s50`, `OAI_Laughlin_Certificate_computeLDL_23_9_8`, `OAI.Laughlin.Certificate.computeLDL_23_9_8_s50`, `OAI_Laughlin_Certificate_computeLDL_23_9_9`, `OAI.Laughlin.Certificate.computeLDL_23_9_9_s50`, `OAI_Laughlin_Certificate_error_9`, `OAI.Laughlin.Certificate.error_9_s50`, `OAI_Laughlin_Certificate_gram_14`, `OAI.Laughlin.Certificate.gram_14_s50`, `OAI_Laughlin_Certificate_gram_15`, `OAI.Laughlin.Certificate.gram_15_s50`, `OAI_Laughlin_Certificate_gram_16`, `OAI.Laughlin.Certificate.gram_16_s50`, `OAI_Laughlin_Certificate_gram_17`, `OAI.Laughlin.Certificate.gram_17_s50`, `OAI_Laughlin_Certificate_gram_18`, `OAI.Laughlin.Certificate.gram_18_s50`, `OAI_Laughlin_Certificate_gram_19`, `OAI.Laughlin.Certificate.gram_19_s50`, `OAI_Laughlin_Certificate_gram_20`, `OAI.Laughlin.Certificate.gram_20_s50`, `OAI_Laughlin_Certificate_gram_21`, `OAI.Laughlin.Certificate.gram_21_s50`, `OAI_Laughlin_Certificate_gram_22`, `OAI.Laughlin.Certificate.gram_22_s50`, `OAI_Laughlin_Certificate_gram_23`, `OAI.Laughlin.Certificate.gram_23_s50`, `OAI_Laughlin_Certificate_gram_9`, `OAI.Laughlin.Certificate.gram_9_s50`, `OAI_Laughlin_Certificate_ldl_12`, `OAI.Laughlin.Certificate.ldl_12_s50`, `OAI_Laughlin_Certificate_ldl_five` and `OAI.Laughlin.Certificate.ldl_five_s50`; the proofs of `OAI_Laughlin_Certificate_candidateLDL_10`, `OAI.Laughlin.Certificate.candidateLDL_10_s50`, `OAI_Laughlin_Certificate_candidateLDL_11`, `OAI.Laughlin.Certificate.candidateLDL_11_s50`, `OAI_Laughlin_Certificate_candidateLDL_12`, `OAI.Laughlin.Certificate.candidateLDL_12_s50`, `OAI_Laughlin_Certificate_candidateLDL_14`, `OAI.Laughlin.Certificate.candidateLDL_14_s50`, `OAI_Laughlin_Certificate_candidateLDL_15`, `OAI.Laughlin.Certificate.candidateLDL_15_s50`, `OAI_Laughlin_Certificate_candidateLDL_16`, `OAI.Laughlin.Certificate.candidateLDL_16_s50`, `OAI_Laughlin_Certificate_candidateLDL_17`, `OAI.Laughlin.Certificate.candidateLDL_17_s50`, `OAI_Laughlin_Certificate_candidateLDL_18`, `OAI.Laughlin.Certificate.candidateLDL_18_s50`, `OAI_Laughlin_Certificate_candidateLDL_19`, `OAI.Laughlin.Certificate.candidateLDL_19_s50`, `OAI_Laughlin_Certificate_candidateLDL_20`, `OAI.Laughlin.Certificate.candidateLDL_20_s50`, `OAI_Laughlin_Certificate_candidateLDL_21`, `OAI.Laughlin.Certificate.candidateLDL_21_s50`, `OAI_Laughlin_Certificate_candidateLDL_22`, `OAI.Laughlin.Certificate.candidateLDL_22_s50`, `OAI_Laughlin_Certificate_candidateLDL_23`, `OAI.Laughlin.Certificate.candidateLDL_23_s50`, `OAI_Laughlin_Certificate_candidateLDL_9`, `OAI.Laughlin.Certificate.candidateLDL_9_s50`, `OAI_Laughlin_Certificate_computeLDL_11_5_5`, `OAI.Laughlin.Certificate.computeLDL_11_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_1_5`, `OAI.Laughlin.Certificate.computeLDL_12_1_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_0`, `OAI.Laughlin.Certificate.computeLDL_12_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_1`, `OAI.Laughlin.Certificate.computeLDL_12_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_2`, `OAI.Laughlin.Certificate.computeLDL_12_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_3`, `OAI.Laughlin.Certificate.computeLDL_12_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_4`, `OAI.Laughlin.Certificate.computeLDL_12_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_5`, `OAI.Laughlin.Certificate.computeLDL_12_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_0`, `OAI.Laughlin.Certificate.computeLDL_12_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_1`, `OAI.Laughlin.Certificate.computeLDL_12_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_2`, `OAI.Laughlin.Certificate.computeLDL_12_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_3`, `OAI.Laughlin.Certificate.computeLDL_12_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_4`, `OAI.Laughlin.Certificate.computeLDL_12_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_5`, `OAI.Laughlin.Certificate.computeLDL_12_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_0`, `OAI.Laughlin.Certificate.computeLDL_12_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_1`, `OAI.Laughlin.Certificate.computeLDL_12_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_2`, `OAI.Laughlin.Certificate.computeLDL_12_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_3`, `OAI.Laughlin.Certificate.computeLDL_12_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_4`, `OAI.Laughlin.Certificate.computeLDL_12_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_5`, `OAI.Laughlin.Certificate.computeLDL_12_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_0`, `OAI.Laughlin.Certificate.computeLDL_12_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_1`, `OAI.Laughlin.Certificate.computeLDL_12_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_2`, `OAI.Laughlin.Certificate.computeLDL_12_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_3`, `OAI.Laughlin.Certificate.computeLDL_12_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_4`, `OAI.Laughlin.Certificate.computeLDL_12_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_5`, `OAI.Laughlin.Certificate.computeLDL_12_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_14_1_6`, `OAI.Laughlin.Certificate.computeLDL_14_1_6_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_0`, `OAI.Laughlin.Certificate.computeLDL_14_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_1`, `OAI.Laughlin.Certificate.computeLDL_14_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_2`, `OAI.Laughlin.Certificate.computeLDL_14_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_3`, `OAI.Laughlin.Certificate.computeLDL_14_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_4`, `OAI.Laughlin.Certificate.computeLDL_14_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_5`, `OAI.Laughlin.Certificate.computeLDL_14_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_14_2_6`, `OAI.Laughlin.Certificate.computeLDL_14_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_0`, `OAI.Laughlin.Certificate.computeLDL_14_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_1`, `OAI.Laughlin.Certificate.computeLDL_14_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_2`, `OAI.Laughlin.Certificate.computeLDL_14_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_3`, `OAI.Laughlin.Certificate.computeLDL_14_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_4`, `OAI.Laughlin.Certificate.computeLDL_14_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_5`, `OAI.Laughlin.Certificate.computeLDL_14_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_14_3_6`, `OAI.Laughlin.Certificate.computeLDL_14_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_0`, `OAI.Laughlin.Certificate.computeLDL_14_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_1`, `OAI.Laughlin.Certificate.computeLDL_14_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_2`, `OAI.Laughlin.Certificate.computeLDL_14_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_3`, `OAI.Laughlin.Certificate.computeLDL_14_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_4`, `OAI.Laughlin.Certificate.computeLDL_14_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_5`, `OAI.Laughlin.Certificate.computeLDL_14_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_14_4_6`, `OAI.Laughlin.Certificate.computeLDL_14_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_0`, `OAI.Laughlin.Certificate.computeLDL_14_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_1`, `OAI.Laughlin.Certificate.computeLDL_14_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_2`, `OAI.Laughlin.Certificate.computeLDL_14_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_3`, `OAI.Laughlin.Certificate.computeLDL_14_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_4`, `OAI.Laughlin.Certificate.computeLDL_14_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_5`, `OAI.Laughlin.Certificate.computeLDL_14_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_14_5_6`, `OAI.Laughlin.Certificate.computeLDL_14_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_0`, `OAI.Laughlin.Certificate.computeLDL_14_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_1`, `OAI.Laughlin.Certificate.computeLDL_14_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_2`, `OAI.Laughlin.Certificate.computeLDL_14_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_3`, `OAI.Laughlin.Certificate.computeLDL_14_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_4`, `OAI.Laughlin.Certificate.computeLDL_14_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_5`, `OAI.Laughlin.Certificate.computeLDL_14_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_14_6_6`, `OAI.Laughlin.Certificate.computeLDL_14_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_1_7`, `OAI.Laughlin.Certificate.computeLDL_15_1_7_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_0`, `OAI.Laughlin.Certificate.computeLDL_15_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_1`, `OAI.Laughlin.Certificate.computeLDL_15_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_2`, `OAI.Laughlin.Certificate.computeLDL_15_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_3`, `OAI.Laughlin.Certificate.computeLDL_15_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_4`, `OAI.Laughlin.Certificate.computeLDL_15_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_5`, `OAI.Laughlin.Certificate.computeLDL_15_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_6`, `OAI.Laughlin.Certificate.computeLDL_15_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_7`, `OAI.Laughlin.Certificate.computeLDL_15_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_0`, `OAI.Laughlin.Certificate.computeLDL_15_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_1`, `OAI.Laughlin.Certificate.computeLDL_15_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_2`, `OAI.Laughlin.Certificate.computeLDL_15_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_3`, `OAI.Laughlin.Certificate.computeLDL_15_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_4`, `OAI.Laughlin.Certificate.computeLDL_15_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_5`, `OAI.Laughlin.Certificate.computeLDL_15_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_6`, `OAI.Laughlin.Certificate.computeLDL_15_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_7`, `OAI.Laughlin.Certificate.computeLDL_15_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_0`, `OAI.Laughlin.Certificate.computeLDL_15_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_1`, `OAI.Laughlin.Certificate.computeLDL_15_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_2`, `OAI.Laughlin.Certificate.computeLDL_15_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_3`, `OAI.Laughlin.Certificate.computeLDL_15_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_4`, `OAI.Laughlin.Certificate.computeLDL_15_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_5`, `OAI.Laughlin.Certificate.computeLDL_15_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_6`, `OAI.Laughlin.Certificate.computeLDL_15_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_7`, `OAI.Laughlin.Certificate.computeLDL_15_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_0`, `OAI.Laughlin.Certificate.computeLDL_15_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_1`, `OAI.Laughlin.Certificate.computeLDL_15_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_2`, `OAI.Laughlin.Certificate.computeLDL_15_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_3`, `OAI.Laughlin.Certificate.computeLDL_15_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_4`, `OAI.Laughlin.Certificate.computeLDL_15_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_5`, `OAI.Laughlin.Certificate.computeLDL_15_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_6`, `OAI.Laughlin.Certificate.computeLDL_15_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_7`, `OAI.Laughlin.Certificate.computeLDL_15_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_0`, `OAI.Laughlin.Certificate.computeLDL_15_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_1`, `OAI.Laughlin.Certificate.computeLDL_15_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_2`, `OAI.Laughlin.Certificate.computeLDL_15_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_3`, `OAI.Laughlin.Certificate.computeLDL_15_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_4`, `OAI.Laughlin.Certificate.computeLDL_15_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_5`, `OAI.Laughlin.Certificate.computeLDL_15_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_6`, `OAI.Laughlin.Certificate.computeLDL_15_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_7`, `OAI.Laughlin.Certificate.computeLDL_15_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_0`, `OAI.Laughlin.Certificate.computeLDL_15_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_1`, `OAI.Laughlin.Certificate.computeLDL_15_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_2`, `OAI.Laughlin.Certificate.computeLDL_15_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_3`, `OAI.Laughlin.Certificate.computeLDL_15_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_4`, `OAI.Laughlin.Certificate.computeLDL_15_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_5`, `OAI.Laughlin.Certificate.computeLDL_15_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_6`, `OAI.Laughlin.Certificate.computeLDL_15_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_7`, `OAI.Laughlin.Certificate.computeLDL_15_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_1_7`, `OAI.Laughlin.Certificate.computeLDL_16_1_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_0`, `OAI.Laughlin.Certificate.computeLDL_16_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_1`, `OAI.Laughlin.Certificate.computeLDL_16_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_2`, `OAI.Laughlin.Certificate.computeLDL_16_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_3`, `OAI.Laughlin.Certificate.computeLDL_16_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_4`, `OAI.Laughlin.Certificate.computeLDL_16_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_5`, `OAI.Laughlin.Certificate.computeLDL_16_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_6`, `OAI.Laughlin.Certificate.computeLDL_16_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_2_7`, `OAI.Laughlin.Certificate.computeLDL_16_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_0`, `OAI.Laughlin.Certificate.computeLDL_16_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_1`, `OAI.Laughlin.Certificate.computeLDL_16_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_2`, `OAI.Laughlin.Certificate.computeLDL_16_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_3`, `OAI.Laughlin.Certificate.computeLDL_16_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_4`, `OAI.Laughlin.Certificate.computeLDL_16_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_5`, `OAI.Laughlin.Certificate.computeLDL_16_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_6`, `OAI.Laughlin.Certificate.computeLDL_16_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_3_7`, `OAI.Laughlin.Certificate.computeLDL_16_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_0`, `OAI.Laughlin.Certificate.computeLDL_16_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_1`, `OAI.Laughlin.Certificate.computeLDL_16_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_2`, `OAI.Laughlin.Certificate.computeLDL_16_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_3`, `OAI.Laughlin.Certificate.computeLDL_16_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_4`, `OAI.Laughlin.Certificate.computeLDL_16_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_5`, `OAI.Laughlin.Certificate.computeLDL_16_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_6`, `OAI.Laughlin.Certificate.computeLDL_16_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_4_7`, `OAI.Laughlin.Certificate.computeLDL_16_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_0`, `OAI.Laughlin.Certificate.computeLDL_16_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_1`, `OAI.Laughlin.Certificate.computeLDL_16_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_2`, `OAI.Laughlin.Certificate.computeLDL_16_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_3`, `OAI.Laughlin.Certificate.computeLDL_16_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_4`, `OAI.Laughlin.Certificate.computeLDL_16_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_5`, `OAI.Laughlin.Certificate.computeLDL_16_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_6`, `OAI.Laughlin.Certificate.computeLDL_16_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_5_7`, `OAI.Laughlin.Certificate.computeLDL_16_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_0`, `OAI.Laughlin.Certificate.computeLDL_16_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_1`, `OAI.Laughlin.Certificate.computeLDL_16_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_2`, `OAI.Laughlin.Certificate.computeLDL_16_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_3`, `OAI.Laughlin.Certificate.computeLDL_16_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_4`, `OAI.Laughlin.Certificate.computeLDL_16_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_5`, `OAI.Laughlin.Certificate.computeLDL_16_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_6`, `OAI.Laughlin.Certificate.computeLDL_16_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_6_7`, `OAI.Laughlin.Certificate.computeLDL_16_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_0`, `OAI.Laughlin.Certificate.computeLDL_16_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_1`, `OAI.Laughlin.Certificate.computeLDL_16_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_2`, `OAI.Laughlin.Certificate.computeLDL_16_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_3`, `OAI.Laughlin.Certificate.computeLDL_16_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_4`, `OAI.Laughlin.Certificate.computeLDL_16_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_5`, `OAI.Laughlin.Certificate.computeLDL_16_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_6`, `OAI.Laughlin.Certificate.computeLDL_16_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_16_7_7`, `OAI.Laughlin.Certificate.computeLDL_16_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_1_8`, `OAI.Laughlin.Certificate.computeLDL_17_1_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_0`, `OAI.Laughlin.Certificate.computeLDL_17_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_1`, `OAI.Laughlin.Certificate.computeLDL_17_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_2`, `OAI.Laughlin.Certificate.computeLDL_17_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_3`, `OAI.Laughlin.Certificate.computeLDL_17_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_4`, `OAI.Laughlin.Certificate.computeLDL_17_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_5`, `OAI.Laughlin.Certificate.computeLDL_17_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_6`, `OAI.Laughlin.Certificate.computeLDL_17_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_7`, `OAI.Laughlin.Certificate.computeLDL_17_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_2_8`, `OAI.Laughlin.Certificate.computeLDL_17_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_0`, `OAI.Laughlin.Certificate.computeLDL_17_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_1`, `OAI.Laughlin.Certificate.computeLDL_17_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_2`, `OAI.Laughlin.Certificate.computeLDL_17_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_3`, `OAI.Laughlin.Certificate.computeLDL_17_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_4`, `OAI.Laughlin.Certificate.computeLDL_17_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_5`, `OAI.Laughlin.Certificate.computeLDL_17_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_6`, `OAI.Laughlin.Certificate.computeLDL_17_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_7`, `OAI.Laughlin.Certificate.computeLDL_17_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_3_8`, `OAI.Laughlin.Certificate.computeLDL_17_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_0`, `OAI.Laughlin.Certificate.computeLDL_17_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_1`, `OAI.Laughlin.Certificate.computeLDL_17_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_2`, `OAI.Laughlin.Certificate.computeLDL_17_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_3`, `OAI.Laughlin.Certificate.computeLDL_17_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_4`, `OAI.Laughlin.Certificate.computeLDL_17_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_5`, `OAI.Laughlin.Certificate.computeLDL_17_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_6`, `OAI.Laughlin.Certificate.computeLDL_17_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_7`, `OAI.Laughlin.Certificate.computeLDL_17_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_4_8`, `OAI.Laughlin.Certificate.computeLDL_17_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_0`, `OAI.Laughlin.Certificate.computeLDL_17_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_1`, `OAI.Laughlin.Certificate.computeLDL_17_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_2`, `OAI.Laughlin.Certificate.computeLDL_17_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_3`, `OAI.Laughlin.Certificate.computeLDL_17_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_4`, `OAI.Laughlin.Certificate.computeLDL_17_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_5`, `OAI.Laughlin.Certificate.computeLDL_17_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_6`, `OAI.Laughlin.Certificate.computeLDL_17_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_7`, `OAI.Laughlin.Certificate.computeLDL_17_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_5_8`, `OAI.Laughlin.Certificate.computeLDL_17_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_0`, `OAI.Laughlin.Certificate.computeLDL_17_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_1`, `OAI.Laughlin.Certificate.computeLDL_17_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_2`, `OAI.Laughlin.Certificate.computeLDL_17_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_3`, `OAI.Laughlin.Certificate.computeLDL_17_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_4`, `OAI.Laughlin.Certificate.computeLDL_17_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_5`, `OAI.Laughlin.Certificate.computeLDL_17_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_6`, `OAI.Laughlin.Certificate.computeLDL_17_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_7`, `OAI.Laughlin.Certificate.computeLDL_17_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_6_8`, `OAI.Laughlin.Certificate.computeLDL_17_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_0`, `OAI.Laughlin.Certificate.computeLDL_17_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_1`, `OAI.Laughlin.Certificate.computeLDL_17_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_2`, `OAI.Laughlin.Certificate.computeLDL_17_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_3`, `OAI.Laughlin.Certificate.computeLDL_17_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_4`, `OAI.Laughlin.Certificate.computeLDL_17_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_5`, `OAI.Laughlin.Certificate.computeLDL_17_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_6`, `OAI.Laughlin.Certificate.computeLDL_17_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_7`, `OAI.Laughlin.Certificate.computeLDL_17_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_7_8`, `OAI.Laughlin.Certificate.computeLDL_17_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_0`, `OAI.Laughlin.Certificate.computeLDL_17_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_1`, `OAI.Laughlin.Certificate.computeLDL_17_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_2`, `OAI.Laughlin.Certificate.computeLDL_17_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_3`, `OAI.Laughlin.Certificate.computeLDL_17_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_4`, `OAI.Laughlin.Certificate.computeLDL_17_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_5`, `OAI.Laughlin.Certificate.computeLDL_17_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_6`, `OAI.Laughlin.Certificate.computeLDL_17_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_7`, `OAI.Laughlin.Certificate.computeLDL_17_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_17_8_8`, `OAI.Laughlin.Certificate.computeLDL_17_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_1_8`, `OAI.Laughlin.Certificate.computeLDL_18_1_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_0`, `OAI.Laughlin.Certificate.computeLDL_18_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_1`, `OAI.Laughlin.Certificate.computeLDL_18_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_2`, `OAI.Laughlin.Certificate.computeLDL_18_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_3`, `OAI.Laughlin.Certificate.computeLDL_18_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_4`, `OAI.Laughlin.Certificate.computeLDL_18_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_5`, `OAI.Laughlin.Certificate.computeLDL_18_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_6`, `OAI.Laughlin.Certificate.computeLDL_18_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_7`, `OAI.Laughlin.Certificate.computeLDL_18_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_2_8`, `OAI.Laughlin.Certificate.computeLDL_18_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_0`, `OAI.Laughlin.Certificate.computeLDL_18_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_1`, `OAI.Laughlin.Certificate.computeLDL_18_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_2`, `OAI.Laughlin.Certificate.computeLDL_18_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_3`, `OAI.Laughlin.Certificate.computeLDL_18_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_4`, `OAI.Laughlin.Certificate.computeLDL_18_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_5`, `OAI.Laughlin.Certificate.computeLDL_18_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_6`, `OAI.Laughlin.Certificate.computeLDL_18_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_7`, `OAI.Laughlin.Certificate.computeLDL_18_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_3_8`, `OAI.Laughlin.Certificate.computeLDL_18_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_0`, `OAI.Laughlin.Certificate.computeLDL_18_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_1`, `OAI.Laughlin.Certificate.computeLDL_18_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_2`, `OAI.Laughlin.Certificate.computeLDL_18_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_3`, `OAI.Laughlin.Certificate.computeLDL_18_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_4`, `OAI.Laughlin.Certificate.computeLDL_18_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_5`, `OAI.Laughlin.Certificate.computeLDL_18_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_6`, `OAI.Laughlin.Certificate.computeLDL_18_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_7`, `OAI.Laughlin.Certificate.computeLDL_18_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_4_8`, `OAI.Laughlin.Certificate.computeLDL_18_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_0`, `OAI.Laughlin.Certificate.computeLDL_18_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_1`, `OAI.Laughlin.Certificate.computeLDL_18_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_2`, `OAI.Laughlin.Certificate.computeLDL_18_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_3`, `OAI.Laughlin.Certificate.computeLDL_18_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_4`, `OAI.Laughlin.Certificate.computeLDL_18_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_5`, `OAI.Laughlin.Certificate.computeLDL_18_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_6`, `OAI.Laughlin.Certificate.computeLDL_18_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_7`, `OAI.Laughlin.Certificate.computeLDL_18_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_5_8`, `OAI.Laughlin.Certificate.computeLDL_18_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_0`, `OAI.Laughlin.Certificate.computeLDL_18_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_1`, `OAI.Laughlin.Certificate.computeLDL_18_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_2`, `OAI.Laughlin.Certificate.computeLDL_18_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_3`, `OAI.Laughlin.Certificate.computeLDL_18_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_4`, `OAI.Laughlin.Certificate.computeLDL_18_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_5`, `OAI.Laughlin.Certificate.computeLDL_18_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_6`, `OAI.Laughlin.Certificate.computeLDL_18_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_7`, `OAI.Laughlin.Certificate.computeLDL_18_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_6_8`, `OAI.Laughlin.Certificate.computeLDL_18_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_0`, `OAI.Laughlin.Certificate.computeLDL_18_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_1`, `OAI.Laughlin.Certificate.computeLDL_18_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_2`, `OAI.Laughlin.Certificate.computeLDL_18_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_3`, `OAI.Laughlin.Certificate.computeLDL_18_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_4`, `OAI.Laughlin.Certificate.computeLDL_18_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_5`, `OAI.Laughlin.Certificate.computeLDL_18_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_6`, `OAI.Laughlin.Certificate.computeLDL_18_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_7`, `OAI.Laughlin.Certificate.computeLDL_18_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_7_8`, `OAI.Laughlin.Certificate.computeLDL_18_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_0`, `OAI.Laughlin.Certificate.computeLDL_18_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_1`, `OAI.Laughlin.Certificate.computeLDL_18_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_2`, `OAI.Laughlin.Certificate.computeLDL_18_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_3`, `OAI.Laughlin.Certificate.computeLDL_18_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_4`, `OAI.Laughlin.Certificate.computeLDL_18_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_5`, `OAI.Laughlin.Certificate.computeLDL_18_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_6`, `OAI.Laughlin.Certificate.computeLDL_18_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_7`, `OAI.Laughlin.Certificate.computeLDL_18_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_18_8_8`, `OAI.Laughlin.Certificate.computeLDL_18_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_1_9`, `OAI.Laughlin.Certificate.computeLDL_19_1_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_0`, `OAI.Laughlin.Certificate.computeLDL_19_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_1`, `OAI.Laughlin.Certificate.computeLDL_19_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_2`, `OAI.Laughlin.Certificate.computeLDL_19_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_3`, `OAI.Laughlin.Certificate.computeLDL_19_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_4`, `OAI.Laughlin.Certificate.computeLDL_19_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_5`, `OAI.Laughlin.Certificate.computeLDL_19_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_6`, `OAI.Laughlin.Certificate.computeLDL_19_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_7`, `OAI.Laughlin.Certificate.computeLDL_19_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_8`, `OAI.Laughlin.Certificate.computeLDL_19_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_2_9`, `OAI.Laughlin.Certificate.computeLDL_19_2_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_0`, `OAI.Laughlin.Certificate.computeLDL_19_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_1`, `OAI.Laughlin.Certificate.computeLDL_19_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_2`, `OAI.Laughlin.Certificate.computeLDL_19_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_3`, `OAI.Laughlin.Certificate.computeLDL_19_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_4`, `OAI.Laughlin.Certificate.computeLDL_19_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_5`, `OAI.Laughlin.Certificate.computeLDL_19_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_6`, `OAI.Laughlin.Certificate.computeLDL_19_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_7`, `OAI.Laughlin.Certificate.computeLDL_19_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_8`, `OAI.Laughlin.Certificate.computeLDL_19_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_3_9`, `OAI.Laughlin.Certificate.computeLDL_19_3_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_0`, `OAI.Laughlin.Certificate.computeLDL_19_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_1`, `OAI.Laughlin.Certificate.computeLDL_19_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_2`, `OAI.Laughlin.Certificate.computeLDL_19_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_3`, `OAI.Laughlin.Certificate.computeLDL_19_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_4`, `OAI.Laughlin.Certificate.computeLDL_19_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_5`, `OAI.Laughlin.Certificate.computeLDL_19_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_6`, `OAI.Laughlin.Certificate.computeLDL_19_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_7`, `OAI.Laughlin.Certificate.computeLDL_19_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_8`, `OAI.Laughlin.Certificate.computeLDL_19_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_4_9`, `OAI.Laughlin.Certificate.computeLDL_19_4_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_0`, `OAI.Laughlin.Certificate.computeLDL_19_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_1`, `OAI.Laughlin.Certificate.computeLDL_19_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_2`, `OAI.Laughlin.Certificate.computeLDL_19_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_3`, `OAI.Laughlin.Certificate.computeLDL_19_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_4`, `OAI.Laughlin.Certificate.computeLDL_19_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_5`, `OAI.Laughlin.Certificate.computeLDL_19_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_6`, `OAI.Laughlin.Certificate.computeLDL_19_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_7`, `OAI.Laughlin.Certificate.computeLDL_19_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_8`, `OAI.Laughlin.Certificate.computeLDL_19_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_5_9`, `OAI.Laughlin.Certificate.computeLDL_19_5_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_0`, `OAI.Laughlin.Certificate.computeLDL_19_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_1`, `OAI.Laughlin.Certificate.computeLDL_19_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_2`, `OAI.Laughlin.Certificate.computeLDL_19_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_3`, `OAI.Laughlin.Certificate.computeLDL_19_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_4`, `OAI.Laughlin.Certificate.computeLDL_19_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_5`, `OAI.Laughlin.Certificate.computeLDL_19_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_6`, `OAI.Laughlin.Certificate.computeLDL_19_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_7`, `OAI.Laughlin.Certificate.computeLDL_19_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_8`, `OAI.Laughlin.Certificate.computeLDL_19_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_6_9`, `OAI.Laughlin.Certificate.computeLDL_19_6_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_0`, `OAI.Laughlin.Certificate.computeLDL_19_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_1`, `OAI.Laughlin.Certificate.computeLDL_19_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_2`, `OAI.Laughlin.Certificate.computeLDL_19_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_3`, `OAI.Laughlin.Certificate.computeLDL_19_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_4`, `OAI.Laughlin.Certificate.computeLDL_19_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_5`, `OAI.Laughlin.Certificate.computeLDL_19_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_6`, `OAI.Laughlin.Certificate.computeLDL_19_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_7`, `OAI.Laughlin.Certificate.computeLDL_19_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_8`, `OAI.Laughlin.Certificate.computeLDL_19_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_7_9`, `OAI.Laughlin.Certificate.computeLDL_19_7_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_0`, `OAI.Laughlin.Certificate.computeLDL_19_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_1`, `OAI.Laughlin.Certificate.computeLDL_19_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_2`, `OAI.Laughlin.Certificate.computeLDL_19_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_3`, `OAI.Laughlin.Certificate.computeLDL_19_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_4`, `OAI.Laughlin.Certificate.computeLDL_19_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_5`, `OAI.Laughlin.Certificate.computeLDL_19_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_6`, `OAI.Laughlin.Certificate.computeLDL_19_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_7`, `OAI.Laughlin.Certificate.computeLDL_19_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_8`, `OAI.Laughlin.Certificate.computeLDL_19_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_8_9`, `OAI.Laughlin.Certificate.computeLDL_19_8_9_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_0`, `OAI.Laughlin.Certificate.computeLDL_19_9_0_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_1`, `OAI.Laughlin.Certificate.computeLDL_19_9_1_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_2`, `OAI.Laughlin.Certificate.computeLDL_19_9_2_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_3`, `OAI.Laughlin.Certificate.computeLDL_19_9_3_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_4`, `OAI.Laughlin.Certificate.computeLDL_19_9_4_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_5`, `OAI.Laughlin.Certificate.computeLDL_19_9_5_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_6`, `OAI.Laughlin.Certificate.computeLDL_19_9_6_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_7`, `OAI.Laughlin.Certificate.computeLDL_19_9_7_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_8`, `OAI.Laughlin.Certificate.computeLDL_19_9_8_s50`, `OAI_Laughlin_Certificate_computeLDL_19_9_9`, `OAI.Laughlin.Certificate.computeLDL_19_9_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_1_9`, `OAI.Laughlin.Certificate.computeLDL_20_1_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_0`, `OAI.Laughlin.Certificate.computeLDL_20_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_1`, `OAI.Laughlin.Certificate.computeLDL_20_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_2`, `OAI.Laughlin.Certificate.computeLDL_20_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_3`, `OAI.Laughlin.Certificate.computeLDL_20_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_4`, `OAI.Laughlin.Certificate.computeLDL_20_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_5`, `OAI.Laughlin.Certificate.computeLDL_20_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_6`, `OAI.Laughlin.Certificate.computeLDL_20_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_7`, `OAI.Laughlin.Certificate.computeLDL_20_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_8`, `OAI.Laughlin.Certificate.computeLDL_20_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_2_9`, `OAI.Laughlin.Certificate.computeLDL_20_2_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_0`, `OAI.Laughlin.Certificate.computeLDL_20_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_1`, `OAI.Laughlin.Certificate.computeLDL_20_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_2`, `OAI.Laughlin.Certificate.computeLDL_20_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_3`, `OAI.Laughlin.Certificate.computeLDL_20_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_4`, `OAI.Laughlin.Certificate.computeLDL_20_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_5`, `OAI.Laughlin.Certificate.computeLDL_20_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_6`, `OAI.Laughlin.Certificate.computeLDL_20_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_7`, `OAI.Laughlin.Certificate.computeLDL_20_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_8`, `OAI.Laughlin.Certificate.computeLDL_20_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_3_9`, `OAI.Laughlin.Certificate.computeLDL_20_3_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_0`, `OAI.Laughlin.Certificate.computeLDL_20_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_1`, `OAI.Laughlin.Certificate.computeLDL_20_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_2`, `OAI.Laughlin.Certificate.computeLDL_20_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_3`, `OAI.Laughlin.Certificate.computeLDL_20_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_4`, `OAI.Laughlin.Certificate.computeLDL_20_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_5`, `OAI.Laughlin.Certificate.computeLDL_20_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_6`, `OAI.Laughlin.Certificate.computeLDL_20_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_7`, `OAI.Laughlin.Certificate.computeLDL_20_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_8`, `OAI.Laughlin.Certificate.computeLDL_20_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_4_9`, `OAI.Laughlin.Certificate.computeLDL_20_4_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_0`, `OAI.Laughlin.Certificate.computeLDL_20_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_1`, `OAI.Laughlin.Certificate.computeLDL_20_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_2`, `OAI.Laughlin.Certificate.computeLDL_20_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_3`, `OAI.Laughlin.Certificate.computeLDL_20_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_4`, `OAI.Laughlin.Certificate.computeLDL_20_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_5`, `OAI.Laughlin.Certificate.computeLDL_20_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_6`, `OAI.Laughlin.Certificate.computeLDL_20_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_7`, `OAI.Laughlin.Certificate.computeLDL_20_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_8`, `OAI.Laughlin.Certificate.computeLDL_20_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_5_9`, `OAI.Laughlin.Certificate.computeLDL_20_5_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_0`, `OAI.Laughlin.Certificate.computeLDL_20_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_1`, `OAI.Laughlin.Certificate.computeLDL_20_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_2`, `OAI.Laughlin.Certificate.computeLDL_20_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_3`, `OAI.Laughlin.Certificate.computeLDL_20_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_4`, `OAI.Laughlin.Certificate.computeLDL_20_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_5`, `OAI.Laughlin.Certificate.computeLDL_20_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_6`, `OAI.Laughlin.Certificate.computeLDL_20_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_7`, `OAI.Laughlin.Certificate.computeLDL_20_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_8`, `OAI.Laughlin.Certificate.computeLDL_20_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_6_9`, `OAI.Laughlin.Certificate.computeLDL_20_6_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_0`, `OAI.Laughlin.Certificate.computeLDL_20_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_1`, `OAI.Laughlin.Certificate.computeLDL_20_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_2`, `OAI.Laughlin.Certificate.computeLDL_20_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_3`, `OAI.Laughlin.Certificate.computeLDL_20_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_4`, `OAI.Laughlin.Certificate.computeLDL_20_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_5`, `OAI.Laughlin.Certificate.computeLDL_20_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_6`, `OAI.Laughlin.Certificate.computeLDL_20_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_7`, `OAI.Laughlin.Certificate.computeLDL_20_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_8`, `OAI.Laughlin.Certificate.computeLDL_20_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_7_9`, `OAI.Laughlin.Certificate.computeLDL_20_7_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_0`, `OAI.Laughlin.Certificate.computeLDL_20_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_1`, `OAI.Laughlin.Certificate.computeLDL_20_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_2`, `OAI.Laughlin.Certificate.computeLDL_20_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_3`, `OAI.Laughlin.Certificate.computeLDL_20_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_4`, `OAI.Laughlin.Certificate.computeLDL_20_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_5`, `OAI.Laughlin.Certificate.computeLDL_20_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_6`, `OAI.Laughlin.Certificate.computeLDL_20_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_7`, `OAI.Laughlin.Certificate.computeLDL_20_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_8`, `OAI.Laughlin.Certificate.computeLDL_20_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_8_9`, `OAI.Laughlin.Certificate.computeLDL_20_8_9_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_0`, `OAI.Laughlin.Certificate.computeLDL_20_9_0_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_1`, `OAI.Laughlin.Certificate.computeLDL_20_9_1_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_2`, `OAI.Laughlin.Certificate.computeLDL_20_9_2_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_3`, `OAI.Laughlin.Certificate.computeLDL_20_9_3_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_4`, `OAI.Laughlin.Certificate.computeLDL_20_9_4_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_5`, `OAI.Laughlin.Certificate.computeLDL_20_9_5_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_6`, `OAI.Laughlin.Certificate.computeLDL_20_9_6_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_7`, `OAI.Laughlin.Certificate.computeLDL_20_9_7_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_8`, `OAI.Laughlin.Certificate.computeLDL_20_9_8_s50`, `OAI_Laughlin_Certificate_computeLDL_20_9_9`, `OAI.Laughlin.Certificate.computeLDL_20_9_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_0_10`, `OAI.Laughlin.Certificate.computeLDL_21_0_10_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_0`, `OAI.Laughlin.Certificate.computeLDL_21_10_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_1`, `OAI_Laughlin_Certificate_computeLDL_21_10_10`, `OAI.Laughlin.Certificate.computeLDL_21_10_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_10_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_2`, `OAI.Laughlin.Certificate.computeLDL_21_10_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_3`, `OAI.Laughlin.Certificate.computeLDL_21_10_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_4`, `OAI.Laughlin.Certificate.computeLDL_21_10_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_5`, `OAI.Laughlin.Certificate.computeLDL_21_10_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_6`, `OAI.Laughlin.Certificate.computeLDL_21_10_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_7`, `OAI.Laughlin.Certificate.computeLDL_21_10_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_8`, `OAI.Laughlin.Certificate.computeLDL_21_10_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_10_9`, `OAI.Laughlin.Certificate.computeLDL_21_10_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_1_10`, `OAI.Laughlin.Certificate.computeLDL_21_1_10_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_1`, `OAI_Laughlin_Certificate_computeLDL_21_2_10`, `OAI.Laughlin.Certificate.computeLDL_21_2_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_2`, `OAI.Laughlin.Certificate.computeLDL_21_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_3`, `OAI.Laughlin.Certificate.computeLDL_21_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_4`, `OAI.Laughlin.Certificate.computeLDL_21_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_5`, `OAI.Laughlin.Certificate.computeLDL_21_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_6`, `OAI.Laughlin.Certificate.computeLDL_21_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_7`, `OAI.Laughlin.Certificate.computeLDL_21_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_8`, `OAI.Laughlin.Certificate.computeLDL_21_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_2_9`, `OAI.Laughlin.Certificate.computeLDL_21_2_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_0`, `OAI.Laughlin.Certificate.computeLDL_21_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_1`, `OAI_Laughlin_Certificate_computeLDL_21_3_10`, `OAI.Laughlin.Certificate.computeLDL_21_3_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_2`, `OAI.Laughlin.Certificate.computeLDL_21_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_3`, `OAI.Laughlin.Certificate.computeLDL_21_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_4`, `OAI.Laughlin.Certificate.computeLDL_21_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_5`, `OAI.Laughlin.Certificate.computeLDL_21_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_6`, `OAI.Laughlin.Certificate.computeLDL_21_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_7`, `OAI.Laughlin.Certificate.computeLDL_21_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_8`, `OAI.Laughlin.Certificate.computeLDL_21_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_3_9`, `OAI.Laughlin.Certificate.computeLDL_21_3_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_0`, `OAI.Laughlin.Certificate.computeLDL_21_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_1`, `OAI_Laughlin_Certificate_computeLDL_21_4_10`, `OAI.Laughlin.Certificate.computeLDL_21_4_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_2`, `OAI.Laughlin.Certificate.computeLDL_21_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_3`, `OAI.Laughlin.Certificate.computeLDL_21_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_4`, `OAI.Laughlin.Certificate.computeLDL_21_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_5`, `OAI.Laughlin.Certificate.computeLDL_21_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_6`, `OAI.Laughlin.Certificate.computeLDL_21_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_7`, `OAI.Laughlin.Certificate.computeLDL_21_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_8`, `OAI.Laughlin.Certificate.computeLDL_21_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_4_9`, `OAI.Laughlin.Certificate.computeLDL_21_4_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_0`, `OAI.Laughlin.Certificate.computeLDL_21_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_1`, `OAI_Laughlin_Certificate_computeLDL_21_5_10`, `OAI.Laughlin.Certificate.computeLDL_21_5_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_2`, `OAI.Laughlin.Certificate.computeLDL_21_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_3`, `OAI.Laughlin.Certificate.computeLDL_21_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_4`, `OAI.Laughlin.Certificate.computeLDL_21_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_5`, `OAI.Laughlin.Certificate.computeLDL_21_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_6`, `OAI.Laughlin.Certificate.computeLDL_21_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_7`, `OAI.Laughlin.Certificate.computeLDL_21_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_8`, `OAI.Laughlin.Certificate.computeLDL_21_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_5_9`, `OAI.Laughlin.Certificate.computeLDL_21_5_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_0`, `OAI.Laughlin.Certificate.computeLDL_21_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_1`, `OAI_Laughlin_Certificate_computeLDL_21_6_10`, `OAI.Laughlin.Certificate.computeLDL_21_6_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_2`, `OAI.Laughlin.Certificate.computeLDL_21_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_3`, `OAI.Laughlin.Certificate.computeLDL_21_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_4`, `OAI.Laughlin.Certificate.computeLDL_21_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_5`, `OAI.Laughlin.Certificate.computeLDL_21_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_6`, `OAI.Laughlin.Certificate.computeLDL_21_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_7`, `OAI.Laughlin.Certificate.computeLDL_21_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_8`, `OAI.Laughlin.Certificate.computeLDL_21_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_6_9`, `OAI.Laughlin.Certificate.computeLDL_21_6_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_0`, `OAI.Laughlin.Certificate.computeLDL_21_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_1`, `OAI_Laughlin_Certificate_computeLDL_21_7_10`, `OAI.Laughlin.Certificate.computeLDL_21_7_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_2`, `OAI.Laughlin.Certificate.computeLDL_21_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_3`, `OAI.Laughlin.Certificate.computeLDL_21_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_4`, `OAI.Laughlin.Certificate.computeLDL_21_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_5`, `OAI.Laughlin.Certificate.computeLDL_21_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_6`, `OAI.Laughlin.Certificate.computeLDL_21_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_7`, `OAI.Laughlin.Certificate.computeLDL_21_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_8`, `OAI.Laughlin.Certificate.computeLDL_21_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_7_9`, `OAI.Laughlin.Certificate.computeLDL_21_7_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_0`, `OAI.Laughlin.Certificate.computeLDL_21_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_1`, `OAI_Laughlin_Certificate_computeLDL_21_8_10`, `OAI.Laughlin.Certificate.computeLDL_21_8_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_2`, `OAI.Laughlin.Certificate.computeLDL_21_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_3`, `OAI.Laughlin.Certificate.computeLDL_21_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_4`, `OAI.Laughlin.Certificate.computeLDL_21_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_5`, `OAI.Laughlin.Certificate.computeLDL_21_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_6`, `OAI.Laughlin.Certificate.computeLDL_21_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_7`, `OAI.Laughlin.Certificate.computeLDL_21_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_8`, `OAI.Laughlin.Certificate.computeLDL_21_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_8_9`, `OAI.Laughlin.Certificate.computeLDL_21_8_9_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_0`, `OAI.Laughlin.Certificate.computeLDL_21_9_0_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_1`, `OAI_Laughlin_Certificate_computeLDL_21_9_10`, `OAI.Laughlin.Certificate.computeLDL_21_9_10_s50`, `OAI.Laughlin.Certificate.computeLDL_21_9_1_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_2`, `OAI.Laughlin.Certificate.computeLDL_21_9_2_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_3`, `OAI.Laughlin.Certificate.computeLDL_21_9_3_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_4`, `OAI.Laughlin.Certificate.computeLDL_21_9_4_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_5`, `OAI.Laughlin.Certificate.computeLDL_21_9_5_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_6`, `OAI.Laughlin.Certificate.computeLDL_21_9_6_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_7`, `OAI.Laughlin.Certificate.computeLDL_21_9_7_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_8`, `OAI.Laughlin.Certificate.computeLDL_21_9_8_s50`, `OAI_Laughlin_Certificate_computeLDL_21_9_9`, `OAI.Laughlin.Certificate.computeLDL_21_9_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_0_10`, `OAI.Laughlin.Certificate.computeLDL_22_0_10_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_0`, `OAI.Laughlin.Certificate.computeLDL_22_10_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_1`, `OAI_Laughlin_Certificate_computeLDL_22_10_10`, `OAI.Laughlin.Certificate.computeLDL_22_10_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_10_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_2`, `OAI.Laughlin.Certificate.computeLDL_22_10_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_3`, `OAI.Laughlin.Certificate.computeLDL_22_10_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_4`, `OAI.Laughlin.Certificate.computeLDL_22_10_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_5`, `OAI.Laughlin.Certificate.computeLDL_22_10_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_6`, `OAI.Laughlin.Certificate.computeLDL_22_10_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_7`, `OAI.Laughlin.Certificate.computeLDL_22_10_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_8`, `OAI.Laughlin.Certificate.computeLDL_22_10_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_9`, `OAI.Laughlin.Certificate.computeLDL_22_10_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_1_10`, `OAI.Laughlin.Certificate.computeLDL_22_1_10_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_1`, `OAI_Laughlin_Certificate_computeLDL_22_2_10`, `OAI.Laughlin.Certificate.computeLDL_22_2_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_2`, `OAI.Laughlin.Certificate.computeLDL_22_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_3`, `OAI.Laughlin.Certificate.computeLDL_22_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_4`, `OAI.Laughlin.Certificate.computeLDL_22_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_5`, `OAI.Laughlin.Certificate.computeLDL_22_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_6`, `OAI.Laughlin.Certificate.computeLDL_22_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_7`, `OAI.Laughlin.Certificate.computeLDL_22_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_8`, `OAI.Laughlin.Certificate.computeLDL_22_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_9`, `OAI.Laughlin.Certificate.computeLDL_22_2_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_0`, `OAI.Laughlin.Certificate.computeLDL_22_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_1`, `OAI_Laughlin_Certificate_computeLDL_22_3_10`, `OAI.Laughlin.Certificate.computeLDL_22_3_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_2`, `OAI.Laughlin.Certificate.computeLDL_22_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_3`, `OAI.Laughlin.Certificate.computeLDL_22_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_4`, `OAI.Laughlin.Certificate.computeLDL_22_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_5`, `OAI.Laughlin.Certificate.computeLDL_22_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_6`, `OAI.Laughlin.Certificate.computeLDL_22_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_7`, `OAI.Laughlin.Certificate.computeLDL_22_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_8`, `OAI.Laughlin.Certificate.computeLDL_22_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_9`, `OAI.Laughlin.Certificate.computeLDL_22_3_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_0`, `OAI.Laughlin.Certificate.computeLDL_22_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_1`, `OAI_Laughlin_Certificate_computeLDL_22_4_10`, `OAI.Laughlin.Certificate.computeLDL_22_4_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_2`, `OAI.Laughlin.Certificate.computeLDL_22_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_3`, `OAI.Laughlin.Certificate.computeLDL_22_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_4`, `OAI.Laughlin.Certificate.computeLDL_22_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_5`, `OAI.Laughlin.Certificate.computeLDL_22_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_6`, `OAI.Laughlin.Certificate.computeLDL_22_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_7`, `OAI.Laughlin.Certificate.computeLDL_22_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_8`, `OAI.Laughlin.Certificate.computeLDL_22_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_9`, `OAI.Laughlin.Certificate.computeLDL_22_4_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_0`, `OAI.Laughlin.Certificate.computeLDL_22_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_1`, `OAI_Laughlin_Certificate_computeLDL_22_5_10`, `OAI.Laughlin.Certificate.computeLDL_22_5_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_2`, `OAI.Laughlin.Certificate.computeLDL_22_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_3`, `OAI.Laughlin.Certificate.computeLDL_22_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_4`, `OAI.Laughlin.Certificate.computeLDL_22_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_5`, `OAI.Laughlin.Certificate.computeLDL_22_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_6`, `OAI.Laughlin.Certificate.computeLDL_22_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_7`, `OAI.Laughlin.Certificate.computeLDL_22_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_8`, `OAI.Laughlin.Certificate.computeLDL_22_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_9`, `OAI.Laughlin.Certificate.computeLDL_22_5_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_0`, `OAI.Laughlin.Certificate.computeLDL_22_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_1`, `OAI_Laughlin_Certificate_computeLDL_22_6_10`, `OAI.Laughlin.Certificate.computeLDL_22_6_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_2`, `OAI.Laughlin.Certificate.computeLDL_22_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_3`, `OAI.Laughlin.Certificate.computeLDL_22_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_4`, `OAI.Laughlin.Certificate.computeLDL_22_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_5`, `OAI.Laughlin.Certificate.computeLDL_22_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_6`, `OAI.Laughlin.Certificate.computeLDL_22_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_7`, `OAI.Laughlin.Certificate.computeLDL_22_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_8`, `OAI.Laughlin.Certificate.computeLDL_22_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_9`, `OAI.Laughlin.Certificate.computeLDL_22_6_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_0`, `OAI.Laughlin.Certificate.computeLDL_22_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_1`, `OAI_Laughlin_Certificate_computeLDL_22_7_10`, `OAI.Laughlin.Certificate.computeLDL_22_7_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_2`, `OAI.Laughlin.Certificate.computeLDL_22_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_3`, `OAI.Laughlin.Certificate.computeLDL_22_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_4`, `OAI.Laughlin.Certificate.computeLDL_22_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_5`, `OAI.Laughlin.Certificate.computeLDL_22_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_6`, `OAI.Laughlin.Certificate.computeLDL_22_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_7`, `OAI.Laughlin.Certificate.computeLDL_22_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_8`, `OAI.Laughlin.Certificate.computeLDL_22_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_9`, `OAI.Laughlin.Certificate.computeLDL_22_7_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_0`, `OAI.Laughlin.Certificate.computeLDL_22_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_1`, `OAI_Laughlin_Certificate_computeLDL_22_8_10`, `OAI.Laughlin.Certificate.computeLDL_22_8_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_2`, `OAI.Laughlin.Certificate.computeLDL_22_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_3`, `OAI.Laughlin.Certificate.computeLDL_22_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_4`, `OAI.Laughlin.Certificate.computeLDL_22_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_5`, `OAI.Laughlin.Certificate.computeLDL_22_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_6`, `OAI.Laughlin.Certificate.computeLDL_22_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_7`, `OAI.Laughlin.Certificate.computeLDL_22_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_8`, `OAI.Laughlin.Certificate.computeLDL_22_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_9`, `OAI.Laughlin.Certificate.computeLDL_22_8_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_0`, `OAI.Laughlin.Certificate.computeLDL_22_9_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_1`, `OAI_Laughlin_Certificate_computeLDL_22_9_10`, `OAI.Laughlin.Certificate.computeLDL_22_9_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_9_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_2`, `OAI.Laughlin.Certificate.computeLDL_22_9_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_3`, `OAI.Laughlin.Certificate.computeLDL_22_9_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_4`, `OAI.Laughlin.Certificate.computeLDL_22_9_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_5`, `OAI.Laughlin.Certificate.computeLDL_22_9_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_6`, `OAI.Laughlin.Certificate.computeLDL_22_9_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_7`, `OAI.Laughlin.Certificate.computeLDL_22_9_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_8`, `OAI.Laughlin.Certificate.computeLDL_22_9_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_9`, `OAI.Laughlin.Certificate.computeLDL_22_9_9_s50`, `OAI_Laughlin_Certificate_computeLDL_23_0_10`, `OAI.Laughlin.Certificate.computeLDL_23_0_10_s50`, `OAI_Laughlin_Certificate_computeLDL_23_0_11`, `OAI.Laughlin.Certificate.computeLDL_23_0_11_s50`, `OAI_Laughlin_Certificate_computeLDL_23_10_0`, `OAI.Laughlin.Certificate.computeLDL_23_10_0_s50`, `OAI_Laughlin_Certificate_computeLDL_23_10_1`, `OAI_Laughlin_Certificate_computeLDL_23_10_10`, `OAI.Laughlin.Certificate.computeLDL_23_10_10_s50`, `OAI_Laughlin_Certificate_computeLDL_23_10_11`, `OAI.Laughlin.Certificate.computeLDL_23_10_11_s50`, `OAI.Laughlin.Certificate.computeLDL_23_10_1_s50`, `OAI_Laughlin_Certificate_computeLDL_23_10_2`, `OAI.Laughlin.Certificate.computeLDL_23_10_2_s50`, `OAI_Laughlin_Certificate_computeLDL_23_10_3`, `OAI.Laughlin.Certificate.computeLDL_23_10_3_s50`, `OAI_Laughlin_Certificate_computeLDL_23_10_4`, `OAI.Laughlin.Certificate.computeLDL_23_10_4_s50`, `OAI_Laughlin_Certificate_computeLDL_23_10_5`, `OAI.Laughlin.Certificate.computeLDL_23_10_5_s50`, `OAI_Laughlin_Certificate_computeLDL_23_10_6`, `OAI.Laughlin.Certificate.computeLDL_23_10_6_s50`, `OAI_Laughlin_Certificate_computeLDL_23_10_7`, `OAI.Laughlin.Certificate.computeLDL_23_10_7_s50`, `OAI_Laughlin_Certificate_computeLDL_23_10_8`, `OAI.Laughlin.Certificate.computeLDL_23_10_8_s50`, `OAI_Laughlin_Certificate_computeLDL_23_10_9`, `OAI.Laughlin.Certificate.computeLDL_23_10_9_s50`, `OAI_Laughlin_Certificate_computeLDL_23_11_0`, `OAI.Laughlin.Certificate.computeLDL_23_11_0_s50`, `OAI_Laughlin_Certificate_computeLDL_23_11_1`, `OAI_Laughlin_Certificate_computeLDL_23_11_10`, `OAI.Laughlin.Certificate.computeLDL_23_11_10_s50`, `OAI_Laughlin_Certificate_computeLDL_23_11_11`, `OAI.Laughlin.Certificate.computeLDL_23_11_11_s50`, `OAI.Laughlin.Certificate.computeLDL_23_11_1_s50`, `OAI_Laughlin_Certificate_computeLDL_23_11_2`, `OAI.Laughlin.Certificate.computeLDL_23_11_2_s50`, `OAI_Laughlin_Certificate_computeLDL_23_11_3`, `OAI.Laughlin.Certificate.computeLDL_23_11_3_s50`, `OAI_Laughlin_Certificate_computeLDL_23_11_4`, `OAI.Laughlin.Certificate.computeLDL_23_11_4_s50`, `OAI_Laughlin_Certificate_computeLDL_23_11_5`, `OAI.Laughlin.Certificate.computeLDL_23_11_5_s50`, `OAI_Laughlin_Certificate_computeLDL_23_11_6`, `OAI.Laughlin.Certificate.computeLDL_23_11_6_s50`, `OAI_Laughlin_Certificate_computeLDL_23_11_7`, `OAI.Laughlin.Certificate.computeLDL_23_11_7_s50`, `OAI_Laughlin_Certificate_computeLDL_23_11_8`, `OAI.Laughlin.Certificate.computeLDL_23_11_8_s50`, `OAI_Laughlin_Certificate_computeLDL_23_11_9`, `OAI.Laughlin.Certificate.computeLDL_23_11_9_s50`, `OAI_Laughlin_Certificate_computeLDL_23_1_10`, `OAI.Laughlin.Certificate.computeLDL_23_1_10_s50`, `OAI_Laughlin_Certificate_computeLDL_23_1_11`, `OAI.Laughlin.Certificate.computeLDL_23_1_11_s50`, `OAI_Laughlin_Certificate_computeLDL_23_2_10`, `OAI.Laughlin.Certificate.computeLDL_23_2_10_s50`, `OAI_Laughlin_Certificate_computeLDL_23_2_11`, `OAI.Laughlin.Certificate.computeLDL_23_2_11_s50`, `OAI_Laughlin_Certificate_computeLDL_23_2_3`, `OAI.Laughlin.Certificate.computeLDL_23_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_23_2_4`, `OAI.Laughlin.Certificate.computeLDL_23_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_23_2_5`, `OAI.Laughlin.Certificate.computeLDL_23_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_23_2_6`, `OAI.Laughlin.Certificate.computeLDL_23_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_23_2_7`, `OAI.Laughlin.Certificate.computeLDL_23_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_23_2_8`, `OAI.Laughlin.Certificate.computeLDL_23_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_23_2_9`, `OAI.Laughlin.Certificate.computeLDL_23_2_9_s50`, `OAI_Laughlin_Certificate_computeLDL_23_3_0`, `OAI.Laughlin.Certificate.computeLDL_23_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_23_3_1`, `OAI_Laughlin_Certificate_computeLDL_23_3_10`, `OAI.Laughlin.Certificate.computeLDL_23_3_10_s50`, `OAI_Laughlin_Certificate_computeLDL_23_3_11`, `OAI.Laughlin.Certificate.computeLDL_23_3_11_s50`, `OAI.Laughlin.Certificate.computeLDL_23_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_23_3_2`, `OAI.Laughlin.Certificate.computeLDL_23_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_23_3_3`, `OAI.Laughlin.Certificate.computeLDL_23_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_23_3_4`, `OAI.Laughlin.Certificate.computeLDL_23_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_23_3_5`, `OAI.Laughlin.Certificate.computeLDL_23_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_23_3_6`, `OAI.Laughlin.Certificate.computeLDL_23_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_23_3_7`, `OAI.Laughlin.Certificate.computeLDL_23_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_23_3_8`, `OAI.Laughlin.Certificate.computeLDL_23_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_23_3_9`, `OAI.Laughlin.Certificate.computeLDL_23_3_9_s50`, `OAI_Laughlin_Certificate_computeLDL_23_4_0`, `OAI.Laughlin.Certificate.computeLDL_23_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_23_4_1`, `OAI_Laughlin_Certificate_computeLDL_23_4_10`, `OAI.Laughlin.Certificate.computeLDL_23_4_10_s50`, `OAI_Laughlin_Certificate_computeLDL_23_4_11`, `OAI.Laughlin.Certificate.computeLDL_23_4_11_s50`, `OAI.Laughlin.Certificate.computeLDL_23_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_23_4_2`, `OAI.Laughlin.Certificate.computeLDL_23_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_23_4_3`, `OAI.Laughlin.Certificate.computeLDL_23_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_23_4_4`, `OAI.Laughlin.Certificate.computeLDL_23_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_23_4_5`, `OAI.Laughlin.Certificate.computeLDL_23_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_23_4_6`, `OAI.Laughlin.Certificate.computeLDL_23_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_23_4_7`, `OAI.Laughlin.Certificate.computeLDL_23_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_23_4_8`, `OAI.Laughlin.Certificate.computeLDL_23_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_23_4_9`, `OAI.Laughlin.Certificate.computeLDL_23_4_9_s50`, `OAI_Laughlin_Certificate_computeLDL_23_5_0`, `OAI.Laughlin.Certificate.computeLDL_23_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_23_5_1`, `OAI_Laughlin_Certificate_computeLDL_23_5_10`, `OAI.Laughlin.Certificate.computeLDL_23_5_10_s50`, `OAI_Laughlin_Certificate_computeLDL_23_5_11`, `OAI.Laughlin.Certificate.computeLDL_23_5_11_s50`, `OAI.Laughlin.Certificate.computeLDL_23_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_23_5_2`, `OAI.Laughlin.Certificate.computeLDL_23_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_23_5_3`, `OAI.Laughlin.Certificate.computeLDL_23_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_23_5_4`, `OAI.Laughlin.Certificate.computeLDL_23_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_23_5_5`, `OAI.Laughlin.Certificate.computeLDL_23_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_23_5_6`, `OAI.Laughlin.Certificate.computeLDL_23_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_23_5_7`, `OAI.Laughlin.Certificate.computeLDL_23_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_23_5_8`, `OAI.Laughlin.Certificate.computeLDL_23_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_23_5_9`, `OAI.Laughlin.Certificate.computeLDL_23_5_9_s50`, `OAI_Laughlin_Certificate_computeLDL_23_6_0`, `OAI.Laughlin.Certificate.computeLDL_23_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_23_6_1`, `OAI_Laughlin_Certificate_computeLDL_23_6_10`, `OAI.Laughlin.Certificate.computeLDL_23_6_10_s50`, `OAI_Laughlin_Certificate_computeLDL_23_6_11`, `OAI.Laughlin.Certificate.computeLDL_23_6_11_s50`, `OAI.Laughlin.Certificate.computeLDL_23_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_23_6_2`, `OAI.Laughlin.Certificate.computeLDL_23_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_23_6_3`, `OAI.Laughlin.Certificate.computeLDL_23_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_23_6_4`, `OAI.Laughlin.Certificate.computeLDL_23_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_23_6_5`, `OAI.Laughlin.Certificate.computeLDL_23_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_23_6_6`, `OAI.Laughlin.Certificate.computeLDL_23_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_23_6_7`, `OAI.Laughlin.Certificate.computeLDL_23_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_23_6_8`, `OAI.Laughlin.Certificate.computeLDL_23_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_23_6_9`, `OAI.Laughlin.Certificate.computeLDL_23_6_9_s50`, `OAI_Laughlin_Certificate_computeLDL_23_7_0`, `OAI.Laughlin.Certificate.computeLDL_23_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_23_7_1`, `OAI_Laughlin_Certificate_computeLDL_23_7_10`, `OAI.Laughlin.Certificate.computeLDL_23_7_10_s50`, `OAI_Laughlin_Certificate_computeLDL_23_7_11`, `OAI.Laughlin.Certificate.computeLDL_23_7_11_s50`, `OAI.Laughlin.Certificate.computeLDL_23_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_23_7_2`, `OAI.Laughlin.Certificate.computeLDL_23_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_23_7_3`, `OAI.Laughlin.Certificate.computeLDL_23_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_23_7_4`, `OAI.Laughlin.Certificate.computeLDL_23_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_23_7_5`, `OAI.Laughlin.Certificate.computeLDL_23_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_23_7_6`, `OAI.Laughlin.Certificate.computeLDL_23_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_23_7_7`, `OAI.Laughlin.Certificate.computeLDL_23_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_23_7_8`, `OAI.Laughlin.Certificate.computeLDL_23_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_23_7_9`, `OAI.Laughlin.Certificate.computeLDL_23_7_9_s50`, `OAI_Laughlin_Certificate_computeLDL_23_8_0`, `OAI.Laughlin.Certificate.computeLDL_23_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_23_8_1`, `OAI_Laughlin_Certificate_computeLDL_23_8_10`, `OAI.Laughlin.Certificate.computeLDL_23_8_10_s50`, `OAI_Laughlin_Certificate_computeLDL_23_8_11`, `OAI.Laughlin.Certificate.computeLDL_23_8_11_s50`, `OAI.Laughlin.Certificate.computeLDL_23_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_23_8_2`, `OAI.Laughlin.Certificate.computeLDL_23_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_23_8_3`, `OAI.Laughlin.Certificate.computeLDL_23_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_23_8_4`, `OAI.Laughlin.Certificate.computeLDL_23_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_23_8_5`, `OAI.Laughlin.Certificate.computeLDL_23_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_23_8_6`, `OAI.Laughlin.Certificate.computeLDL_23_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_23_8_7`, `OAI.Laughlin.Certificate.computeLDL_23_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_23_8_8`, `OAI.Laughlin.Certificate.computeLDL_23_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_23_8_9`, `OAI.Laughlin.Certificate.computeLDL_23_8_9_s50`, `OAI_Laughlin_Certificate_computeLDL_23_9_0`, `OAI.Laughlin.Certificate.computeLDL_23_9_0_s50`, `OAI_Laughlin_Certificate_computeLDL_23_9_1`, `OAI_Laughlin_Certificate_computeLDL_23_9_10`, `OAI.Laughlin.Certificate.computeLDL_23_9_10_s50`, `OAI_Laughlin_Certificate_computeLDL_23_9_11`, `OAI.Laughlin.Certificate.computeLDL_23_9_11_s50`, `OAI.Laughlin.Certificate.computeLDL_23_9_1_s50`, `OAI_Laughlin_Certificate_computeLDL_23_9_2`, `OAI.Laughlin.Certificate.computeLDL_23_9_2_s50`, `OAI_Laughlin_Certificate_computeLDL_23_9_3`, `OAI.Laughlin.Certificate.computeLDL_23_9_3_s50`, `OAI_Laughlin_Certificate_computeLDL_23_9_4`, `OAI.Laughlin.Certificate.computeLDL_23_9_4_s50`, `OAI_Laughlin_Certificate_computeLDL_23_9_5`, `OAI.Laughlin.Certificate.computeLDL_23_9_5_s50`, `OAI_Laughlin_Certificate_computeLDL_23_9_6`, `OAI.Laughlin.Certificate.computeLDL_23_9_6_s50`, `OAI_Laughlin_Certificate_computeLDL_23_9_7`, `OAI.Laughlin.Certificate.computeLDL_23_9_7_s50`, `OAI_Laughlin_Certificate_computeLDL_23_9_8`, `OAI.Laughlin.Certificate.computeLDL_23_9_8_s50`, `OAI_Laughlin_Certificate_computeLDL_23_9_9`, `OAI.Laughlin.Certificate.computeLDL_23_9_9_s50`, `OAI_Laughlin_Certificate_error_9`, `OAI.Laughlin.Certificate.error_9_s50`, `OAI_Laughlin_Certificate_four_body_10_positive`, `OAI.Laughlin.Certificate.four_body_10_positive_s50`, `OAI_Laughlin_Certificate_four_body_11_positive`, `OAI.Laughlin.Certificate.four_body_11_positive_s50`, `OAI_Laughlin_Certificate_four_body_12_positive`, `OAI.Laughlin.Certificate.four_body_12_positive_s50`, `OAI_Laughlin_Certificate_four_body_9_positive`, `OAI.Laughlin.Certificate.four_body_9_positive_s50`, `OAI_Laughlin_Certificate_four_body_five_positive`, `OAI.Laughlin.Certificate.four_body_five_positive_s50`, `OAI_Laughlin_Certificate_gram_14`, `OAI.Laughlin.Certificate.gram_14_s50`, `OAI_Laughlin_Certificate_gram_15`, `OAI.Laughlin.Certificate.gram_15_s50`, `OAI_Laughlin_Certificate_gram_16`, `OAI.Laughlin.Certificate.gram_16_s50`, `OAI_Laughlin_Certificate_gram_17`, `OAI.Laughlin.Certificate.gram_17_s50`, `OAI_Laughlin_Certificate_gram_18`, `OAI.Laughlin.Certificate.gram_18_s50`, `OAI_Laughlin_Certificate_gram_19`, `OAI.Laughlin.Certificate.gram_19_s50`, `OAI_Laughlin_Certificate_gram_20`, `OAI.Laughlin.Certificate.gram_20_s50`, `OAI_Laughlin_Certificate_gram_21`, `OAI.Laughlin.Certificate.gram_21_s50`, `OAI_Laughlin_Certificate_gram_22`, `OAI.Laughlin.Certificate.gram_22_s50`, `OAI_Laughlin_Certificate_gram_23`, `OAI.Laughlin.Certificate.gram_23_s50`, `OAI_Laughlin_Certificate_gram_9`, `OAI.Laughlin.Certificate.gram_9_s50`, `OAI_Laughlin_Certificate_ldl_12`, `OAI.Laughlin.Certificate.ldl_12_s50`, `OAI_Laughlin_Certificate_ldl_14`, `OAI.Laughlin.Certificate.ldl_14_s50`, `OAI_Laughlin_Certificate_ldl_15`, `OAI.Laughlin.Certificate.ldl_15_s50`, `OAI_Laughlin_Certificate_ldl_16`, `OAI.Laughlin.Certificate.ldl_16_s50`, `OAI_Laughlin_Certificate_ldl_17`, `OAI.Laughlin.Certificate.ldl_17_s50`, `OAI_Laughlin_Certificate_ldl_18`, `OAI.Laughlin.Certificate.ldl_18_s50`, `OAI_Laughlin_Certificate_ldl_19`, `OAI.Laughlin.Certificate.ldl_19_s50`, `OAI_Laughlin_Certificate_ldl_20`, `OAI.Laughlin.Certificate.ldl_20_s50`, `OAI_Laughlin_Certificate_ldl_21`, `OAI.Laughlin.Certificate.ldl_21_s50`, `OAI_Laughlin_Certificate_ldl_22`, `OAI.Laughlin.Certificate.ldl_22_s50`, `OAI_Laughlin_Certificate_ldl_23`, `OAI.Laughlin.Certificate.ldl_23_s50`, `OAI_Laughlin_Certificate_ldl_five`, `OAI.Laughlin.Certificate.ldl_five_s50`, `OAI_Laughlin_Fock_complexThreeSpinProjector_eigen`, `OAI_Laughlin_Fock_fourCopyForm_scaled_haar`, `OAI_Laughlin_Fock_physical_fock_square_eventually_sharp`, `OAI_Laughlin_Fock_source_fourBody_physical_L`, `OAI_Laughlin_Spin_source_fourBody_factorial_coefficient`, `OAI.Laughlin.Spin.source_fourBody_factorial_coefficient_s50` and `OAI_Laughlin_Spin_source_threeBody_physical_traces_strict_eventually`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Data09
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
def candidateY_9 : Matrix (Fin 5) (Fin 5) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => -12465910883340844333323483/6710886400000000000000
  | 0, 1 => -33961811903853786055197/838860800000000000000
  | 0, 2 => -670994343426034247927913/6710886400000000000000
  | 0, 3 => 4530779263986412498504797/3355443200000000000000
  | 0, 4 => 2064320406503781558919011/838860800000000000000
  | 1, 0 => -33961811903853786055197/838860800000000000000
  | 1, 1 => 2960534512700301116069433/23488102400000000000000
  | 1, 2 => -249132079557021880785303/11744051200000000000000
  | 1, 3 => -172612848420190308157317/419430400000000000000
  | 1, 4 => -460639144770506834240727/209715200000000000000
  | 2, 0 => -670994343426034247927913/6710886400000000000000
  | 2, 1 => -249132079557021880785303/11744051200000000000000
  | 2, 2 => -12391755266391716879263611/46976204800000000000000
  | 2, 3 => 202846259663372040293217/3355443200000000000000
  | 2, 4 => 1717697222431419971099331/838860800000000000000
  | 3, 0 => 4530779263986412498504797/3355443200000000000000
  | 3, 1 => -172612848420190308157317/419430400000000000000
  | 3, 2 => 202846259663372040293217/3355443200000000000000
  | 3, 3 => -3138981013037239731556773/1677721600000000000000
  | 3, 4 => -1034085603218724160418079/419430400000000000000
  | 4, 0 => 2064320406503781558919011/838860800000000000000
  | 4, 1 => -460639144770506834240727/209715200000000000000
  | 4, 2 => 1717697222431419971099331/838860800000000000000
  | 4, 3 => -1034085603218724160418079/419430400000000000000
  | 4, 4 => -9956547203160990435022917/104857600000000000000
  | _, _ => 0
def candidateZ_9 : Matrix (Fin 5) (Fin 5) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 80640
  | 0, 3 => -10080
  | 0, 4 => 136080
  | 1, 1 => 4320
  | 1, 2 => -2160
  | 1, 4 => 22680
  | 2, 1 => -2160
  | 2, 2 => 1080
  | 2, 4 => -11340
  | 3, 0 => -10080
  | 3, 3 => 1260
  | 3, 4 => -17010
  | 4, 0 => 136080
  | 4, 1 => 22680
  | 4, 2 => -11340
  | 4, 3 => -17010
  | 4, 4 => 348705
  | _, _ => 0
def lower_9 : Matrix (Fin 5) (Fin 5) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 23599862696142345457458519/3087682465193682626040960764
  | 1, 1 => 1
  | 2, 0 => -23599862696142345457458519/6175364930387365252081921528
  | 2, 1 => -1/2
  | 2, 2 => 1
  | 3, 0 => -1/8
  | 3, 3 => 1
  | 4, 0 => 2667181719584543372547889257/1543841232596841313020480382
  | 4, 1 => 21/4
  | 4, 4 => 1
  | _, _ => 0

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Data10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
def lower_10 : Matrix (Fin 5) (Fin 5) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 1 => 1
  | 2, 2 => 1
  | 3, 1 => -3/4
  | 3, 3 => 1
  | 4, 1 => 3
  | 4, 4 => 1
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
def lower_11 : Matrix (Fin 6) (Fin 6) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 1925158773729525751974454/150990079174740777675305331
  | 1, 1 => 1
  | 2, 0 => -3936218478175539835501733/1207920633397926221402442648
  | 2, 1 => 97293768145330047583879356561582525137135743957/398751775291942480923180911595463390779768165464
  | 2, 2 => 1
  | 3, 0 => 8301941609933521328767591/6039603166989631107012213240
  | 3, 1 => -1179496096132238434241131635425406914434660414529/1993758876459712404615904557977316953898840827320
  | 3, 2 => -7/5
  | 3, 3 => 1
  | 4, 0 => -34900457663141259371752627/503300263915802592251017770
  | 4, 1 => 2043169131051930999261466487793233027879850623097/3987517752919424809231809115954633907797681654640
  | 4, 2 => 21/10
  | 4, 4 => 1
  | 5, 0 => 75821519573118101206927129/50330026391580259225101777
  | 5, 1 => 165/16
  | 5, 5 => 1
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
def lower_12 : Matrix (Fin 6) (Fin 6) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 1 => 1
  | 2, 1 => 204004003367800299891773/539865092478537355668714
  | 2, 2 => 1
  | 3, 1 => -204004003367800299891773/719820123304716474224952
  | 3, 2 => -3/4
  | 3, 3 => 1
  | 4, 1 => -1/2
  | 4, 4 => 1
  | 5, 1 => 449550461547858066194128/89977515413089559278119
  | 5, 2 => 33/8
  | 5, 5 => 1
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
def candidateZ_14 : Matrix (Fin 7) (Fin 7) ℚ := fun i j =>
  match i.val, j.val with
  | 1, 1 => 239500800
  | 1, 5 => -74844000
  | 1, 6 => 778377600
  | 2, 2 => 43545600
  | 2, 4 => -21772800
  | 2, 6 => 389188800
  | 3, 3 => 11113200
  | 3, 4 => -19051200
  | 3, 5 => 26195400
  | 4, 2 => -21772800
  | 4, 3 => -19051200
  | 4, 4 => 43545600
  | 4, 5 => -44906400
  | 4, 6 => -194594400
  | 5, 1 => -74844000
  | 5, 3 => 26195400
  | 5, 4 => -44906400
  | 5, 5 => 85135050
  | 5, 6 => -243243000
  | 6, 1 => 778377600
  | 6, 2 => 389188800
  | 6, 4 => -194594400
  | 6, 5 => -243243000
  | 6, 6 => 6008102100
  | _, _ => 0

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Data15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
def candidateZ_15 : Matrix (Fin 8) (Fin 8) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 174356582400
  | 0, 6 => -2724321600
  | 0, 7 => 122594472000
  | 1, 1 => 2874009600
  | 1, 5 => -179625600
  | 1, 7 => 40864824000
  | 2, 2 => 435456000
  | 2, 4 => -40824000
  | 2, 5 => -299376000
  | 2, 6 => 1459458000
  | 2, 7 => 10216206000
  | 3, 3 => 177811200
  | 3, 4 => -171460800
  | 3, 6 => 681080400
  | 4, 2 => -40824000
  | 4, 3 => -171460800
  | 4, 4 => 175543200
  | 4, 6 => -656756100
  | 4, 7 => -2554051500
  | 5, 1 => -179625600
  | 5, 2 => -299376000
  | 5, 5 => 340540200
  | 5, 6 => -1605403800
  | 5, 7 => -2554051500
  | 6, 0 => -2724321600
  | 6, 2 => 1459458000
  | 6, 3 => 681080400
  | 6, 4 => -656756100
  | 6, 5 => -1605403800
  | 6, 6 => 10477692225
  | 6, 7 => -1915538625
  | 7, 0 => 122594472000
  | 7, 1 => 40864824000
  | 7, 2 => 10216206000
  | 7, 4 => -2554051500
  | 7, 5 => -2554051500
  | 7, 6 => -1915538625
  | 7, 7 => 1306397342250
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
def candidateZ_16 : Matrix (Fin 8) (Fin 8) ℚ := fun i j =>
  match i.val, j.val with
  | 1, 1 => 37362124800
  | 1, 6 => -7005398400
  | 1, 7 => 102162060000
  | 2, 2 => 4790016000
  | 2, 5 => -1496880000
  | 2, 7 => 61297236000
  | 3, 3 => 1828915200
  | 3, 4 => -685843200
  | 3, 5 => -1571724000
  | 3, 6 => 4086482400
  | 3, 7 => 15324309000
  | 4, 3 => -685843200
  | 4, 4 => 457228800
  | 4, 7 => -10216206000
  | 5, 2 => -1496880000
  | 5, 3 => -1571724000
  | 5, 5 => 3555090000
  | 5, 6 => -8027019000
  | 5, 7 => -19155386250
  | 6, 1 => -7005398400
  | 6, 3 => 4086482400
  | 6, 5 => -8027019000
  | 6, 6 => 22183761600
  | 6, 7 => -19155386250
  | 7, 1 => 102162060000
  | 7, 2 => 61297236000
  | 7, 3 => 15324309000
  | 7, 4 => -10216206000
  | 7, 5 => -19155386250
  | 7, 6 => -19155386250
  | 7, 7 => 2584061605125/2
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
def candidateZ_17 : Matrix (Fin 9) (Fin 9) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 41845579776000
  | 0, 7 => -326918592000
  | 0, 8 => 19451656224000
  | 1, 1 => 523069747200
  | 1, 6 => -16345929600
  | 1, 8 => 6947020080000
  | 2, 2 => 57480192000
  | 2, 5 => -2694384000
  | 2, 6 => -29189160000
  | 2, 7 => 204324120000
  | 2, 8 => 2084106024000
  | 3, 3 => 18289152000
  | 3, 4 => -1143072000
  | 3, 5 => -12573792000
  | 3, 7 => 143026884000
  | 3, 8 => 347351004000
  | 4, 3 => -1143072000
  | 4, 4 => 5372438400
  | 4, 5 => -9430344000
  | 4, 6 => 12259447200
  | 4, 8 => -173675502000
  | 5, 2 => -2694384000
  | 5, 3 => -12573792000
  | 5, 4 => -9430344000
  | 5, 5 => 28740096000
  | 5, 6 => -24081057000
  | 5, 7 => -112378266000
  | 5, 8 => -260513253000
  | 6, 1 => -16345929600
  | 6, 2 => -29189160000
  | 6, 4 => 12259447200
  | 6, 5 => -24081057000
  | 6, 6 => 55532376900
  | 6, 7 => -166013347500
  | 6, 8 => -217094377500
  | 7, 0 => -326918592000
  | 7, 2 => 204324120000
  | 7, 3 => 143026884000
  | 7, 5 => -112378266000
  | 7, 6 => -166013347500
  | 7, 7 => 2442950259750
  | 7, 8 => -151966064250
  | 8, 0 => 19451656224000
  | 8, 1 => 6947020080000
  | 8, 2 => 2084106024000
  | 8, 3 => 347351004000
  | 8, 4 => -173675502000
  | 8, 5 => -260513253000
  | 8, 6 => -217094377500
  | 8, 7 => -151966064250
  | 8, 8 => 355589735626125
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
def candidateZ_18 : Matrix (Fin 9) (Fin 9) ℚ := fun i j =>
  match i.val, j.val with
  | 1, 1 => 7846046208000
  | 1, 7 => -858161304000
  | 1, 8 => 16672848192000
  | 2, 2 => 747242496000
  | 2, 6 => -140107968000
  | 2, 8 => 11115232128000
  | 3, 3 => 201180672000
  | 3, 5 => -47151720000
  | 3, 6 => -163459296000
  | 3, 7 => 643620978000
  | 3, 8 => 4168212048000
  | 4, 4 => 98761420800
  | 4, 5 => -113164128000
  | 4, 7 => 367783416000
  | 5, 3 => -47151720000
  | 5, 4 => -113164128000
  | 5, 5 => 149313780000
  | 5, 7 => -421418497500
  | 5, 8 => -1736755020000
  | 6, 2 => -140107968000
  | 6, 3 => -163459296000
  | 6, 6 => 329837508000
  | 6, 7 => -1195296102000
  | 6, 8 => -2084106024000
  | 7, 1 => -858161304000
  | 7, 3 => 643620978000
  | 7, 4 => 367783416000
  | 7, 5 => -421418497500
  | 7, 6 => -1195296102000
  | 7, 7 => 6169949911125
  | 7, 8 => -1823592771000
  | 8, 1 => 16672848192000
  | 8, 2 => 11115232128000
  | 8, 3 => 4168212048000
  | 8, 5 => -1736755020000
  | 8, 6 => -2084106024000
  | 8, 7 => -1823592771000
  | 8, 8 => 354298024080000
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
def candidateZ_19 : Matrix (Fin 10) (Fin 10) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 12804747411456000
  | 0, 8 => -50018544576000
  | 0, 9 => 3801409387776000
  | 1, 1 => 125536739328000
  | 1, 7 => -1961511552000
  | 1, 9 => 1425528520416000
  | 2, 2 => 10461394944000
  | 2, 6 => -245188944000
  | 2, 7 => -3677834160000
  | 2, 8 => 34735100400000
  | 2, 9 => 475176173472000
  | 3, 3 => 2414168064000
  | 3, 5 => -75442752000
  | 3, 6 => -1225944720000
  | 3, 8 => 29177484336000
  | 3, 9 => 118794043368000
  | 4, 4 => 1265380704000
  | 4, 5 => -678984768000
  | 4, 6 => -1103350248000
  | 4, 7 => 2574483912000
  | 4, 8 => 9378477108000
  | 5, 3 => -75442752000
  | 5, 4 => -678984768000
  | 5, 5 => 572107536000
  | 5, 8 => -7641722088000
  | 5, 9 => -29698510842000
  | 6, 2 => -245188944000
  | 6, 3 => -1225944720000
  | 6, 4 => -1103350248000
  | 6, 6 => 3544293753000
  | 6, 7 => -6574128561000
  | 6, 8 => -16933361445000
  | 6, 9 => -29698510842000
  | 7, 1 => -1961511552000
  | 7, 2 => -3677834160000
  | 7, 4 => 2574483912000
  | 7, 6 => -6574128561000
  | 7, 7 => 17439063642000
  | 7, 8 => -19538493975000
  | 7, 9 => -22273883131500
  | 8, 0 => -50018544576000
  | 8, 2 => 34735100400000
  | 8, 3 => 29177484336000
  | 8, 4 => 9378477108000
  | 8, 5 => -7641722088000
  | 8, 6 => -16933361445000
  | 8, 7 => -19538493975000
  | 8, 8 => 693290894546250
  | 8, 9 => -14849255421000
  | 9, 0 => 3801409387776000
  | 9, 1 => 1425528520416000
  | 9, 2 => 475176173472000
  | 9, 3 => 118794043368000
  | 9, 5 => -29698510842000
  | 9, 6 => -29698510842000
  | 9, 7 => -22273883131500
  | 9, 8 => -14849255421000
  | 9, 9 => 121635819624193875
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
def candidateZ_20 : Matrix (Fin 10) (Fin 10) ℚ := fun i j =>
  match i.val, j.val with
  | 1, 1 => 2134124568576000
  | 1, 8 => -133382785536000
  | 1, 9 => 3326233214304000
  | 2, 2 => 156920924160000
  | 2, 7 => -17163226080000
  | 2, 9 => 2375880867360000
  | 3, 3 => 31384184832000
  | 3, 6 => -4413400992000
  | 3, 7 => -21454032600000
  | 3, 8 => 116709937344000
  | 3, 9 => 1069146390312000
  | 4, 4 => 14485008384000
  | 4, 5 => -2263282560000
  | 4, 6 => -11769069312000
  | 4, 8 => 100037089152000
  | 4, 9 => 237588086736000
  | 5, 4 => -2263282560000
  | 5, 5 => 5148967824000
  | 5, 6 => -8091235152000
  | 5, 7 => 10114043940000
  | 5, 9 => -148492554210000
  | 6, 3 => -4413400992000
  | 6, 4 => -11769069312000
  | 6, 5 => -8091235152000
  | 6, 6 => 31384184832000
  | 6, 7 => -21913761870000
  | 6, 8 => -108373513248000
  | 6, 9 => -267286597578000
  | 7, 2 => -17163226080000
  | 7, 3 => -21454032600000
  | 7, 5 => 10114043940000
  | 7, 6 => -21913761870000
  | 7, 7 => 62791356127500
  | 7, 8 => -182359277100000
  | 7, 9 => -259861969867500
  | 8, 1 => -133382785536000
  | 8, 3 => 116709937344000
  | 8, 4 => 100037089152000
  | 8, 6 => -108373513248000
  | 8, 7 => -182359277100000
  | 8, 8 => 1921545754128000
  | 8, 9 => -207889575894000
  | 9, 1 => 3326233214304000
  | 9, 2 => 2375880867360000
  | 9, 3 => 1069146390312000
  | 9, 4 => 237588086736000
  | 9, 5 => -148492554210000
  | 9, 6 => -267286597578000
  | 9, 7 => -259861969867500
  | 9, 8 => -207889575894000
  | 9, 9 => 121494751697694375
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
def candidateZ_21 : Matrix (Fin 11) (Fin 11) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 4865804016353280000
  | 0, 9 => -9503523469440000
  | 0, 10 => 898082967862080000
  | 1, 1 => 38414242234368000
  | 1, 8 => -300111267456000
  | 1, 10 => 349254487501920000
  | 2, 2 => 2510734786560000
  | 2, 7 => -29422673280000
  | 2, 8 => -583549686720000
  | 2, 9 => 7127642602080000
  | 2, 10 => 124733745536400000
  | 3, 3 => 439378587648000
  | 3, 6 => -6865290432000
  | 3, 7 => -154469034720000
  | 3, 9 => 6652466428608000
  | 3, 10 => 37420123660920000
  | 4, 4 => 173820100608000
  | 4, 5 => -3394923840000
  | 4, 6 => -66201014880000
  | 4, 7 => -154469034720000
  | 4, 8 => 525194718048000
  | 4, 9 => 3207439170936000
  | 4, 10 => 6236687276820000
  | 5, 4 => -3394923840000
  | 5, 5 => 95057867520000
  | 5, 6 => -121368527280000
  | 5, 8 => 343877493960000
  | 5, 10 => -3118343638410000
  | 6, 3 => -6865290432000
  | 6, 4 => -66201014880000
  | 6, 5 => -121368527280000
  | 6, 6 => 198480450168000
  | 6, 8 => -447040742148000
  | 6, 9 => -1930403204730000
  | 6, 10 => -4677515457615000
  | 7, 2 => -29422673280000
  | 7, 3 => -154469034720000
  | 7, 4 => -154469034720000
  | 7, 7 => 481336545690000
  | 7, 8 => -1422402361380000
  | 7, 9 => -2672865975780000
  | 7, 10 => -3897929548012500
  | 8, 1 => -300111267456000
  | 8, 2 => -583549686720000
  | 8, 4 => 525194718048000
  | 8, 5 => 343877493960000
  | 8, 6 => -447040742148000
  | 8, 7 => -1422402361380000
  | 8, 8 => 6322135623804000
  | 8, 9 => -2650592092648500
  | 8, 10 => -2728550683608750
  | 9, 0 => -9503523469440000
  | 9, 2 => 7127642602080000
  | 9, 3 => 6652466428608000
  | 9, 4 => 3207439170936000
  | 9, 6 => -1930403204730000
  | 9, 7 => -2672865975780000
  | 9, 8 => -2650592092648500
  | 9, 9 => 241033113993672000
  | 9, 10 => -1754068296605625
  | 10, 0 => 898082967862080000
  | 10, 1 => 349254487501920000
  | 10, 2 => 124733745536400000
  | 10, 3 => 37420123660920000
  | 10, 4 => 6236687276820000
  | 10, 5 => -3118343638410000
  | 10, 6 => -4677515457615000
  | 10, 7 => -3897929548012500
  | 10, 8 => -2728550683608750
  | 10, 9 => -1754068296605625
  | 10, 10 => 102179740482167473125/2
  | _, _ => 0

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Data22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
def candidateZ_22 : Matrix (Fin 11) (Fin 11) ℚ := fun i j =>
  match i.val, j.val with
  | 1, 1 => 729870602452992000
  | 1, 9 => -25659513367488000
  | 1, 10 => 798295971432960000
  | 2, 2 => 42682491371520000
  | 2, 8 => -2667655710720000
  | 2, 10 => 598721978574720000
  | 3, 3 => 6590678814720000
  | 3, 7 => -540641621520000
  | 3, 8 => -3501298120320000
  | 3, 9 => 24946749107280000
  | 3, 10 => 299360989287360000
  | 4, 4 => 2259661307904000
  | 4, 6 => -211843247616000
  | 4, 7 => -1544690347200000
  | 4, 9 => 25659513367488000
  | 4, 10 => 99786996429120000
  | 5, 5 => 1437750246240000
  | 5, 6 => -970948218240000
  | 5, 7 => -1274369536440000
  | 5, 8 => 2751019951680000
  | 5, 9 => 9800508577860000
  | 6, 4 => -211843247616000
  | 6, 5 => -970948218240000
  | 6, 6 => 997428624192000
  | 6, 9 => -9265935382704000
  | 6, 10 => -37420123660920000
  | 7, 3 => -540641621520000
  | 7, 4 => -1544690347200000
  | 7, 5 => -1274369536440000
  | 7, 7 => 5440206316545000
  | 7, 8 => -8534414168280000
  | 7, 9 => -23387577288075000
  | 7, 10 => -43656810937740000
  | 8, 2 => -2667655710720000
  | 8, 3 => -3501298120320000
  | 8, 5 => 2751019951680000
  | 8, 7 => -8534414168280000
  | 8, 8 => 22841802023040000
  | 8, 9 => -30292481058840000
  | 8, 10 => -37420123660920000
  | 9, 1 => -25659513367488000
  | 9, 3 => 24946749107280000
  | 9, 4 => 25659513367488000
  | 9, 5 => 9800508577860000
  | 9, 6 => -9265935382704000
  | 9, 7 => -23387577288075000
  | 9, 8 => -30292481058840000
  | 9, 9 => 698765124659852250
  | 9, 10 => -28065092745690000
  | 10, 1 => 798295971432960000
  | 10, 2 => 598721978574720000
  | 10, 3 => 299360989287360000
  | 10, 4 => 99786996429120000
  | 10, 6 => -37420123660920000
  | 10, 7 => -43656810937740000
  | 10, 8 => -37420123660920000
  | 10, 9 => -28065092745690000
  | 10, 10 => 51071452523969377500
  | _, _ => 0

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Data23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
def candidateZ_23 : Matrix (Fin 12) (Fin 12) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 2248001455555215360000
  | 0, 10 => -2195313921440640000
  | 0, 11 => 252461100965673600000
  | 1, 1 => 14597412049059840000
  | 1, 9 => -57021140816640000
  | 1, 11 => 100984440386269440000
  | 2, 2 => 768284844687360000
  | 2, 8 => -4501669011840000
  | 2, 9 => -114042281633280000
  | 2, 10 => 1746272437509600000
  | 2, 11 => 37869165144851040000
  | 3, 3 => 105450861035520000
  | 3, 7 => -823834851840000
  | 3, 8 => -24509086842240000
  | 3, 10 => 1746272437509600000
  | 3, 11 => 12623055048283680000
  | 4, 4 => 31635258310656000
  | 4, 6 => -308938069440000
  | 4, 7 => -8341327874880000
  | 4, 8 => -26259735902400000
  | 4, 9 => 119744395714944000
  | 4, 10 => 1010343338844840000
  | 4, 11 => 3155763762070920000
  | 5, 5 => 18896146093440000
  | 5, 6 => -4854741091200000
  | 5, 7 => -16991593819200000
  | 5, 9 => 117606102934320000
  | 5, 10 => 274414240180080000
  | 6, 4 => -308938069440000
  | 6, 5 => -4854741091200000
  | 6, 6 => 8396495387280000
  | 6, 7 => -11044535982480000
  | 6, 8 => 13411222264440000
  | 6, 10 => -202692336496650000
  | 6, 11 => -788940940517730000
  | 7, 3 => -823834851840000
  | 7, 4 => -8341327874880000
  | 7, 5 => -16991593819200000
  | 7, 6 => -11044535982480000
  | 7, 7 => 52725430517760000
  | 7, 8 => -31292851950360000
  | 7, 9 => -162153869197320000
  | 7, 10 => -420976391185350000
  | 7, 11 => -788940940517730000
  | 8, 2 => -4501669011840000
  | 8, 3 => -24509086842240000
  | 8, 4 => -26259735902400000
  | 8, 6 => 13411222264440000
  | 8, 7 => -31292851950360000
  | 8, 8 => 111009907368360000
  | 8, 9 => -302924810588400000
  | 8, 10 => -463853616213487500
  | 8, 11 => -591705705388297500
  | 9, 1 => -57021140816640000
  | 9, 2 => -114042281633280000
  | 9, 4 => 119744395714944000
  | 9, 5 => 117606102934320000
  | 9, 7 => -162153869197320000
  | 9, 8 => -302924810588400000
  | 9, 9 => 2530981340232345000
  | 9, 10 => -414739703908530000
  | 9, 11 => -394470470258865000
  | 10, 0 => -2195313921440640000
  | 10, 2 => 1746272437509600000
  | 10, 3 => 1746272437509600000
  | 10, 4 => 1010343338844840000
  | 10, 5 => 274414240180080000
  | 10, 6 => -202692336496650000
  | 10, 7 => -420976391185350000
  | 10, 8 => -463853616213487500
  | 10, 9 => -414739703908530000
  | 10, 10 => 101850365435360416875
  | 10, 11 => -246544043911790625
  | 11, 0 => 252461100965673600000
  | 11, 1 => 100984440386269440000
  | 11, 2 => 37869165144851040000
  | 11, 3 => 12623055048283680000
  | 11, 4 => 3155763762070920000
  | 11, 6 => -788940940517730000
  | 11, 7 => -788940940517730000
  | 11, 8 => -591705705388297500
  | 11, 9 => -394470470258865000
  | 11, 10 => -246544043911790625
  | 11, 11 => 25851868812458629565625
  | _, _ => 0

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_Certificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

def limitBound (z : ℕ) : ℚ := (3/2 : ℚ) * (3 * (z : ℚ) - 1) * (-1/2 : ℚ)^z


end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Positive05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

def lowerFive : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 0, 0; -1/2, 1, 0; 5/4, 0, 1]

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Polynomial_SourceIntegerPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped BigOperators
open Polynomial

noncomputable def integerCouplingPolynomial (z n : ℕ) : Polynomial ℤ := (Polynomial.X-1)^z * (Polynomial.X+1)^n

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_TripleLadderIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

abbrev Orbital (Q : ℕ) := Fin (Q+1)

end Laughlin.Spin

end OAI
end


