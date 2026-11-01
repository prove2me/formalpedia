-- Prove2me | Definitions.Def_OAIQ050L001
-- name    : OAIQ050L001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T09:06:31.659086+00:00
-- url     : https://prove2.me/theorems/e1e223f3-8e30-4afe-b9c7-d9bb310634e0
-- title:
--   Definitions bundle OAIQ050L001 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 8 definitions. The definitions and types are `OAI.Laughlin.Certificate.arithmeticScale`, `OAI.Laughlin.Certificate.candidateY_10`, `OAI.Laughlin.Certificate.candidateY_11`, `OAI.Laughlin.Certificate.candidateY_12`, `OAI.Laughlin.Certificate.candidateY_13`, `OAI.Laughlin.Certificate.candidateY_15`, `OAI.Laughlin.Certificate.candidateY_22`, `OAI.Laughlin.Certificate.rows`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Laughlin_FiniteFlux_Data10`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FiniteFlux/Data10.lean), [`Laughlin_FiniteFlux_Data11`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FiniteFlux/Data11.lean), [`Laughlin_FiniteFlux_Data12`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FiniteFlux/Data12.lean), [`Laughlin_FiniteFlux_Data13`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FiniteFlux/Data13.lean), [`Laughlin_FiniteFlux_Data15`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FiniteFlux/Data15.lean), [`Laughlin_FiniteFlux_Data22`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FiniteFlux/Data22.lean), [`Laughlin_FourBody_Integral`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/Integral.lean), [`Laughlin_Operators_Certificate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Operators/Certificate.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ050L010`, `OAIQ050L012` and `OAIQ050L014`; the statements `OAI_Laughlin_Certificate_candidateLDL_10`, `OAI.Laughlin.Certificate.candidateLDL_10_s50`, `OAI_Laughlin_Certificate_candidateLDL_11`, `OAI.Laughlin.Certificate.candidateLDL_11_s50`, `OAI_Laughlin_Certificate_candidateLDL_12`, `OAI.Laughlin.Certificate.candidateLDL_12_s50`, `OAI_Laughlin_Certificate_candidateLDL_13`, `OAI.Laughlin.Certificate.candidateLDL_13_s50`, `OAI_Laughlin_Certificate_candidateLDL_15`, `OAI.Laughlin.Certificate.candidateLDL_15_s50`, `OAI_Laughlin_Certificate_candidateLDL_22`, `OAI.Laughlin.Certificate.candidateLDL_22_s50`, `OAI_Laughlin_Certificate_computeLDL_11_5_5`, `OAI.Laughlin.Certificate.computeLDL_11_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_1_5`, `OAI.Laughlin.Certificate.computeLDL_12_1_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_0`, `OAI.Laughlin.Certificate.computeLDL_12_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_1`, `OAI.Laughlin.Certificate.computeLDL_12_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_2`, `OAI.Laughlin.Certificate.computeLDL_12_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_3`, `OAI.Laughlin.Certificate.computeLDL_12_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_4`, `OAI.Laughlin.Certificate.computeLDL_12_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_5`, `OAI.Laughlin.Certificate.computeLDL_12_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_0`, `OAI.Laughlin.Certificate.computeLDL_12_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_1`, `OAI.Laughlin.Certificate.computeLDL_12_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_2`, `OAI.Laughlin.Certificate.computeLDL_12_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_3`, `OAI.Laughlin.Certificate.computeLDL_12_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_4`, `OAI.Laughlin.Certificate.computeLDL_12_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_5`, `OAI.Laughlin.Certificate.computeLDL_12_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_0`, `OAI.Laughlin.Certificate.computeLDL_12_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_1`, `OAI.Laughlin.Certificate.computeLDL_12_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_2`, `OAI.Laughlin.Certificate.computeLDL_12_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_3`, `OAI.Laughlin.Certificate.computeLDL_12_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_4`, `OAI.Laughlin.Certificate.computeLDL_12_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_5`, `OAI.Laughlin.Certificate.computeLDL_12_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_0`, `OAI.Laughlin.Certificate.computeLDL_12_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_1`, `OAI.Laughlin.Certificate.computeLDL_12_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_2`, `OAI.Laughlin.Certificate.computeLDL_12_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_3`, `OAI.Laughlin.Certificate.computeLDL_12_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_4`, `OAI.Laughlin.Certificate.computeLDL_12_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_5`, `OAI.Laughlin.Certificate.computeLDL_12_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_13_1_6`, `OAI.Laughlin.Certificate.computeLDL_13_1_6_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_0`, `OAI.Laughlin.Certificate.computeLDL_13_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_1`, `OAI.Laughlin.Certificate.computeLDL_13_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_2`, `OAI.Laughlin.Certificate.computeLDL_13_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_3`, `OAI.Laughlin.Certificate.computeLDL_13_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_4`, `OAI.Laughlin.Certificate.computeLDL_13_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_5`, `OAI.Laughlin.Certificate.computeLDL_13_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_6`, `OAI.Laughlin.Certificate.computeLDL_13_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_0`, `OAI.Laughlin.Certificate.computeLDL_13_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_1`, `OAI.Laughlin.Certificate.computeLDL_13_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_2`, `OAI.Laughlin.Certificate.computeLDL_13_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_3`, `OAI.Laughlin.Certificate.computeLDL_13_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_4`, `OAI.Laughlin.Certificate.computeLDL_13_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_5`, `OAI.Laughlin.Certificate.computeLDL_13_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_6`, `OAI.Laughlin.Certificate.computeLDL_13_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_0`, `OAI.Laughlin.Certificate.computeLDL_13_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_1`, `OAI.Laughlin.Certificate.computeLDL_13_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_2`, `OAI.Laughlin.Certificate.computeLDL_13_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_3`, `OAI.Laughlin.Certificate.computeLDL_13_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_4`, `OAI.Laughlin.Certificate.computeLDL_13_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_5`, `OAI.Laughlin.Certificate.computeLDL_13_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_6`, `OAI.Laughlin.Certificate.computeLDL_13_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_0`, `OAI.Laughlin.Certificate.computeLDL_13_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_1`, `OAI.Laughlin.Certificate.computeLDL_13_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_2`, `OAI.Laughlin.Certificate.computeLDL_13_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_3`, `OAI.Laughlin.Certificate.computeLDL_13_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_4`, `OAI.Laughlin.Certificate.computeLDL_13_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_5`, `OAI.Laughlin.Certificate.computeLDL_13_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_6`, `OAI.Laughlin.Certificate.computeLDL_13_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_0`, `OAI.Laughlin.Certificate.computeLDL_13_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_1`, `OAI.Laughlin.Certificate.computeLDL_13_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_2`, `OAI.Laughlin.Certificate.computeLDL_13_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_3`, `OAI.Laughlin.Certificate.computeLDL_13_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_4`, `OAI.Laughlin.Certificate.computeLDL_13_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_5`, `OAI.Laughlin.Certificate.computeLDL_13_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_6`, `OAI.Laughlin.Certificate.computeLDL_13_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_1_7`, `OAI.Laughlin.Certificate.computeLDL_15_1_7_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_0`, `OAI.Laughlin.Certificate.computeLDL_15_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_1`, `OAI.Laughlin.Certificate.computeLDL_15_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_2`, `OAI.Laughlin.Certificate.computeLDL_15_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_3`, `OAI.Laughlin.Certificate.computeLDL_15_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_4`, `OAI.Laughlin.Certificate.computeLDL_15_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_5`, `OAI.Laughlin.Certificate.computeLDL_15_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_6`, `OAI.Laughlin.Certificate.computeLDL_15_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_7`, `OAI.Laughlin.Certificate.computeLDL_15_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_0`, `OAI.Laughlin.Certificate.computeLDL_15_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_1`, `OAI.Laughlin.Certificate.computeLDL_15_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_2`, `OAI.Laughlin.Certificate.computeLDL_15_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_3`, `OAI.Laughlin.Certificate.computeLDL_15_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_4`, `OAI.Laughlin.Certificate.computeLDL_15_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_5`, `OAI.Laughlin.Certificate.computeLDL_15_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_6`, `OAI.Laughlin.Certificate.computeLDL_15_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_7`, `OAI.Laughlin.Certificate.computeLDL_15_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_0`, `OAI.Laughlin.Certificate.computeLDL_15_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_1`, `OAI.Laughlin.Certificate.computeLDL_15_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_2`, `OAI.Laughlin.Certificate.computeLDL_15_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_3`, `OAI.Laughlin.Certificate.computeLDL_15_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_4`, `OAI.Laughlin.Certificate.computeLDL_15_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_5`, `OAI.Laughlin.Certificate.computeLDL_15_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_6`, `OAI.Laughlin.Certificate.computeLDL_15_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_7`, `OAI.Laughlin.Certificate.computeLDL_15_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_0`, `OAI.Laughlin.Certificate.computeLDL_15_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_1`, `OAI.Laughlin.Certificate.computeLDL_15_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_2`, `OAI.Laughlin.Certificate.computeLDL_15_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_3`, `OAI.Laughlin.Certificate.computeLDL_15_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_4`, `OAI.Laughlin.Certificate.computeLDL_15_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_5`, `OAI.Laughlin.Certificate.computeLDL_15_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_6`, `OAI.Laughlin.Certificate.computeLDL_15_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_7`, `OAI.Laughlin.Certificate.computeLDL_15_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_0`, `OAI.Laughlin.Certificate.computeLDL_15_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_1`, `OAI.Laughlin.Certificate.computeLDL_15_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_2`, `OAI.Laughlin.Certificate.computeLDL_15_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_3`, `OAI.Laughlin.Certificate.computeLDL_15_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_4`, `OAI.Laughlin.Certificate.computeLDL_15_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_5`, `OAI.Laughlin.Certificate.computeLDL_15_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_6`, `OAI.Laughlin.Certificate.computeLDL_15_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_7`, `OAI.Laughlin.Certificate.computeLDL_15_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_0`, `OAI.Laughlin.Certificate.computeLDL_15_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_1`, `OAI.Laughlin.Certificate.computeLDL_15_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_2`, `OAI.Laughlin.Certificate.computeLDL_15_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_3`, `OAI.Laughlin.Certificate.computeLDL_15_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_4`, `OAI.Laughlin.Certificate.computeLDL_15_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_5`, `OAI.Laughlin.Certificate.computeLDL_15_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_6`, `OAI.Laughlin.Certificate.computeLDL_15_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_7`, `OAI.Laughlin.Certificate.computeLDL_15_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_0_10`, `OAI.Laughlin.Certificate.computeLDL_22_0_10_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_0`, `OAI.Laughlin.Certificate.computeLDL_22_10_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_1`, `OAI_Laughlin_Certificate_computeLDL_22_10_10`, `OAI.Laughlin.Certificate.computeLDL_22_10_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_10_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_2`, `OAI.Laughlin.Certificate.computeLDL_22_10_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_3`, `OAI.Laughlin.Certificate.computeLDL_22_10_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_4`, `OAI.Laughlin.Certificate.computeLDL_22_10_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_5`, `OAI.Laughlin.Certificate.computeLDL_22_10_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_6`, `OAI.Laughlin.Certificate.computeLDL_22_10_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_7`, `OAI.Laughlin.Certificate.computeLDL_22_10_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_8`, `OAI.Laughlin.Certificate.computeLDL_22_10_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_9`, `OAI.Laughlin.Certificate.computeLDL_22_10_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_1_10`, `OAI.Laughlin.Certificate.computeLDL_22_1_10_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_1`, `OAI_Laughlin_Certificate_computeLDL_22_2_10`, `OAI.Laughlin.Certificate.computeLDL_22_2_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_2`, `OAI.Laughlin.Certificate.computeLDL_22_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_3`, `OAI.Laughlin.Certificate.computeLDL_22_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_4`, `OAI.Laughlin.Certificate.computeLDL_22_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_5`, `OAI.Laughlin.Certificate.computeLDL_22_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_6`, `OAI.Laughlin.Certificate.computeLDL_22_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_7`, `OAI.Laughlin.Certificate.computeLDL_22_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_8`, `OAI.Laughlin.Certificate.computeLDL_22_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_9`, `OAI.Laughlin.Certificate.computeLDL_22_2_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_0`, `OAI.Laughlin.Certificate.computeLDL_22_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_1`, `OAI_Laughlin_Certificate_computeLDL_22_3_10`, `OAI.Laughlin.Certificate.computeLDL_22_3_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_2`, `OAI.Laughlin.Certificate.computeLDL_22_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_3`, `OAI.Laughlin.Certificate.computeLDL_22_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_4`, `OAI.Laughlin.Certificate.computeLDL_22_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_5`, `OAI.Laughlin.Certificate.computeLDL_22_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_6`, `OAI.Laughlin.Certificate.computeLDL_22_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_7`, `OAI.Laughlin.Certificate.computeLDL_22_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_8`, `OAI.Laughlin.Certificate.computeLDL_22_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_9`, `OAI.Laughlin.Certificate.computeLDL_22_3_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_0`, `OAI.Laughlin.Certificate.computeLDL_22_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_1`, `OAI_Laughlin_Certificate_computeLDL_22_4_10`, `OAI.Laughlin.Certificate.computeLDL_22_4_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_2`, `OAI.Laughlin.Certificate.computeLDL_22_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_3`, `OAI.Laughlin.Certificate.computeLDL_22_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_4`, `OAI.Laughlin.Certificate.computeLDL_22_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_5`, `OAI.Laughlin.Certificate.computeLDL_22_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_6`, `OAI.Laughlin.Certificate.computeLDL_22_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_7`, `OAI.Laughlin.Certificate.computeLDL_22_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_8`, `OAI.Laughlin.Certificate.computeLDL_22_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_9`, `OAI.Laughlin.Certificate.computeLDL_22_4_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_0`, `OAI.Laughlin.Certificate.computeLDL_22_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_1`, `OAI_Laughlin_Certificate_computeLDL_22_5_10`, `OAI.Laughlin.Certificate.computeLDL_22_5_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_2`, `OAI.Laughlin.Certificate.computeLDL_22_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_3`, `OAI.Laughlin.Certificate.computeLDL_22_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_4`, `OAI.Laughlin.Certificate.computeLDL_22_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_5`, `OAI.Laughlin.Certificate.computeLDL_22_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_6`, `OAI.Laughlin.Certificate.computeLDL_22_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_7`, `OAI.Laughlin.Certificate.computeLDL_22_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_8`, `OAI.Laughlin.Certificate.computeLDL_22_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_9`, `OAI.Laughlin.Certificate.computeLDL_22_5_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_0`, `OAI.Laughlin.Certificate.computeLDL_22_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_1`, `OAI_Laughlin_Certificate_computeLDL_22_6_10`, `OAI.Laughlin.Certificate.computeLDL_22_6_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_2`, `OAI.Laughlin.Certificate.computeLDL_22_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_3`, `OAI.Laughlin.Certificate.computeLDL_22_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_4`, `OAI.Laughlin.Certificate.computeLDL_22_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_5`, `OAI.Laughlin.Certificate.computeLDL_22_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_6`, `OAI.Laughlin.Certificate.computeLDL_22_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_7`, `OAI.Laughlin.Certificate.computeLDL_22_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_8`, `OAI.Laughlin.Certificate.computeLDL_22_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_9`, `OAI.Laughlin.Certificate.computeLDL_22_6_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_0`, `OAI.Laughlin.Certificate.computeLDL_22_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_1`, `OAI_Laughlin_Certificate_computeLDL_22_7_10`, `OAI.Laughlin.Certificate.computeLDL_22_7_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_2`, `OAI.Laughlin.Certificate.computeLDL_22_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_3`, `OAI.Laughlin.Certificate.computeLDL_22_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_4`, `OAI.Laughlin.Certificate.computeLDL_22_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_5`, `OAI.Laughlin.Certificate.computeLDL_22_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_6`, `OAI.Laughlin.Certificate.computeLDL_22_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_7`, `OAI.Laughlin.Certificate.computeLDL_22_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_8`, `OAI.Laughlin.Certificate.computeLDL_22_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_9`, `OAI.Laughlin.Certificate.computeLDL_22_7_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_0`, `OAI.Laughlin.Certificate.computeLDL_22_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_1`, `OAI_Laughlin_Certificate_computeLDL_22_8_10`, `OAI.Laughlin.Certificate.computeLDL_22_8_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_2`, `OAI.Laughlin.Certificate.computeLDL_22_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_3`, `OAI.Laughlin.Certificate.computeLDL_22_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_4`, `OAI.Laughlin.Certificate.computeLDL_22_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_5`, `OAI.Laughlin.Certificate.computeLDL_22_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_6`, `OAI.Laughlin.Certificate.computeLDL_22_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_7`, `OAI.Laughlin.Certificate.computeLDL_22_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_8`, `OAI.Laughlin.Certificate.computeLDL_22_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_9`, `OAI.Laughlin.Certificate.computeLDL_22_8_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_0`, `OAI.Laughlin.Certificate.computeLDL_22_9_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_1`, `OAI_Laughlin_Certificate_computeLDL_22_9_10`, `OAI.Laughlin.Certificate.computeLDL_22_9_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_9_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_2`, `OAI.Laughlin.Certificate.computeLDL_22_9_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_3`, `OAI.Laughlin.Certificate.computeLDL_22_9_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_4`, `OAI.Laughlin.Certificate.computeLDL_22_9_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_5`, `OAI.Laughlin.Certificate.computeLDL_22_9_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_6`, `OAI.Laughlin.Certificate.computeLDL_22_9_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_7`, `OAI.Laughlin.Certificate.computeLDL_22_9_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_8`, `OAI.Laughlin.Certificate.computeLDL_22_9_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_9`, `OAI.Laughlin.Certificate.computeLDL_22_9_9_s50`, `OAI_Laughlin_Certificate_yRow_7_3_1_1`, `OAI.Laughlin.Certificate.yRow_7_3_1_1_s50`, `OAI_Laughlin_Certificate_yRow_7_3_1_2`, `OAI.Laughlin.Certificate.yRow_7_3_1_2_s50`, `OAI_Laughlin_Certificate_yRow_7_3_1_3`, `OAI.Laughlin.Certificate.yRow_7_3_1_3_s50`, `OAI_Laughlin_Certificate_yRow_7_3_1_4`, `OAI.Laughlin.Certificate.yRow_7_3_1_4_s50`, `OAI_Laughlin_Certificate_yRow_7_3_1_5`, `OAI.Laughlin.Certificate.yRow_7_3_1_5_s50`, `OAI_Laughlin_Certificate_yRow_7_5_1_2`, `OAI.Laughlin.Certificate.yRow_7_5_1_2_s50`, `OAI_Laughlin_Certificate_yRow_7_5_1_3`, `OAI.Laughlin.Certificate.yRow_7_5_1_3_s50`, `OAI_Laughlin_Certificate_yRow_7_5_1_4`, `OAI.Laughlin.Certificate.yRow_7_5_1_4_s50`, `OAI_Laughlin_Certificate_yRow_7_5_1_5`, `OAI.Laughlin.Certificate.yRow_7_5_1_5_s50`, `OAI_Laughlin_Certificate_yRow_7_5_1_6`, `OAI.Laughlin.Certificate.yRow_7_5_1_6_s50`, `OAI_Laughlin_Certificate_yRow_7_5_3_2`, `OAI.Laughlin.Certificate.yRow_7_5_3_2_s50`, `OAI_Laughlin_Certificate_yRow_7_5_3_3`, `OAI.Laughlin.Certificate.yRow_7_5_3_3_s50`, `OAI_Laughlin_Certificate_yRow_7_5_3_4`, `OAI.Laughlin.Certificate.yRow_7_5_3_4_s50`, `OAI_Laughlin_Certificate_yRow_7_5_3_5`, `OAI.Laughlin.Certificate.yRow_7_5_3_5_s50`, `OAI_Laughlin_Certificate_yRow_7_5_3_6`, `OAI.Laughlin.Certificate.yRow_7_5_3_6_s50`, `OAI_Laughlin_Certificate_yRow_7_7_1_2`, `OAI.Laughlin.Certificate.yRow_7_7_1_2_s50`, `OAI_Laughlin_Certificate_yRow_7_7_1_3`, `OAI.Laughlin.Certificate.yRow_7_7_1_3_s50`, `OAI_Laughlin_Certificate_yRow_7_7_1_4`, `OAI.Laughlin.Certificate.yRow_7_7_1_4_s50`, `OAI_Laughlin_Certificate_yRow_7_7_1_5`, `OAI.Laughlin.Certificate.yRow_7_7_1_5_s50`, `OAI_Laughlin_Certificate_yRow_7_7_1_6`, `OAI.Laughlin.Certificate.yRow_7_7_1_6_s50`, `OAI_Laughlin_Certificate_yRow_7_7_3_2`, `OAI.Laughlin.Certificate.yRow_7_7_3_2_s50`, `OAI_Laughlin_Certificate_yRow_7_7_3_3`, `OAI.Laughlin.Certificate.yRow_7_7_3_3_s50`, `OAI_Laughlin_Certificate_yRow_7_7_3_4`, `OAI.Laughlin.Certificate.yRow_7_7_3_4_s50`, `OAI_Laughlin_Certificate_yRow_7_7_3_5`, `OAI.Laughlin.Certificate.yRow_7_7_3_5_s50`, `OAI_Laughlin_Certificate_yRow_7_7_3_6`, `OAI.Laughlin.Certificate.yRow_7_7_3_6_s50`, `OAI_Laughlin_Certificate_yRow_7_7_5_2`, `OAI.Laughlin.Certificate.yRow_7_7_5_2_s50`, `OAI_Laughlin_Certificate_yRow_7_7_5_3`, `OAI.Laughlin.Certificate.yRow_7_7_5_3_s50`, `OAI_Laughlin_Certificate_yRow_7_7_5_4`, `OAI.Laughlin.Certificate.yRow_7_7_5_4_s50`, `OAI_Laughlin_Certificate_yRow_7_7_5_5`, `OAI.Laughlin.Certificate.yRow_7_7_5_5_s50`, `OAI_Laughlin_Certificate_yRow_7_7_5_6`, `OAI.Laughlin.Certificate.yRow_7_7_5_6_s50` and `OAI_Laughlin_Fock_complexThreeSpinProjector_eigen`; the proofs of `OAI_Laughlin_Certificate_candidateLDL_10`, `OAI.Laughlin.Certificate.candidateLDL_10_s50`, `OAI_Laughlin_Certificate_candidateLDL_11`, `OAI.Laughlin.Certificate.candidateLDL_11_s50`, `OAI_Laughlin_Certificate_candidateLDL_12`, `OAI.Laughlin.Certificate.candidateLDL_12_s50`, `OAI_Laughlin_Certificate_candidateLDL_13`, `OAI.Laughlin.Certificate.candidateLDL_13_s50`, `OAI_Laughlin_Certificate_candidateLDL_15`, `OAI.Laughlin.Certificate.candidateLDL_15_s50`, `OAI_Laughlin_Certificate_candidateLDL_22`, `OAI.Laughlin.Certificate.candidateLDL_22_s50`, `OAI_Laughlin_Certificate_computeLDL_11_5_5`, `OAI.Laughlin.Certificate.computeLDL_11_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_1_5`, `OAI.Laughlin.Certificate.computeLDL_12_1_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_0`, `OAI.Laughlin.Certificate.computeLDL_12_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_1`, `OAI.Laughlin.Certificate.computeLDL_12_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_2`, `OAI.Laughlin.Certificate.computeLDL_12_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_3`, `OAI.Laughlin.Certificate.computeLDL_12_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_4`, `OAI.Laughlin.Certificate.computeLDL_12_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_12_2_5`, `OAI.Laughlin.Certificate.computeLDL_12_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_0`, `OAI.Laughlin.Certificate.computeLDL_12_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_1`, `OAI.Laughlin.Certificate.computeLDL_12_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_2`, `OAI.Laughlin.Certificate.computeLDL_12_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_3`, `OAI.Laughlin.Certificate.computeLDL_12_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_4`, `OAI.Laughlin.Certificate.computeLDL_12_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_12_3_5`, `OAI.Laughlin.Certificate.computeLDL_12_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_0`, `OAI.Laughlin.Certificate.computeLDL_12_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_1`, `OAI.Laughlin.Certificate.computeLDL_12_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_2`, `OAI.Laughlin.Certificate.computeLDL_12_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_3`, `OAI.Laughlin.Certificate.computeLDL_12_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_4`, `OAI.Laughlin.Certificate.computeLDL_12_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_12_4_5`, `OAI.Laughlin.Certificate.computeLDL_12_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_0`, `OAI.Laughlin.Certificate.computeLDL_12_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_1`, `OAI.Laughlin.Certificate.computeLDL_12_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_2`, `OAI.Laughlin.Certificate.computeLDL_12_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_3`, `OAI.Laughlin.Certificate.computeLDL_12_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_4`, `OAI.Laughlin.Certificate.computeLDL_12_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_12_5_5`, `OAI.Laughlin.Certificate.computeLDL_12_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_13_1_6`, `OAI.Laughlin.Certificate.computeLDL_13_1_6_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_0`, `OAI.Laughlin.Certificate.computeLDL_13_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_1`, `OAI.Laughlin.Certificate.computeLDL_13_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_2`, `OAI.Laughlin.Certificate.computeLDL_13_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_3`, `OAI.Laughlin.Certificate.computeLDL_13_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_4`, `OAI.Laughlin.Certificate.computeLDL_13_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_5`, `OAI.Laughlin.Certificate.computeLDL_13_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_13_2_6`, `OAI.Laughlin.Certificate.computeLDL_13_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_0`, `OAI.Laughlin.Certificate.computeLDL_13_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_1`, `OAI.Laughlin.Certificate.computeLDL_13_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_2`, `OAI.Laughlin.Certificate.computeLDL_13_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_3`, `OAI.Laughlin.Certificate.computeLDL_13_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_4`, `OAI.Laughlin.Certificate.computeLDL_13_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_5`, `OAI.Laughlin.Certificate.computeLDL_13_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_13_3_6`, `OAI.Laughlin.Certificate.computeLDL_13_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_0`, `OAI.Laughlin.Certificate.computeLDL_13_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_1`, `OAI.Laughlin.Certificate.computeLDL_13_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_2`, `OAI.Laughlin.Certificate.computeLDL_13_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_3`, `OAI.Laughlin.Certificate.computeLDL_13_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_4`, `OAI.Laughlin.Certificate.computeLDL_13_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_5`, `OAI.Laughlin.Certificate.computeLDL_13_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_13_4_6`, `OAI.Laughlin.Certificate.computeLDL_13_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_0`, `OAI.Laughlin.Certificate.computeLDL_13_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_1`, `OAI.Laughlin.Certificate.computeLDL_13_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_2`, `OAI.Laughlin.Certificate.computeLDL_13_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_3`, `OAI.Laughlin.Certificate.computeLDL_13_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_4`, `OAI.Laughlin.Certificate.computeLDL_13_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_5`, `OAI.Laughlin.Certificate.computeLDL_13_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_13_5_6`, `OAI.Laughlin.Certificate.computeLDL_13_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_0`, `OAI.Laughlin.Certificate.computeLDL_13_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_1`, `OAI.Laughlin.Certificate.computeLDL_13_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_2`, `OAI.Laughlin.Certificate.computeLDL_13_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_3`, `OAI.Laughlin.Certificate.computeLDL_13_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_4`, `OAI.Laughlin.Certificate.computeLDL_13_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_5`, `OAI.Laughlin.Certificate.computeLDL_13_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_13_6_6`, `OAI.Laughlin.Certificate.computeLDL_13_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_1_7`, `OAI.Laughlin.Certificate.computeLDL_15_1_7_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_0`, `OAI.Laughlin.Certificate.computeLDL_15_2_0_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_1`, `OAI.Laughlin.Certificate.computeLDL_15_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_2`, `OAI.Laughlin.Certificate.computeLDL_15_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_3`, `OAI.Laughlin.Certificate.computeLDL_15_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_4`, `OAI.Laughlin.Certificate.computeLDL_15_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_5`, `OAI.Laughlin.Certificate.computeLDL_15_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_6`, `OAI.Laughlin.Certificate.computeLDL_15_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_2_7`, `OAI.Laughlin.Certificate.computeLDL_15_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_0`, `OAI.Laughlin.Certificate.computeLDL_15_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_1`, `OAI.Laughlin.Certificate.computeLDL_15_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_2`, `OAI.Laughlin.Certificate.computeLDL_15_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_3`, `OAI.Laughlin.Certificate.computeLDL_15_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_4`, `OAI.Laughlin.Certificate.computeLDL_15_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_5`, `OAI.Laughlin.Certificate.computeLDL_15_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_6`, `OAI.Laughlin.Certificate.computeLDL_15_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_3_7`, `OAI.Laughlin.Certificate.computeLDL_15_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_0`, `OAI.Laughlin.Certificate.computeLDL_15_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_1`, `OAI.Laughlin.Certificate.computeLDL_15_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_2`, `OAI.Laughlin.Certificate.computeLDL_15_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_3`, `OAI.Laughlin.Certificate.computeLDL_15_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_4`, `OAI.Laughlin.Certificate.computeLDL_15_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_5`, `OAI.Laughlin.Certificate.computeLDL_15_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_6`, `OAI.Laughlin.Certificate.computeLDL_15_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_4_7`, `OAI.Laughlin.Certificate.computeLDL_15_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_0`, `OAI.Laughlin.Certificate.computeLDL_15_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_1`, `OAI.Laughlin.Certificate.computeLDL_15_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_2`, `OAI.Laughlin.Certificate.computeLDL_15_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_3`, `OAI.Laughlin.Certificate.computeLDL_15_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_4`, `OAI.Laughlin.Certificate.computeLDL_15_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_5`, `OAI.Laughlin.Certificate.computeLDL_15_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_6`, `OAI.Laughlin.Certificate.computeLDL_15_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_5_7`, `OAI.Laughlin.Certificate.computeLDL_15_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_0`, `OAI.Laughlin.Certificate.computeLDL_15_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_1`, `OAI.Laughlin.Certificate.computeLDL_15_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_2`, `OAI.Laughlin.Certificate.computeLDL_15_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_3`, `OAI.Laughlin.Certificate.computeLDL_15_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_4`, `OAI.Laughlin.Certificate.computeLDL_15_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_5`, `OAI.Laughlin.Certificate.computeLDL_15_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_6`, `OAI.Laughlin.Certificate.computeLDL_15_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_6_7`, `OAI.Laughlin.Certificate.computeLDL_15_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_0`, `OAI.Laughlin.Certificate.computeLDL_15_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_1`, `OAI.Laughlin.Certificate.computeLDL_15_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_2`, `OAI.Laughlin.Certificate.computeLDL_15_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_3`, `OAI.Laughlin.Certificate.computeLDL_15_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_4`, `OAI.Laughlin.Certificate.computeLDL_15_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_5`, `OAI.Laughlin.Certificate.computeLDL_15_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_6`, `OAI.Laughlin.Certificate.computeLDL_15_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_15_7_7`, `OAI.Laughlin.Certificate.computeLDL_15_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_0_10`, `OAI.Laughlin.Certificate.computeLDL_22_0_10_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_0`, `OAI.Laughlin.Certificate.computeLDL_22_10_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_1`, `OAI_Laughlin_Certificate_computeLDL_22_10_10`, `OAI.Laughlin.Certificate.computeLDL_22_10_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_10_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_2`, `OAI.Laughlin.Certificate.computeLDL_22_10_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_3`, `OAI.Laughlin.Certificate.computeLDL_22_10_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_4`, `OAI.Laughlin.Certificate.computeLDL_22_10_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_5`, `OAI.Laughlin.Certificate.computeLDL_22_10_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_6`, `OAI.Laughlin.Certificate.computeLDL_22_10_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_7`, `OAI.Laughlin.Certificate.computeLDL_22_10_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_8`, `OAI.Laughlin.Certificate.computeLDL_22_10_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_10_9`, `OAI.Laughlin.Certificate.computeLDL_22_10_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_1_10`, `OAI.Laughlin.Certificate.computeLDL_22_1_10_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_1`, `OAI_Laughlin_Certificate_computeLDL_22_2_10`, `OAI.Laughlin.Certificate.computeLDL_22_2_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_2_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_2`, `OAI.Laughlin.Certificate.computeLDL_22_2_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_3`, `OAI.Laughlin.Certificate.computeLDL_22_2_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_4`, `OAI.Laughlin.Certificate.computeLDL_22_2_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_5`, `OAI.Laughlin.Certificate.computeLDL_22_2_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_6`, `OAI.Laughlin.Certificate.computeLDL_22_2_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_7`, `OAI.Laughlin.Certificate.computeLDL_22_2_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_8`, `OAI.Laughlin.Certificate.computeLDL_22_2_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_2_9`, `OAI.Laughlin.Certificate.computeLDL_22_2_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_0`, `OAI.Laughlin.Certificate.computeLDL_22_3_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_1`, `OAI_Laughlin_Certificate_computeLDL_22_3_10`, `OAI.Laughlin.Certificate.computeLDL_22_3_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_3_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_2`, `OAI.Laughlin.Certificate.computeLDL_22_3_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_3`, `OAI.Laughlin.Certificate.computeLDL_22_3_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_4`, `OAI.Laughlin.Certificate.computeLDL_22_3_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_5`, `OAI.Laughlin.Certificate.computeLDL_22_3_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_6`, `OAI.Laughlin.Certificate.computeLDL_22_3_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_7`, `OAI.Laughlin.Certificate.computeLDL_22_3_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_8`, `OAI.Laughlin.Certificate.computeLDL_22_3_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_3_9`, `OAI.Laughlin.Certificate.computeLDL_22_3_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_0`, `OAI.Laughlin.Certificate.computeLDL_22_4_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_1`, `OAI_Laughlin_Certificate_computeLDL_22_4_10`, `OAI.Laughlin.Certificate.computeLDL_22_4_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_4_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_2`, `OAI.Laughlin.Certificate.computeLDL_22_4_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_3`, `OAI.Laughlin.Certificate.computeLDL_22_4_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_4`, `OAI.Laughlin.Certificate.computeLDL_22_4_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_5`, `OAI.Laughlin.Certificate.computeLDL_22_4_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_6`, `OAI.Laughlin.Certificate.computeLDL_22_4_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_7`, `OAI.Laughlin.Certificate.computeLDL_22_4_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_8`, `OAI.Laughlin.Certificate.computeLDL_22_4_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_4_9`, `OAI.Laughlin.Certificate.computeLDL_22_4_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_0`, `OAI.Laughlin.Certificate.computeLDL_22_5_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_1`, `OAI_Laughlin_Certificate_computeLDL_22_5_10`, `OAI.Laughlin.Certificate.computeLDL_22_5_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_5_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_2`, `OAI.Laughlin.Certificate.computeLDL_22_5_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_3`, `OAI.Laughlin.Certificate.computeLDL_22_5_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_4`, `OAI.Laughlin.Certificate.computeLDL_22_5_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_5`, `OAI.Laughlin.Certificate.computeLDL_22_5_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_6`, `OAI.Laughlin.Certificate.computeLDL_22_5_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_7`, `OAI.Laughlin.Certificate.computeLDL_22_5_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_8`, `OAI.Laughlin.Certificate.computeLDL_22_5_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_5_9`, `OAI.Laughlin.Certificate.computeLDL_22_5_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_0`, `OAI.Laughlin.Certificate.computeLDL_22_6_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_1`, `OAI_Laughlin_Certificate_computeLDL_22_6_10`, `OAI.Laughlin.Certificate.computeLDL_22_6_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_6_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_2`, `OAI.Laughlin.Certificate.computeLDL_22_6_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_3`, `OAI.Laughlin.Certificate.computeLDL_22_6_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_4`, `OAI.Laughlin.Certificate.computeLDL_22_6_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_5`, `OAI.Laughlin.Certificate.computeLDL_22_6_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_6`, `OAI.Laughlin.Certificate.computeLDL_22_6_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_7`, `OAI.Laughlin.Certificate.computeLDL_22_6_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_8`, `OAI.Laughlin.Certificate.computeLDL_22_6_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_6_9`, `OAI.Laughlin.Certificate.computeLDL_22_6_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_0`, `OAI.Laughlin.Certificate.computeLDL_22_7_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_1`, `OAI_Laughlin_Certificate_computeLDL_22_7_10`, `OAI.Laughlin.Certificate.computeLDL_22_7_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_7_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_2`, `OAI.Laughlin.Certificate.computeLDL_22_7_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_3`, `OAI.Laughlin.Certificate.computeLDL_22_7_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_4`, `OAI.Laughlin.Certificate.computeLDL_22_7_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_5`, `OAI.Laughlin.Certificate.computeLDL_22_7_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_6`, `OAI.Laughlin.Certificate.computeLDL_22_7_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_7`, `OAI.Laughlin.Certificate.computeLDL_22_7_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_8`, `OAI.Laughlin.Certificate.computeLDL_22_7_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_7_9`, `OAI.Laughlin.Certificate.computeLDL_22_7_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_0`, `OAI.Laughlin.Certificate.computeLDL_22_8_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_1`, `OAI_Laughlin_Certificate_computeLDL_22_8_10`, `OAI.Laughlin.Certificate.computeLDL_22_8_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_8_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_2`, `OAI.Laughlin.Certificate.computeLDL_22_8_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_3`, `OAI.Laughlin.Certificate.computeLDL_22_8_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_4`, `OAI.Laughlin.Certificate.computeLDL_22_8_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_5`, `OAI.Laughlin.Certificate.computeLDL_22_8_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_6`, `OAI.Laughlin.Certificate.computeLDL_22_8_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_7`, `OAI.Laughlin.Certificate.computeLDL_22_8_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_8`, `OAI.Laughlin.Certificate.computeLDL_22_8_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_8_9`, `OAI.Laughlin.Certificate.computeLDL_22_8_9_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_0`, `OAI.Laughlin.Certificate.computeLDL_22_9_0_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_1`, `OAI_Laughlin_Certificate_computeLDL_22_9_10`, `OAI.Laughlin.Certificate.computeLDL_22_9_10_s50`, `OAI.Laughlin.Certificate.computeLDL_22_9_1_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_2`, `OAI.Laughlin.Certificate.computeLDL_22_9_2_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_3`, `OAI.Laughlin.Certificate.computeLDL_22_9_3_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_4`, `OAI.Laughlin.Certificate.computeLDL_22_9_4_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_5`, `OAI.Laughlin.Certificate.computeLDL_22_9_5_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_6`, `OAI.Laughlin.Certificate.computeLDL_22_9_6_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_7`, `OAI.Laughlin.Certificate.computeLDL_22_9_7_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_8`, `OAI.Laughlin.Certificate.computeLDL_22_9_8_s50`, `OAI_Laughlin_Certificate_computeLDL_22_9_9`, `OAI.Laughlin.Certificate.computeLDL_22_9_9_s50`, `OAI_Laughlin_Certificate_yRow_7_3_1_1`, `OAI.Laughlin.Certificate.yRow_7_3_1_1_s50`, `OAI_Laughlin_Certificate_yRow_7_3_1_2`, `OAI.Laughlin.Certificate.yRow_7_3_1_2_s50`, `OAI_Laughlin_Certificate_yRow_7_3_1_3`, `OAI.Laughlin.Certificate.yRow_7_3_1_3_s50`, `OAI_Laughlin_Certificate_yRow_7_3_1_4`, `OAI.Laughlin.Certificate.yRow_7_3_1_4_s50`, `OAI_Laughlin_Certificate_yRow_7_3_1_5`, `OAI.Laughlin.Certificate.yRow_7_3_1_5_s50`, `OAI_Laughlin_Certificate_yRow_7_5_1_2`, `OAI.Laughlin.Certificate.yRow_7_5_1_2_s50`, `OAI_Laughlin_Certificate_yRow_7_5_1_3`, `OAI.Laughlin.Certificate.yRow_7_5_1_3_s50`, `OAI_Laughlin_Certificate_yRow_7_5_1_4`, `OAI.Laughlin.Certificate.yRow_7_5_1_4_s50`, `OAI_Laughlin_Certificate_yRow_7_5_1_5`, `OAI.Laughlin.Certificate.yRow_7_5_1_5_s50`, `OAI_Laughlin_Certificate_yRow_7_5_1_6`, `OAI.Laughlin.Certificate.yRow_7_5_1_6_s50`, `OAI_Laughlin_Certificate_yRow_7_7_1_2`, `OAI.Laughlin.Certificate.yRow_7_7_1_2_s50`, `OAI_Laughlin_Certificate_yRow_7_7_1_3` and `OAI.Laughlin.Certificate.yRow_7_7_1_3_s50`.
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
def candidateY_10 : Matrix (Fin 5) (Fin 5) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 3252603773208384966897801/134217728000000000000
  | 0, 1 => -1219963203744052188572919/167772160000000000000
  | 0, 2 => 1233781148459940320874483/134217728000000000000
  | 0, 3 => -4673143458544379455879083/335544320000000000000
  | 0, 4 => 2012606963507139814961019/83886080000000000000
  | 1, 0 => -1219963203744052188572919/167772160000000000000
  | 1, 1 => 23917264894764854794377/16777216000000000000
  | 1, 2 => -13854999171694482915831/8388608000000000000
  | 1, 3 => 57805337880323795919969/16777216000000000000
  | 1, 4 => -52562004903703102850037/5242880000000000000
  | 2, 0 => 1233781148459940320874483/134217728000000000000
  | 2, 1 => -13854999171694482915831/8388608000000000000
  | 2, 2 => 2285267576183515842978393/939524096000000000000
  | 2, 3 => -121198635809384297528619/67108864000000000000
  | 2, 4 => 127922353790121014632767/16777216000000000000
  | 3, 0 => -4673143458544379455879083/335544320000000000000
  | 3, 1 => 57805337880323795919969/16777216000000000000
  | 3, 2 => -121198635809384297528619/67108864000000000000
  | 3, 3 => 51194502011873480782923/167772160000000000000
  | 3, 4 => 10203611212469228878953/41943040000000000000
  | 4, 0 => 2012606963507139814961019/83886080000000000000
  | 4, 1 => -52562004903703102850037/5242880000000000000
  | 4, 2 => 127922353790121014632767/16777216000000000000
  | 4, 3 => 10203611212469228878953/41943040000000000000
  | 4, 4 => -990036939147267786688413/10485760000000000000
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
def candidateY_11 : Matrix (Fin 6) (Fin 6) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 15310420495743050456853357/134217728000000000000
  | 0, 1 => -21091981152473935416162441/335544320000000000000
  | 0, 2 => 1759644912412486678804947/134217728000000000000
  | 0, 3 => -7117902998608090523107887/335544320000000000000
  | 0, 4 => 2050140304557578762479287/16777216000000000000
  | 0, 5 => -3816671070411211699962099/8388608000000000000
  | 1, 0 => -21091981152473935416162441/335544320000000000000
  | 1, 1 => 3139824493398164330092707/167772160000000000000
  | 1, 2 => -110846050581407277067047/13421772800000000000
  | 1, 3 => -120000452149124136234801/167772160000000000000
  | 1, 4 => -804905973848069092119267/41943040000000000000
  | 1, 5 => -488664944191263381981813/20971520000000000000
  | 2, 0 => 1759644912412486678804947/134217728000000000000
  | 2, 1 => -110846050581407277067047/13421772800000000000
  | 2, 2 => 186561496958160530399967/134217728000000000000
  | 2, 3 => -132022995280028243088831/67108864000000000000
  | 2, 4 => 39011604836809336804287/16777216000000000000
  | 2, 5 => -536635508982633719381547/8388608000000000000
  | 3, 0 => -7117902998608090523107887/335544320000000000000
  | 3, 1 => -120000452149124136234801/167772160000000000000
  | 3, 2 => -132022995280028243088831/67108864000000000000
  | 3, 3 => 53081184869685889157043/167772160000000000000
  | 3, 4 => 581826960578730870868149/41943040000000000000
  | 3, 5 => 48169578758531066711919/20971520000000000000
  | 4, 0 => 2050140304557578762479287/16777216000000000000
  | 4, 1 => -804905973848069092119267/41943040000000000000
  | 4, 2 => 39011604836809336804287/16777216000000000000
  | 4, 3 => 581826960578730870868149/41943040000000000000
  | 4, 4 => -985704999590345844614157/10485760000000000000
  | 4, 5 => 390621018140645815377261/1048576000000000000
  | 5, 0 => -3816671070411211699962099/8388608000000000000
  | 5, 1 => -488664944191263381981813/20971520000000000000
  | 5, 2 => -536635508982633719381547/8388608000000000000
  | 5, 3 => 48169578758531066711919/20971520000000000000
  | 5, 4 => 390621018140645815377261/1048576000000000000
  | 5, 5 => -7434351034101698173344801/524288000000000000
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
def candidateY_12 : Matrix (Fin 6) (Fin 6) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => -21758497948837526814361611/16777216000000000000
  | 0, 1 => 7514500960705467759694389/41943040000000000000
  | 0, 2 => 3165688667606660909537571/16777216000000000000
  | 0, 3 => -41707520784065633150907/8388608000000000000
  | 0, 4 => -2287894342236011100448461/10485760000000000000
  | 0, 5 => 974459105668097994666249/1048576000000000000
  | 1, 0 => 7514500960705467759694389/41943040000000000000
  | 1, 1 => -2755174567464265689714987/41943040000000000000
  | 1, 2 => 13005450739700130750669/8388608000000000000
  | 1, 3 => 81483121238154923538567/4194304000000000000
  | 1, 4 => 404785016635235824043973/5242880000000000000
  | 1, 5 => 6215584013984995241823/40960000000000000
  | 2, 0 => 3165688667606660909537571/16777216000000000000
  | 2, 1 => 13005450739700130750669/8388608000000000000
  | 2, 2 => 46805674377515194537803/3355443200000000000
  | 2, 3 => -41483885509932371903727/8388608000000000000
  | 2, 4 => -10240121934522536047317/419430400000000000
  | 2, 5 => -25627330574660171363787/1048576000000000000
  | 3, 0 => -41707520784065633150907/8388608000000000000
  | 3, 1 => 81483121238154923538567/4194304000000000000
  | 3, 2 => -41483885509932371903727/8388608000000000000
  | 3, 3 => -192219299280069275276433/4194304000000000000
  | 3, 4 => -42262827210616968341919/1048576000000000000
  | 3, 5 => 102387833991081458685459/524288000000000000
  | 4, 0 => -2287894342236011100448461/10485760000000000000
  | 4, 1 => 404785016635235824043973/5242880000000000000
  | 4, 2 => -10240121934522536047317/419430400000000000
  | 4, 3 => -42262827210616968341919/1048576000000000000
  | 4, 4 => 42184147125974825030859/1310720000000000000
  | 4, 5 => 18732467483584451907057/655360000000000000
  | 5, 0 => 974459105668097994666249/1048576000000000000
  | 5, 1 => 6215584013984995241823/40960000000000000
  | 5, 2 => -25627330574660171363787/1048576000000000000
  | 5, 3 => 102387833991081458685459/524288000000000000
  | 5, 4 => 18732467483584451907057/655360000000000000
  | 5, 5 => -330567209557174956464307/65536000000000000
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
def candidateY_13 : Matrix (Fin 7) (Fin 7) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 121685493803305440547576917/8388608000000000000
  | 0, 1 => 7563908306608840424871171/8388608000000000000
  | 0, 2 => -66091999624888726298111247/16777216000000000000
  | 0, 3 => 2728798823338271240310567/1677721600000000000
  | 0, 4 => -13501297339814524797227781/10485760000000000000
  | 0, 5 => 12432022452888993488134359/1048576000000000000
  | 0, 6 => -165874530574631465579316753/1048576000000000000
  | 1, 0 => 7563908306608840424871171/8388608000000000000
  | 1, 1 => -2041302613950531427151763/8388608000000000000
  | 1, 2 => 126715690823288866730217/419430400000000000
  | 1, 3 => -500594098074230841463629/2097152000000000000
  | 1, 4 => -1215155073315811787592453/2621440000000000000
  | 1, 5 => -47337050492347165740927/524288000000000000
  | 1, 6 => -394753123867351949086959/131072000000000000
  | 2, 0 => -66091999624888726298111247/16777216000000000000
  | 2, 1 => 126715690823288866730217/419430400000000000
  | 2, 2 => -1379799513707028925041063/16777216000000000000
  | 2, 3 => 701982483744393187744923/8388608000000000000
  | 2, 4 => 672840394965225922256721/2097152000000000000
  | 2, 5 => 2506297034373528441573/1048576000000000000
  | 2, 6 => 5534718096701578046307903/1048576000000000000
  | 3, 0 => 2728798823338271240310567/1677721600000000000
  | 3, 1 => -500594098074230841463629/2097152000000000000
  | 3, 2 => 701982483744393187744923/8388608000000000000
  | 3, 3 => 126607865811947282465541/838860800000000000
  | 3, 4 => -175665130303631642663517/1048576000000000000
  | 3, 5 => 420722950805223871087107/524288000000000000
  | 3, 6 => -2485443250416390286101651/524288000000000000
  | 4, 0 => -13501297339814524797227781/10485760000000000000
  | 4, 1 => -1215155073315811787592453/2621440000000000000
  | 4, 2 => 672840394965225922256721/2097152000000000000
  | 4, 3 => -175665130303631642663517/1048576000000000000
  | 4, 4 => -125541053085493256369427/262144000000000000
  | 4, 5 => 1437479079722043725179197/655360000000000000
  | 4, 6 => -2022830025440980274156781/655360000000000000
  | 5, 0 => 12432022452888993488134359/1048576000000000000
  | 5, 1 => -47337050492347165740927/524288000000000000
  | 5, 2 => 2506297034373528441573/1048576000000000000
  | 5, 3 => 420722950805223871087107/524288000000000000
  | 5, 4 => 1437479079722043725179197/655360000000000000
  | 5, 5 => -184207969249874832456117/65536000000000000
  | 5, 6 => 252554056596275363975331/65536000000000000
  | 6, 0 => -165874530574631465579316753/1048576000000000000
  | 6, 1 => -394753123867351949086959/131072000000000000
  | 6, 2 => 5534718096701578046307903/1048576000000000000
  | 6, 3 => -2485443250416390286101651/524288000000000000
  | 6, 4 => -2022830025440980274156781/655360000000000000
  | 6, 5 => 252554056596275363975331/65536000000000000
  | 6, 6 => -17580701774552693245136811/13107200000000000
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
def candidateY_15 : Matrix (Fin 8) (Fin 8) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1160239161688954312188380157/1048576000000000000
  | 0, 1 => 527769145158896263581537579/2097152000000000000
  | 0, 2 => -364633884256427977153375413/1677721600000000000
  | 0, 3 => 70800295830292526868599229/838860800000000000
  | 0, 4 => -213215905018995130639958571/1048576000000000000
  | 0, 5 => -236988935373506936612565573/524288000000000000
  | 0, 6 => 374746885492881333249210393/524288000000000000
  | 0, 7 => -1454272995490648196091417189/52428800000000000
  | 1, 0 => 527769145158896263581537579/2097152000000000000
  | 1, 1 => -79903889464778925306594867/2097152000000000000
  | 1, 2 => 10380910649344519579874271/838860800000000000
  | 1, 3 => 2399450471501791440121389/419430400000000000
  | 1, 4 => 7831247768240800098462597/524288000000000000
  | 1, 5 => 260365051976410952573409/52428800000000000
  | 1, 6 => 15417580069242120546303813/262144000000000000
  | 1, 7 => -19651317795670208550803901/26214400000000000
  | 2, 0 => -364633884256427977153375413/1677721600000000000
  | 2, 1 => 10380910649344519579874271/838860800000000000
  | 2, 2 => -544144788797698439940321/335544320000000000
  | 2, 3 => -1550173356554793074510931/838860800000000000
  | 2, 4 => -251612565167710626302493/209715200000000000
  | 2, 5 => 412467042517374252900789/104857600000000000
  | 2, 6 => -3917597116231063282740723/104857600000000000
  | 2, 7 => 6737890215993101774728119/10485760000000000
  | 3, 0 => 70800295830292526868599229/838860800000000000
  | 3, 1 => 2399450471501791440121389/419430400000000000
  | 3, 2 => -1550173356554793074510931/838860800000000000
  | 3, 3 => -11010455047903773080463201/2097152000000000000
  | 3, 4 => 483384920806779568744041/524288000000000000
  | 3, 5 => -2196385127442123145785873/262144000000000000
  | 3, 6 => -3020058706667129324414217/262144000000000000
  | 3, 7 => 6630571266894369608354541/26214400000000000
  | 4, 0 => -213215905018995130639958571/1048576000000000000
  | 4, 1 => 7831247768240800098462597/524288000000000000
  | 4, 2 => -251612565167710626302493/209715200000000000
  | 4, 3 => 483384920806779568744041/524288000000000000
  | 4, 4 => -733927230254603053476261/131072000000000000
  | 4, 5 => 144198476217622441333917/65536000000000000
  | 4, 6 => -270537545003843608530039/65536000000000000
  | 4, 7 => 488416974255188057862783/1310720000000000
  | 5, 0 => -236988935373506936612565573/524288000000000000
  | 5, 1 => 260365051976410952573409/52428800000000000
  | 5, 2 => 412467042517374252900789/104857600000000000
  | 5, 3 => -2196385127442123145785873/262144000000000000
  | 5, 4 => 144198476217622441333917/65536000000000000
  | 5, 5 => 103242122786757662097687/32768000000000000
  | 5, 6 => -1188419411670004290171681/32768000000000000
  | 5, 7 => -946932022961651320973379/3276800000000000
  | 6, 0 => 374746885492881333249210393/524288000000000000
  | 6, 1 => 15417580069242120546303813/262144000000000000
  | 6, 2 => -3917597116231063282740723/104857600000000000
  | 6, 3 => -3020058706667129324414217/262144000000000000
  | 6, 4 => -270537545003843608530039/65536000000000000
  | 6, 5 => -1188419411670004290171681/32768000000000000
  | 6, 6 => -13385634727914986582216457/32768000000000000
  | 6, 7 => 6044229669744752465993013/3276800000000000
  | 7, 0 => -1454272995490648196091417189/52428800000000000
  | 7, 1 => -19651317795670208550803901/26214400000000000
  | 7, 2 => 6737890215993101774728119/10485760000000000
  | 7, 3 => 6630571266894369608354541/26214400000000000
  | 7, 4 => 488416974255188057862783/1310720000000000
  | 7, 5 => -946932022961651320973379/3276800000000000
  | 7, 6 => 6044229669744752465993013/3276800000000000
  | 7, 7 => -31526289117493065494479881/327680000000000
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
def candidateY_22 : Matrix (Fin 11) (Fin 11) ℚ := fun i j =>
  match i.val, j.val with
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

def rows : List (ℕ × ℤ × List (ℕ × ℕ × ℤ)) :=
  [(0, 7181518, [(0, 5, -849651), (0, 7, -2958744), (1, 5, 751659), (1, 6, -43084), (1, 7, -146216), (3, 2, 720949), (3, 5, -127514), (4, 2, 222437), (4, 3, -262822), (5, 3, -117700), (6, 1, -55024), (7, 1, -166049)]),
   (1, -112991, [(0, 5, 142772), (0, 6, -142342), (0, 7, 527055), (0, 8, 50742), (1, 6, 197917), (1, 8, -18343), (2, 4, 5764), (2, 7, -21183), (3, 2, 75832), (3, 5, -6115), (4, 5, 2660), (5, 3, -9455), (6, 1, -27091), (6, 3, -3494), (7, 1, 479), (7, 2, -15331)]),
   (1, -4247311, [(0, 5, -12207250), (0, 6, -14064191), (0, 7, -14063663), (0, 8, -15662679), (1, 6, 483831), (1, 8, 3987214), (2, 4, -814558), (2, 7, 888887), (3, 2, 966462), (3, 5, 145978), (4, 5, -171722), (5, 3, 34350), (6, 1, 389319), (6, 3, 97603), (7, 1, 412447), (7, 2, -53786)]),
   (2, 3438746, [(1, 4, 6689266), (1, 5, 6620205), (1, 6, 6625065), (1, 7, 4969272), (1, 8, 4878238), (2, 7, -1387380), (3, 6, -586188), (3, 7, 344087), (4, 2, -1120634), (4, 5, -318530), (4, 6, 559169), (5, 5, 157455), (6, 1, 1207103), (6, 3, 211617), (6, 4, 33240), (7, 1, 577001), (7, 3, -142578)]),
   (5, -98645, [(0, 5, -2719776), (0, 8, -8519913), (1, 4, -949523), (1, 7, -1952105), (1, 8, -1562606), (2, 8, -8919966), (3, 2, 248826), (3, 5, -1017623), (3, 7, 3656005), (3, 8, -2081871), (4, 2, -33163), (4, 3, -305905), (4, 6, 35677), (4, 7, -1320749), (4, 8, -1040378), (5, 3, 502094), (5, 5, 1060633), (5, 8, -998003), (6, 1, -113617), (6, 3, 184919), (6, 4, 209239), (6, 5, -68198), (6, 7, -266297), (7, 2, -606696), (7, 3, -563620), (7, 4, 437345), (7, 6, -432189)]),
   (5, -3160276, [(0, 5, -1698129), (0, 8, 10575875), (1, 4, -252576), (1, 7, -8002616), (1, 8, 22592844), (2, 8, 7370640), (3, 2, 289294), (3, 5, 1400647), (3, 7, 1987740), (3, 8, 4030699), (4, 2, -1731401), (4, 3, -1034062), (4, 6, -1106371), (4, 7, -1257051), (4, 8, 1461735), (5, 3, 1408149), (5, 5, 1136847), (5, 8, 1878501), (6, 1, -2838516), (6, 3, -734099), (6, 4, 1062416), (6, 5, 11745), (6, 7, 611312), (7, 2, -480776), (7, 3, 20459), (7, 4, 316925), (7, 6, 37092)]),
   (7, 1441784, [(0, 7, 3441286), (0, 8, -6097155), (3, 7, -1002399), (4, 7, -251321), (5, 8, 1143225), (6, 6, -17397), (7, 1, -1007464), (7, 3, -662286), (7, 6, -344621), (7, 8, -1115284)])]

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Integral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

def arithmeticScale : ℚ := 2^64 * (Nat.factorial 24 : ℚ)

end Laughlin.Certificate

end OAI
end


