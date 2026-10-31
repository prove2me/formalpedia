-- Prove2me | Definitions.Def_OAIQ024S016
-- name    : OAIQ024S016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T21:23:06.483646+00:00
-- url     : https://prove2.me/theorems/b5a10e88-d06c-4b61-a86a-d951c9a49baa
-- title:
--   Definitions bundle OAIQ024S016 of the split of OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 58 declarations of OpenAI's Lean: 55 definitions, 1 inductive type or structure and 2 theorems. The definitions and types are `OAI.SKRatio.Certificate.Expr.cell`, `OAI.SKRatio.Certificate.Expr.check`, `OAI.SKRatio.Certificate.Expr.compute`, `OAI.SKRatio.Certificate.Expr.quad`, `OAI.SKRatio.Certificate.Expr.sec`, `OAI.SKRatio.Certificate.Valid`, `OAI.SKRatio.Certificate.batchCheck`, `OAI.SKRatio.Fields.gibbsScale`, `OAI.SKRatio.Fields.heatBathGenerator`, `OAI.SKRatio.Fields.heatBathLinear`, `OAI.SKRatio.Fields.linearObservable`, `OAI.SKRatio.Fields.localField`, `OAI.SKRatio.Fields.pairConditionalMean`, `OAI.SKRatio.Fields.realSpinEnergy`, `OAI.SKRatio.Fields.sitePrior`, `OAI.SKRatio.Fields.siteVariance`, `OAI.SKRatio.Fields.spinGradient`, `OAI.SKRatio.Fields.variance`, `OAI.SKRatio.Gaussian.matrixGood`, `OAI.SKRatio.Observation.Channel.divergenceIntegrand`, `OAI.SKRatio.Observation.Channel.interaction`, `OAI.SKRatio.Observation.Channel.majorant`, `OAI.SKRatio.Observation.Channel.pairKernel`, `OAI.SKRatio.Observation.Channel.pairShift`, `OAI.SKRatio.Observation.Channel.posterior`, `OAI.SKRatio.Observation.Channel.quadraticIntegrand`, `OAI.SKRatio.Observation.History.density`, `OAI.SKRatio.Observation.History.posterior`, `OAI.SKRatio.Observation.History.remainingEntropy`, `OAI.SKRatio.Observation.ent`, `OAI.SKRatio.Observation.fieldPrior`, `OAI.SKRatio.Observation.gibbsFeature`, `OAI.SKRatio.Observation.gibbsPrior`, `OAI.SKRatio.Observation.observationMatrix`, `OAI.SKRatio.Observation.observedField`, `OAI.SKRatio.Observation.productPrior`, `OAI.SKRatio.Observation.productSiteEntropy`, `OAI.SKRatio.Observation.reweight`, `OAI.SKRatio.Observation.shiftedCoupling`, `OAI.SKRatio.Observation.var` and 16 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `SKRatio_Calculus_Expectation`, `SKRatio_Calculus_PairUpdate`, `SKRatio_Certificates_CertifiedBatches`, `SKRatio_Certificates_CertifiedInterpolation`, `SKRatio_Certificates_CertifiedJet`, `SKRatio_Certificates_CertifiedQuadrature`, `SKRatio_Entropy_AnnealedTransfer`, `SKRatio_Entropy_GaussianChannel`, `SKRatio_Entropy_GaussianHistory`, `SKRatio_Entropy_GibbsObservation`, `SKRatio_Entropy_ProductEntropy`, `SKRatio_FiniteChain_EntropicCovariance`, `SKRatio_Gaussian_GaussianEvents`, `SKRatio_Gaussian_PlantedCriterion`, `SKRatio_Matrices_AugmentedSquares`, `SKRatio_Matrices_PlantedSquares`, `SKRatio_Matrices_RowGeometry`, `SKRatio_Matrices_WeightedSquares`, `SKRatio_Variational_ScalarCoherent`, `SKRatio_Variational_ScalarInterpolation`, `SKRatio_Variational_ScalarReduction`, `SKRatio_Variational_UniformGap`.
--
--   **Imports.** It imports the published bundle `Def_SKRatio`; the bundles `OAIQ024S002`, `OAIQ024S003`, `OAIQ024S004`, `OAIQ024S005`, `OAIQ024S006`, `OAIQ024S007`, `OAIQ024S008`, `OAIQ024S009` and `OAIQ024S010` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.SKRatio.Certificate.Data.J0K1.checks`, `OAI.SKRatio.Certificate.Data.J0K3.check_35`, `OAI.SKRatio.Certificate.Data.J0K3.check_36`, `OAI.SKRatio.Certificate.Data.J0K3.check_37`, `OAI.SKRatio.Certificate.Data.J0K3.check_38`, `OAI.SKRatio.Certificate.Data.J0K3.check_39`, `OAI.SKRatio.Certificate.Data.J0K3.checks`, `OAI.SKRatio.Certificate.Data.J0K5.checks`, `OAI.SKRatio.Certificate.Data.J0K6.checks`, `OAI.SKRatio.Certificate.Data.J0K7.check_26`, `OAI.SKRatio.Certificate.Data.J0K7.check_27`, `OAI.SKRatio.Certificate.Data.J0K7.check_28`, `OAI.SKRatio.Certificate.Data.J0K7.check_29`, `OAI.SKRatio.Certificate.Data.J0K7.check_30`, `OAI.SKRatio.Certificate.Data.J0K7.check_31`, `OAI.SKRatio.Certificate.Data.J0K7.check_32`, `OAI.SKRatio.Certificate.Data.J0K7.check_33`, `OAI.SKRatio.Certificate.Data.J0K7.check_34`, `OAI.SKRatio.Certificate.Data.J0K7.check_35`, `OAI.SKRatio.Certificate.Data.J0K7.check_36`, `OAI.SKRatio.Certificate.Data.J0K7.check_37`, `OAI.SKRatio.Certificate.Data.J0K7.check_38`, `OAI.SKRatio.Certificate.Data.J0K7.check_39`, `OAI.SKRatio.Certificate.Data.J0K7.checks`, `OAI.SKRatio.Certificate.Data.J1K1.checks`, `OAI.SKRatio.Certificate.Data.J1K2.checks`, `OAI.SKRatio.Certificate.Data.J1K3.check_35`, `OAI.SKRatio.Certificate.Data.J1K3.check_36`, `OAI.SKRatio.Certificate.Data.J1K3.check_37`, `OAI.SKRatio.Certificate.Data.J1K3.check_38`, `OAI.SKRatio.Certificate.Data.J1K3.check_39`, `OAI.SKRatio.Certificate.Data.J1K3.checks`, `OAI.SKRatio.Certificate.Data.J1K5.checks`, `OAI.SKRatio.Certificate.Data.J1K6.checks`, `OAI.SKRatio.Certificate.Data.J1K7.check_27`, `OAI.SKRatio.Certificate.Data.J1K7.check_28`, `OAI.SKRatio.Certificate.Data.J1K7.check_29`, `OAI.SKRatio.Certificate.Data.J1K7.check_30`, `OAI.SKRatio.Certificate.Data.J1K7.check_31`, `OAI.SKRatio.Certificate.Data.J1K7.check_32`, `OAI.SKRatio.Certificate.Data.J1K7.check_33`, `OAI.SKRatio.Certificate.Data.J1K7.check_34`, `OAI.SKRatio.Certificate.Data.J1K7.check_35`, `OAI.SKRatio.Certificate.Data.J1K7.check_36`, `OAI.SKRatio.Certificate.Data.J1K7.check_37`, `OAI.SKRatio.Certificate.Data.J1K7.check_38`, `OAI.SKRatio.Certificate.Data.J1K7.check_39`, `OAI.SKRatio.Certificate.Data.J1K7.checks`, `OAI.SKRatio.Certificate.Data.J2K1.checks`, `OAI.SKRatio.Certificate.Data.J2K2.checks`, `OAI.SKRatio.Certificate.Data.J2K3.check_34`, `OAI.SKRatio.Certificate.Data.J2K3.check_35`, `OAI.SKRatio.Certificate.Data.J2K3.check_36`, `OAI.SKRatio.Certificate.Data.J2K3.check_37`, `OAI.SKRatio.Certificate.Data.J2K3.check_38`, `OAI.SKRatio.Certificate.Data.J2K3.check_39`, `OAI.SKRatio.Certificate.Data.J2K3.checks`, `OAI.SKRatio.Certificate.Data.J2K4.checks`, `OAI.SKRatio.Certificate.Data.J2K5.checks`, `OAI.SKRatio.Certificate.Data.J2K6.checks`, `OAI.SKRatio.Certificate.Data.J2K7.check_26`, `OAI.SKRatio.Certificate.Data.J2K7.check_27`, `OAI.SKRatio.Certificate.Data.J2K7.check_28`, `OAI.SKRatio.Certificate.Data.J2K7.check_29`, `OAI.SKRatio.Certificate.Data.J2K7.check_30`, `OAI.SKRatio.Certificate.Data.J2K7.check_31`, `OAI.SKRatio.Certificate.Data.J2K7.check_32`, `OAI.SKRatio.Certificate.Data.J2K7.check_33`, `OAI.SKRatio.Certificate.Data.J2K7.check_34`, `OAI.SKRatio.Certificate.Data.J2K7.check_35`, `OAI.SKRatio.Certificate.Data.J2K7.check_36`, `OAI.SKRatio.Certificate.Data.J2K7.check_37`, `OAI.SKRatio.Certificate.Data.J2K7.check_38`, `OAI.SKRatio.Certificate.Data.J2K7.check_39`, `OAI.SKRatio.Certificate.Data.J2K7.checks`, `OAI.SKRatio.Certificate.Data.J3K1.checks`, `OAI.SKRatio.Certificate.Data.J3K2.checks`, `OAI.SKRatio.Certificate.Data.J3K3.check_34`, `OAI.SKRatio.Certificate.Data.J3K3.check_35`, `OAI.SKRatio.Certificate.Data.J3K3.check_36`, `OAI.SKRatio.Certificate.Data.J3K3.check_37`, `OAI.SKRatio.Certificate.Data.J3K3.check_38`, `OAI.SKRatio.Certificate.Data.J3K3.check_39`, `OAI.SKRatio.Certificate.Data.J3K3.checks`, `OAI.SKRatio.Certificate.Data.J3K5.checks`, `OAI.SKRatio.Certificate.Data.J3K6.checks`, `OAI.SKRatio.Certificate.Data.J3K7.check_26`, `OAI.SKRatio.Certificate.Data.J3K7.check_27`, `OAI.SKRatio.Certificate.Data.J3K7.check_28`, `OAI.SKRatio.Certificate.Data.J3K7.check_29`, `OAI.SKRatio.Certificate.Data.J3K7.check_30`, `OAI.SKRatio.Certificate.Data.J3K7.check_31`, `OAI.SKRatio.Certificate.Data.J3K7.check_32`, `OAI.SKRatio.Certificate.Data.J3K7.check_33`, `OAI.SKRatio.Certificate.Data.J3K7.check_34`, `OAI.SKRatio.Certificate.Data.J3K7.check_35`, `OAI.SKRatio.Certificate.Data.J3K7.check_36`, `OAI.SKRatio.Certificate.Data.J3K7.check_37`, `OAI.SKRatio.Certificate.Data.J3K7.check_38`, `OAI.SKRatio.Certificate.Data.J3K7.check_39`, `OAI.SKRatio.Certificate.Data.J3K7.checks`, `OAI.SKRatio.Certificate.Data.J4K10.check_15`, `OAI.SKRatio.Certificate.Data.J4K10.check_16`, `OAI.SKRatio.Certificate.Data.J4K10.check_17`, `OAI.SKRatio.Certificate.Data.J4K10.check_18`, `OAI.SKRatio.Certificate.Data.J4K10.check_19`, `OAI.SKRatio.Certificate.Data.J4K10.check_20`, `OAI.SKRatio.Certificate.Data.J4K10.check_21`, `OAI.SKRatio.Certificate.Data.J4K10.check_22`, `OAI.SKRatio.Certificate.Data.J4K10.check_23`, `OAI.SKRatio.Certificate.Data.J4K10.check_24`, `OAI.SKRatio.Certificate.Data.J4K10.check_25`, `OAI.SKRatio.Certificate.Data.J4K10.check_26`, `OAI.SKRatio.Certificate.Data.J4K10.check_27`, `OAI.SKRatio.Certificate.Data.J4K10.check_28`, `OAI.SKRatio.Certificate.Data.J4K10.check_29`, `OAI.SKRatio.Certificate.Data.J4K10.check_30`, `OAI.SKRatio.Certificate.Data.J4K10.check_31`, `OAI.SKRatio.Certificate.Data.J4K10.check_32`, `OAI.SKRatio.Certificate.Data.J4K10.check_33`, `OAI.SKRatio.Certificate.Data.J4K10.check_34`, `OAI.SKRatio.Certificate.Data.J4K10.check_35`, `OAI.SKRatio.Certificate.Data.J4K10.check_36`, `OAI.SKRatio.Certificate.Data.J4K10.check_37`, `OAI.SKRatio.Certificate.Data.J4K10.check_38`, `OAI.SKRatio.Certificate.Data.J4K10.check_39`, `OAI.SKRatio.Certificate.Data.J4K10.checks`, `OAI.SKRatio.Certificate.Data.J4K11.check_14`, `OAI.SKRatio.Certificate.Data.J4K11.check_15`, `OAI.SKRatio.Certificate.Data.J4K11.check_16`, `OAI.SKRatio.Certificate.Data.J4K11.check_17`, `OAI.SKRatio.Certificate.Data.J4K11.check_18`, `OAI.SKRatio.Certificate.Data.J4K11.check_19`, `OAI.SKRatio.Certificate.Data.J4K11.check_20`, `OAI.SKRatio.Certificate.Data.J4K11.check_21`, `OAI.SKRatio.Certificate.Data.J4K11.check_22`, `OAI.SKRatio.Certificate.Data.J4K11.check_23`, `OAI.SKRatio.Certificate.Data.J4K11.check_24`, `OAI.SKRatio.Certificate.Data.J4K11.check_25`, `OAI.SKRatio.Certificate.Data.J4K11.check_26`, `OAI.SKRatio.Certificate.Data.J4K11.check_27`, `OAI.SKRatio.Certificate.Data.J4K11.check_28`, `OAI.SKRatio.Certificate.Data.J4K11.check_29`, `OAI.SKRatio.Certificate.Data.J4K11.check_30`, `OAI.SKRatio.Certificate.Data.J4K11.check_31`, `OAI.SKRatio.Certificate.Data.J4K11.check_32`, `OAI.SKRatio.Certificate.Data.J4K11.check_33`, `OAI.SKRatio.Certificate.Data.J4K11.check_34`, `OAI.SKRatio.Certificate.Data.J4K11.check_35`, `OAI.SKRatio.Certificate.Data.J4K11.check_36`, `OAI.SKRatio.Certificate.Data.J4K11.check_37`, `OAI.SKRatio.Certificate.Data.J4K11.check_38`, `OAI.SKRatio.Certificate.Data.J4K11.check_39`, `OAI.SKRatio.Certificate.Data.J4K11.checks`, `OAI.SKRatio.Certificate.Data.J4K12.check_22`, `OAI.SKRatio.Certificate.Data.J4K12.check_23`, `OAI.SKRatio.Certificate.Data.J4K12.check_24`, `OAI.SKRatio.Certificate.Data.J4K12.check_25`, `OAI.SKRatio.Certificate.Data.J4K12.check_26`, `OAI.SKRatio.Certificate.Data.J4K12.check_27`, `OAI.SKRatio.Certificate.Data.J4K12.check_28`, `OAI.SKRatio.Certificate.Data.J4K12.check_29`, `OAI.SKRatio.Certificate.Data.J4K12.check_30`, `OAI.SKRatio.Certificate.Data.J4K12.check_31`, `OAI.SKRatio.Certificate.Data.J4K12.check_32`, `OAI.SKRatio.Certificate.Data.J4K12.check_33`, `OAI.SKRatio.Certificate.Data.J4K12.check_34`, `OAI.SKRatio.Certificate.Data.J4K12.check_35`, `OAI.SKRatio.Certificate.Data.J4K12.check_36`, `OAI.SKRatio.Certificate.Data.J4K12.check_37`, `OAI.SKRatio.Certificate.Data.J4K12.check_38`, `OAI.SKRatio.Certificate.Data.J4K12.check_39`, `OAI.SKRatio.Certificate.Data.J4K12.checks`, `OAI.SKRatio.Certificate.Data.J4K1.checks`, `OAI.SKRatio.Certificate.Data.J4K2.checks`, `OAI.SKRatio.Certificate.Data.J4K3.check_33`, `OAI.SKRatio.Certificate.Data.J4K3.check_34`, `OAI.SKRatio.Certificate.Data.J4K3.check_35`, `OAI.SKRatio.Certificate.Data.J4K3.check_36`, `OAI.SKRatio.Certificate.Data.J4K3.check_37`, `OAI.SKRatio.Certificate.Data.J4K3.check_38`, `OAI.SKRatio.Certificate.Data.J4K3.check_39`, `OAI.SKRatio.Certificate.Data.J4K3.checks`, `OAI.SKRatio.Certificate.Data.J4K4.checks`, `OAI.SKRatio.Certificate.Data.J4K5.checks`, `OAI.SKRatio.Certificate.Data.J4K6.checks`, `OAI.SKRatio.Certificate.Data.J4K7.check_26`, `OAI.SKRatio.Certificate.Data.J4K7.check_27`, `OAI.SKRatio.Certificate.Data.J4K7.check_28`, `OAI.SKRatio.Certificate.Data.J4K7.check_29`, `OAI.SKRatio.Certificate.Data.J4K7.check_30`, `OAI.SKRatio.Certificate.Data.J4K7.check_31`, `OAI.SKRatio.Certificate.Data.J4K7.check_32`, `OAI.SKRatio.Certificate.Data.J4K7.check_33`, `OAI.SKRatio.Certificate.Data.J4K7.check_34`, `OAI.SKRatio.Certificate.Data.J4K7.check_35`, `OAI.SKRatio.Certificate.Data.J4K7.check_36`, `OAI.SKRatio.Certificate.Data.J4K7.check_37`, `OAI.SKRatio.Certificate.Data.J4K7.check_38`, `OAI.SKRatio.Certificate.Data.J4K7.check_39`, `OAI.SKRatio.Certificate.Data.J4K7.checks`, `OAI.SKRatio.Certificate.Data.J4K8.check_12`, `OAI.SKRatio.Certificate.Data.J4K8.check_13`, `OAI.SKRatio.Certificate.Data.J4K8.check_14`, `OAI.SKRatio.Certificate.Data.J4K8.check_15`, `OAI.SKRatio.Certificate.Data.J4K8.check_16`, `OAI.SKRatio.Certificate.Data.J4K8.check_17`, `OAI.SKRatio.Certificate.Data.J4K8.check_18`, `OAI.SKRatio.Certificate.Data.J4K8.check_19`, `OAI.SKRatio.Certificate.Data.J4K8.check_20`, `OAI.SKRatio.Certificate.Data.J4K8.check_21`, `OAI.SKRatio.Certificate.Data.J4K8.check_22`, `OAI.SKRatio.Certificate.Data.J4K8.check_23`, `OAI.SKRatio.Certificate.Data.J4K8.check_24`, `OAI.SKRatio.Certificate.Data.J4K8.check_25`, `OAI.SKRatio.Certificate.Data.J4K8.check_26`, `OAI.SKRatio.Certificate.Data.J4K8.check_27`, `OAI.SKRatio.Certificate.Data.J4K8.check_28`, `OAI.SKRatio.Certificate.Data.J4K8.check_29`, `OAI.SKRatio.Certificate.Data.J4K8.check_30`, `OAI.SKRatio.Certificate.Data.J4K8.check_31`, `OAI.SKRatio.Certificate.Data.J4K8.check_32`, `OAI.SKRatio.Certificate.Data.J4K8.check_33`, `OAI.SKRatio.Certificate.Data.J4K8.check_34`, `OAI.SKRatio.Certificate.Data.J4K8.check_35`, `OAI.SKRatio.Certificate.Data.J4K8.check_36`, `OAI.SKRatio.Certificate.Data.J4K8.check_37`, `OAI.SKRatio.Certificate.Data.J4K8.check_38`, `OAI.SKRatio.Certificate.Data.J4K8.check_39`, `OAI.SKRatio.Certificate.Data.J4K8.checks`, `OAI.SKRatio.Certificate.Data.J4K9.check_12`, `OAI.SKRatio.Certificate.Data.J4K9.check_13`, `OAI.SKRatio.Certificate.Data.J4K9.check_14`, `OAI.SKRatio.Certificate.Data.J4K9.check_15`, `OAI.SKRatio.Certificate.Data.J4K9.check_16`, `OAI.SKRatio.Certificate.Data.J4K9.check_17`, `OAI.SKRatio.Certificate.Data.J4K9.check_18`, `OAI.SKRatio.Certificate.Data.J4K9.check_19`, `OAI.SKRatio.Certificate.Data.J4K9.check_20`, `OAI.SKRatio.Certificate.Data.J4K9.check_21`, `OAI.SKRatio.Certificate.Data.J4K9.check_22`, `OAI.SKRatio.Certificate.Data.J4K9.check_23`, `OAI.SKRatio.Certificate.Data.J4K9.check_24`, `OAI.SKRatio.Certificate.Data.J4K9.check_25`, `OAI.SKRatio.Certificate.Data.J4K9.check_26`, `OAI.SKRatio.Certificate.Data.J4K9.check_27`, `OAI.SKRatio.Certificate.Data.J4K9.check_28`, `OAI.SKRatio.Certificate.Data.J4K9.check_29`, `OAI.SKRatio.Certificate.Data.J4K9.check_30`, `OAI.SKRatio.Certificate.Data.J4K9.check_31`, `OAI.SKRatio.Certificate.Data.J4K9.check_32`, `OAI.SKRatio.Certificate.Data.J4K9.check_33`, `OAI.SKRatio.Certificate.Data.J4K9.check_34`, `OAI.SKRatio.Certificate.Data.J4K9.check_35`, `OAI.SKRatio.Certificate.Data.J4K9.check_36`, `OAI.SKRatio.Certificate.Data.J4K9.check_37`, `OAI.SKRatio.Certificate.Data.J4K9.check_38`, `OAI.SKRatio.Certificate.Data.J4K9.check_39`, `OAI.SKRatio.Certificate.Data.J4K9.checks`, `OAI.SKRatio.Certificate.uniform_slacks`, `OAI.SKRatio.Certificate.valid0`, `OAI.SKRatio.Certificate.valid1`, `OAI.SKRatio.Certificate.valid2`, `OAI.SKRatio.Certificate.valid4`, `OAI.SKRatio.Gaussian.matrixGood_probability`, `OAI.SKRatio.Planted.ratio_cutoff_of_planted_form` and `OAI.SKRatio.Planted.ratio_cutoff_of_scalar`; the proofs of `OAI.SKRatio.Certificate.Data.J0K0.integral_bound`, `OAI.SKRatio.Certificate.Data.J0K1.checks`, `OAI.SKRatio.Certificate.Data.J0K2.integral_bound`, `OAI.SKRatio.Certificate.Data.J0K3.check_35`, `OAI.SKRatio.Certificate.Data.J0K3.check_36`, `OAI.SKRatio.Certificate.Data.J0K3.check_37`, `OAI.SKRatio.Certificate.Data.J0K3.check_38`, `OAI.SKRatio.Certificate.Data.J0K3.check_39`, `OAI.SKRatio.Certificate.Data.J0K3.checks`, `OAI.SKRatio.Certificate.Data.J0K4.integral_bound`, `OAI.SKRatio.Certificate.Data.J0K5.checks`, `OAI.SKRatio.Certificate.Data.J0K6.checks`, `OAI.SKRatio.Certificate.Data.J0K7.check_26`, `OAI.SKRatio.Certificate.Data.J0K7.check_27`, `OAI.SKRatio.Certificate.Data.J0K7.check_28`, `OAI.SKRatio.Certificate.Data.J0K7.check_29`, `OAI.SKRatio.Certificate.Data.J0K7.check_30`, `OAI.SKRatio.Certificate.Data.J0K7.check_31`, `OAI.SKRatio.Certificate.Data.J0K7.check_32`, `OAI.SKRatio.Certificate.Data.J0K7.check_33`, `OAI.SKRatio.Certificate.Data.J0K7.check_34`, `OAI.SKRatio.Certificate.Data.J0K7.check_35`, `OAI.SKRatio.Certificate.Data.J0K7.check_36`, `OAI.SKRatio.Certificate.Data.J0K7.check_37`, `OAI.SKRatio.Certificate.Data.J0K7.check_38`, `OAI.SKRatio.Certificate.Data.J0K7.check_39`, `OAI.SKRatio.Certificate.Data.J0K7.checks`, `OAI.SKRatio.Certificate.Data.J1K0.integral_bound`, `OAI.SKRatio.Certificate.Data.J1K1.checks`, `OAI.SKRatio.Certificate.Data.J1K2.checks`, `OAI.SKRatio.Certificate.Data.J1K3.check_35`, `OAI.SKRatio.Certificate.Data.J1K3.check_36`, `OAI.SKRatio.Certificate.Data.J1K3.check_37`, `OAI.SKRatio.Certificate.Data.J1K3.check_38`, `OAI.SKRatio.Certificate.Data.J1K3.check_39`, `OAI.SKRatio.Certificate.Data.J1K3.checks`, `OAI.SKRatio.Certificate.Data.J1K4.integral_bound`, `OAI.SKRatio.Certificate.Data.J1K5.checks`, `OAI.SKRatio.Certificate.Data.J1K6.checks`, `OAI.SKRatio.Certificate.Data.J1K7.check_27`, `OAI.SKRatio.Certificate.Data.J1K7.check_28`, `OAI.SKRatio.Certificate.Data.J1K7.check_29`, `OAI.SKRatio.Certificate.Data.J1K7.check_30`, `OAI.SKRatio.Certificate.Data.J1K7.check_31`, `OAI.SKRatio.Certificate.Data.J1K7.check_32`, `OAI.SKRatio.Certificate.Data.J1K7.check_33`, `OAI.SKRatio.Certificate.Data.J1K7.check_34`, `OAI.SKRatio.Certificate.Data.J1K7.check_35`, `OAI.SKRatio.Certificate.Data.J1K7.check_36`, `OAI.SKRatio.Certificate.Data.J1K7.check_37`, `OAI.SKRatio.Certificate.Data.J1K7.check_38`, `OAI.SKRatio.Certificate.Data.J1K7.check_39`, `OAI.SKRatio.Certificate.Data.J1K7.checks`, `OAI.SKRatio.Certificate.Data.J2K0.integral_bound`, `OAI.SKRatio.Certificate.Data.J2K1.checks`, `OAI.SKRatio.Certificate.Data.J2K2.checks`, `OAI.SKRatio.Certificate.Data.J2K3.check_34`, `OAI.SKRatio.Certificate.Data.J2K3.check_35`, `OAI.SKRatio.Certificate.Data.J2K3.check_36`, `OAI.SKRatio.Certificate.Data.J2K3.check_37`, `OAI.SKRatio.Certificate.Data.J2K3.check_38`, `OAI.SKRatio.Certificate.Data.J2K3.check_39`, `OAI.SKRatio.Certificate.Data.J2K3.checks`, `OAI.SKRatio.Certificate.Data.J2K4.checks`, `OAI.SKRatio.Certificate.Data.J2K5.checks`, `OAI.SKRatio.Certificate.Data.J2K6.checks`, `OAI.SKRatio.Certificate.Data.J2K7.check_26`, `OAI.SKRatio.Certificate.Data.J2K7.check_27`, `OAI.SKRatio.Certificate.Data.J2K7.check_28`, `OAI.SKRatio.Certificate.Data.J2K7.check_29`, `OAI.SKRatio.Certificate.Data.J2K7.check_30`, `OAI.SKRatio.Certificate.Data.J2K7.check_31`, `OAI.SKRatio.Certificate.Data.J2K7.check_32`, `OAI.SKRatio.Certificate.Data.J2K7.check_33`, `OAI.SKRatio.Certificate.Data.J2K7.check_34`, `OAI.SKRatio.Certificate.Data.J2K7.check_35`, `OAI.SKRatio.Certificate.Data.J2K7.check_36`, `OAI.SKRatio.Certificate.Data.J2K7.check_37`, `OAI.SKRatio.Certificate.Data.J2K7.check_38`, `OAI.SKRatio.Certificate.Data.J2K7.check_39`, `OAI.SKRatio.Certificate.Data.J2K7.checks`, `OAI.SKRatio.Certificate.Data.J2K7.integral_bound`, `OAI.SKRatio.Certificate.Data.J3K0.integral_bound`, `OAI.SKRatio.Certificate.Data.J3K1.checks`, `OAI.SKRatio.Certificate.Data.J3K2.checks`, `OAI.SKRatio.Certificate.Data.J3K3.check_34`, `OAI.SKRatio.Certificate.Data.J3K3.check_35`, `OAI.SKRatio.Certificate.Data.J3K3.check_36`, `OAI.SKRatio.Certificate.Data.J3K3.check_37`, `OAI.SKRatio.Certificate.Data.J3K3.check_38`, `OAI.SKRatio.Certificate.Data.J3K3.check_39`, `OAI.SKRatio.Certificate.Data.J3K3.checks`, `OAI.SKRatio.Certificate.Data.J3K4.integral_bound`, `OAI.SKRatio.Certificate.Data.J3K5.checks`, `OAI.SKRatio.Certificate.Data.J3K6.checks`, `OAI.SKRatio.Certificate.Data.J3K7.check_26`, `OAI.SKRatio.Certificate.Data.J3K7.check_27`, `OAI.SKRatio.Certificate.Data.J3K7.check_28`, `OAI.SKRatio.Certificate.Data.J3K7.check_29`, `OAI.SKRatio.Certificate.Data.J3K7.check_30`, `OAI.SKRatio.Certificate.Data.J3K7.check_31`, `OAI.SKRatio.Certificate.Data.J3K7.check_32`, `OAI.SKRatio.Certificate.Data.J3K7.check_33`, `OAI.SKRatio.Certificate.Data.J3K7.check_34`, `OAI.SKRatio.Certificate.Data.J3K7.check_35`, `OAI.SKRatio.Certificate.Data.J3K7.check_36`, `OAI.SKRatio.Certificate.Data.J3K7.check_37`, `OAI.SKRatio.Certificate.Data.J3K7.check_38`, `OAI.SKRatio.Certificate.Data.J3K7.check_39`, `OAI.SKRatio.Certificate.Data.J3K7.checks`, `OAI.SKRatio.Certificate.Data.J3K7.integral_bound`, `OAI.SKRatio.Certificate.Data.J4K0.integral_bound`, `OAI.SKRatio.Certificate.Data.J4K10.check_15`, `OAI.SKRatio.Certificate.Data.J4K10.check_16`, `OAI.SKRatio.Certificate.Data.J4K10.check_17`, `OAI.SKRatio.Certificate.Data.J4K10.check_18`, `OAI.SKRatio.Certificate.Data.J4K10.check_19`, `OAI.SKRatio.Certificate.Data.J4K10.check_20`, `OAI.SKRatio.Certificate.Data.J4K10.check_21`, `OAI.SKRatio.Certificate.Data.J4K10.check_22`, `OAI.SKRatio.Certificate.Data.J4K10.check_23`, `OAI.SKRatio.Certificate.Data.J4K10.check_24`, `OAI.SKRatio.Certificate.Data.J4K10.check_25`, `OAI.SKRatio.Certificate.Data.J4K10.check_26`, `OAI.SKRatio.Certificate.Data.J4K10.check_27`, `OAI.SKRatio.Certificate.Data.J4K10.check_28`, `OAI.SKRatio.Certificate.Data.J4K10.check_29`, `OAI.SKRatio.Certificate.Data.J4K10.check_30`, `OAI.SKRatio.Certificate.Data.J4K10.check_31`, `OAI.SKRatio.Certificate.Data.J4K10.check_32`, `OAI.SKRatio.Certificate.Data.J4K10.check_33`, `OAI.SKRatio.Certificate.Data.J4K10.check_34`, `OAI.SKRatio.Certificate.Data.J4K10.check_35`, `OAI.SKRatio.Certificate.Data.J4K10.check_36`, `OAI.SKRatio.Certificate.Data.J4K10.check_37`, `OAI.SKRatio.Certificate.Data.J4K10.check_38`, `OAI.SKRatio.Certificate.Data.J4K10.check_39`, `OAI.SKRatio.Certificate.Data.J4K10.checks`, `OAI.SKRatio.Certificate.Data.J4K11.check_14`, `OAI.SKRatio.Certificate.Data.J4K11.check_15`, `OAI.SKRatio.Certificate.Data.J4K11.check_16`, `OAI.SKRatio.Certificate.Data.J4K11.check_17`, `OAI.SKRatio.Certificate.Data.J4K11.check_18`, `OAI.SKRatio.Certificate.Data.J4K11.check_19`, `OAI.SKRatio.Certificate.Data.J4K11.check_20`, `OAI.SKRatio.Certificate.Data.J4K11.check_21`, `OAI.SKRatio.Certificate.Data.J4K11.check_22`, `OAI.SKRatio.Certificate.Data.J4K11.check_23`, `OAI.SKRatio.Certificate.Data.J4K11.check_24`, `OAI.SKRatio.Certificate.Data.J4K11.check_25`, `OAI.SKRatio.Certificate.Data.J4K11.check_26`, `OAI.SKRatio.Certificate.Data.J4K11.check_27`, `OAI.SKRatio.Certificate.Data.J4K11.check_28`, `OAI.SKRatio.Certificate.Data.J4K11.check_29`, `OAI.SKRatio.Certificate.Data.J4K11.check_30`, `OAI.SKRatio.Certificate.Data.J4K11.check_31`, `OAI.SKRatio.Certificate.Data.J4K11.check_32`, `OAI.SKRatio.Certificate.Data.J4K11.check_33`, `OAI.SKRatio.Certificate.Data.J4K11.check_34`, `OAI.SKRatio.Certificate.Data.J4K11.check_35`, `OAI.SKRatio.Certificate.Data.J4K11.check_36`, `OAI.SKRatio.Certificate.Data.J4K11.check_37`, `OAI.SKRatio.Certificate.Data.J4K11.check_38`, `OAI.SKRatio.Certificate.Data.J4K11.check_39`, `OAI.SKRatio.Certificate.Data.J4K11.checks`, `OAI.SKRatio.Certificate.Data.J4K12.check_22`, `OAI.SKRatio.Certificate.Data.J4K12.check_23`, `OAI.SKRatio.Certificate.Data.J4K12.check_24`, `OAI.SKRatio.Certificate.Data.J4K12.check_25`, `OAI.SKRatio.Certificate.Data.J4K12.check_26`, `OAI.SKRatio.Certificate.Data.J4K12.check_27`, `OAI.SKRatio.Certificate.Data.J4K12.check_28`, `OAI.SKRatio.Certificate.Data.J4K12.check_29`, `OAI.SKRatio.Certificate.Data.J4K12.check_30`, `OAI.SKRatio.Certificate.Data.J4K12.check_31`, `OAI.SKRatio.Certificate.Data.J4K12.check_32`, `OAI.SKRatio.Certificate.Data.J4K12.check_33`, `OAI.SKRatio.Certificate.Data.J4K12.check_34`, `OAI.SKRatio.Certificate.Data.J4K12.check_35`, `OAI.SKRatio.Certificate.Data.J4K12.check_36`, `OAI.SKRatio.Certificate.Data.J4K12.check_37`, `OAI.SKRatio.Certificate.Data.J4K12.check_38`, `OAI.SKRatio.Certificate.Data.J4K12.check_39`, `OAI.SKRatio.Certificate.Data.J4K12.checks`, `OAI.SKRatio.Certificate.Data.J4K1.checks`, `OAI.SKRatio.Certificate.Data.J4K2.checks`, `OAI.SKRatio.Certificate.Data.J4K3.check_33`, `OAI.SKRatio.Certificate.Data.J4K3.check_34`, `OAI.SKRatio.Certificate.Data.J4K3.check_35`, `OAI.SKRatio.Certificate.Data.J4K3.check_36`, `OAI.SKRatio.Certificate.Data.J4K3.check_37`, `OAI.SKRatio.Certificate.Data.J4K3.check_38`, `OAI.SKRatio.Certificate.Data.J4K3.check_39`, `OAI.SKRatio.Certificate.Data.J4K3.checks`, `OAI.SKRatio.Certificate.Data.J4K4.checks`, `OAI.SKRatio.Certificate.Data.J4K5.checks`, `OAI.SKRatio.Certificate.Data.J4K6.checks`, `OAI.SKRatio.Certificate.Data.J4K7.check_26`, `OAI.SKRatio.Certificate.Data.J4K7.check_27`, `OAI.SKRatio.Certificate.Data.J4K7.check_28`, `OAI.SKRatio.Certificate.Data.J4K7.check_29`, `OAI.SKRatio.Certificate.Data.J4K7.check_30`, `OAI.SKRatio.Certificate.Data.J4K7.check_31`, `OAI.SKRatio.Certificate.Data.J4K7.check_32`, `OAI.SKRatio.Certificate.Data.J4K7.check_33`, `OAI.SKRatio.Certificate.Data.J4K7.check_34`, `OAI.SKRatio.Certificate.Data.J4K7.check_35`, `OAI.SKRatio.Certificate.Data.J4K7.check_36`, `OAI.SKRatio.Certificate.Data.J4K7.check_37`, `OAI.SKRatio.Certificate.Data.J4K7.check_38`, `OAI.SKRatio.Certificate.Data.J4K7.check_39`, `OAI.SKRatio.Certificate.Data.J4K7.checks`, `OAI.SKRatio.Certificate.Data.J4K7.integral_bound`, `OAI.SKRatio.Certificate.Data.J4K8.check_12`, `OAI.SKRatio.Certificate.Data.J4K8.check_13`, `OAI.SKRatio.Certificate.Data.J4K8.check_14`, `OAI.SKRatio.Certificate.Data.J4K8.check_15`, `OAI.SKRatio.Certificate.Data.J4K8.check_16`, `OAI.SKRatio.Certificate.Data.J4K8.check_17`, `OAI.SKRatio.Certificate.Data.J4K8.check_18`, `OAI.SKRatio.Certificate.Data.J4K8.check_19`, `OAI.SKRatio.Certificate.Data.J4K8.check_20`, `OAI.SKRatio.Certificate.Data.J4K8.check_21`, `OAI.SKRatio.Certificate.Data.J4K8.check_22`, `OAI.SKRatio.Certificate.Data.J4K8.check_23`, `OAI.SKRatio.Certificate.Data.J4K8.check_24`, `OAI.SKRatio.Certificate.Data.J4K8.check_25`, `OAI.SKRatio.Certificate.Data.J4K8.check_26`, `OAI.SKRatio.Certificate.Data.J4K8.check_27`, `OAI.SKRatio.Certificate.Data.J4K8.check_28`, `OAI.SKRatio.Certificate.Data.J4K8.check_29`, `OAI.SKRatio.Certificate.Data.J4K8.check_30`, `OAI.SKRatio.Certificate.Data.J4K8.check_31`, `OAI.SKRatio.Certificate.Data.J4K8.check_32`, `OAI.SKRatio.Certificate.Data.J4K8.check_33`, `OAI.SKRatio.Certificate.Data.J4K8.check_34`, `OAI.SKRatio.Certificate.Data.J4K8.check_35`, `OAI.SKRatio.Certificate.Data.J4K8.check_36`, `OAI.SKRatio.Certificate.Data.J4K8.check_37`, `OAI.SKRatio.Certificate.Data.J4K8.check_38`, `OAI.SKRatio.Certificate.Data.J4K8.check_39`, `OAI.SKRatio.Certificate.Data.J4K8.checks`, `OAI.SKRatio.Certificate.Data.J4K9.check_12`, `OAI.SKRatio.Certificate.Data.J4K9.check_13`, `OAI.SKRatio.Certificate.Data.J4K9.check_14`, `OAI.SKRatio.Certificate.Data.J4K9.check_15`, `OAI.SKRatio.Certificate.Data.J4K9.check_16`, `OAI.SKRatio.Certificate.Data.J4K9.check_17`, `OAI.SKRatio.Certificate.Data.J4K9.check_18`, `OAI.SKRatio.Certificate.Data.J4K9.check_19`, `OAI.SKRatio.Certificate.Data.J4K9.check_20`, `OAI.SKRatio.Certificate.Data.J4K9.check_21`, `OAI.SKRatio.Certificate.Data.J4K9.check_22`, `OAI.SKRatio.Certificate.Data.J4K9.check_23`, `OAI.SKRatio.Certificate.Data.J4K9.check_24`, `OAI.SKRatio.Certificate.Data.J4K9.check_25`, `OAI.SKRatio.Certificate.Data.J4K9.check_26`, `OAI.SKRatio.Certificate.Data.J4K9.check_27`, `OAI.SKRatio.Certificate.Data.J4K9.check_28`, `OAI.SKRatio.Certificate.Data.J4K9.check_29`, `OAI.SKRatio.Certificate.Data.J4K9.check_30`, `OAI.SKRatio.Certificate.Data.J4K9.check_31`, `OAI.SKRatio.Certificate.Data.J4K9.check_32`, `OAI.SKRatio.Certificate.Data.J4K9.check_33`, `OAI.SKRatio.Certificate.Data.J4K9.check_34`, `OAI.SKRatio.Certificate.Data.J4K9.check_35`, `OAI.SKRatio.Certificate.Data.J4K9.check_36`, `OAI.SKRatio.Certificate.Data.J4K9.check_37`, `OAI.SKRatio.Certificate.Data.J4K9.check_38`, `OAI.SKRatio.Certificate.Data.J4K9.check_39`, `OAI.SKRatio.Certificate.Data.J4K9.checks`, `OAI.SKRatio.Certificate.diagonal_envelope`, `OAI.SKRatio.Certificate.endpointD_prime_lower`, `OAI.SKRatio.Certificate.endpointD_prime_upper`, `OAI.SKRatio.Certificate.endpointK_one_bound`, `OAI.SKRatio.Certificate.endpointK_zero_bound`, `OAI.SKRatio.Certificate.uniform_slacks`, `OAI.SKRatio.Certificate.valid0`, `OAI.SKRatio.Certificate.valid1`, `OAI.SKRatio.Certificate.valid2`, `OAI.SKRatio.Certificate.valid4`, `OAI.SKRatio.Gaussian.matrixGood_probability`, `OAI.SKRatio.Planted.ratio_cutoff_of_planted_form`, `OAI.SKRatio.Planted.ratio_cutoff_of_scalar`, `OAI.SKRatio.Planted.reduced_error_rare` and `OAI.SKRatio.ratio_cutoff`.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_SKRatio
import Definitions.Def_OAIQ024S002
import Definitions.Def_OAIQ024S003
import Definitions.Def_OAIQ024S004
import Definitions.Def_OAIQ024S005
import Definitions.Def_OAIQ024S006
import Definitions.Def_OAIQ024S007
import Definitions.Def_OAIQ024S008
import Definitions.Def_OAIQ024S009
import Definitions.Def_OAIQ024S010

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_Expectation
attribute [-instance] _root_.OAI.SKRatio.Planted.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace SKRatio.Fields
open Real Matrix TwoSpin
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def variance {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) : ℝ :=
  expectation g h (fun x => (f x - expectation g h f) ^ 2)

def heatBathGenerator (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) (x : Spin n) : ℝ :=
  ∑ i,(f x-conditionalExpectation g h i f x)

def localField (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) : ℝ :=
  h i+∑ k,coupling g i k*spinValue (x k)
def spinGradient (i : Fin n) (f : Spin n→ℝ) (x : Spin n) : ℝ :=
  (f (Function.update x i true)-f (Function.update x i false))/2

def realSpinEnergy (g : Disorder n) (h v : Fin n→ℝ) : ℝ :=
  (1/2)*(v ⬝ᵥ (Matrix.of (coupling g) *ᵥ v))+h ⬝ᵥ v

end SKRatio.Fields
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_PairUpdate
attribute [-instance] _root_.OAI.SKRatio.Planted.law_probability
attribute [-simp] _root_.OAI.SKRatio.Calculus.abs_signConjugate _root_.OAI.SKRatio.Calculus.abs_spin _root_.OAI.SKRatio.Calculus.attempt_const _root_.OAI.SKRatio.Calculus.attempt_pow_const _root_.OAI.SKRatio.Calculus.continuousDistance_zero _root_.OAI.SKRatio.Calculus.continuousKernel_zero _root_.OAI.SKRatio.Calculus.field_reversal _root_.OAI.SKRatio.Calculus.generator_const _root_.OAI.SKRatio.Calculus.gibbsEuclideanEquiv_apply _root_.OAI.SKRatio.Calculus.gibbsMeanCLM_apply _root_.OAI.SKRatio.Calculus.halfDiff_const _root_.OAI.SKRatio.Calculus.halfDiff_replace _root_.OAI.SKRatio.Calculus.halfDiff_self _root_.OAI.SKRatio.Calculus.halfDiff_spin _root_.OAI.SKRatio.Calculus.lift_scalarEigenfunction _root_.OAI.SKRatio.Calculus.mass_reversal _root_.OAI.SKRatio.Calculus.norm_signedVector _root_.OAI.SKRatio.Calculus.plus_signProduct _root_.OAI.SKRatio.Calculus.replace_replace _root_.OAI.SKRatio.Calculus.replace_same _root_.OAI.SKRatio.Calculus.replace_self _root_.OAI.SKRatio.Calculus.reversal_reversal _root_.OAI.SKRatio.Calculus.semigroup_zero _root_.OAI.SKRatio.Calculus.signConjugate_twice _root_.OAI.SKRatio.Calculus.signProduct_plus _root_.OAI.SKRatio.Calculus.siteRefresh_const _root_.OAI.SKRatio.Calculus.spin_reversal _root_.OAI.SKRatio.Calculus.spin_sq _root_.OAI.SKRatio.Calculus.stationaryPairingCLM_apply _root_.OAI.SKRatio.Independent.coupling_zero _root_.OAI.SKRatio.Independent.mass_zero _root_.OAI.SKRatio.Independent.siteKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace SKRatio.Fields
open Real Matrix TwoSpin
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def pairConditionalMean (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n)
    (F : Spin n→ℝ) (x : Spin n) : ℝ :=
  (∑ a : Bool,∑ b : Bool,weight g h (pairUpdate i j x a b)*F (pairUpdate i j x a b))/
    (∑ a : Bool,∑ b : Bool,weight g h (pairUpdate i j x a b))

def siteVariance (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) : ℝ :=
  1-tanh (localField g h i x)^2

def heatBathLinear (g : Disorder n) (h : Fin n→ℝ) : (Spin n→ℝ) →ₗ[ℝ] (Spin n→ℝ) where
  toFun := heatBathGenerator g h
  map_add' f k := by
    funext x
    simp only [heatBathGenerator,conditionalExpectation_add,Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _;ring
  map_smul' c f := by
    funext x
    simp only [heatBathGenerator,conditionalExpectation_smul,Pi.smul_apply,smul_eq_mul,
      RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _;ring

def gibbsScale (g : Disorder n) (h : Fin n→ℝ) : (Spin n→ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Spin n) where
  toFun f := WithLp.toLp 2 (fun x=>sqrt (mass g h x)*f x)
  invFun v := fun x=>v x/sqrt (mass g h x)
  left_inv f := by
    funext x
    change sqrt (mass g h x)*f x/sqrt (mass g h x)=f x
    exact mul_div_cancel_left₀ (f x) (sqrt_pos.mpr (mass_pos g h x)).ne'
  right_inv v := by
    ext x
    exact mul_div_cancel₀ (v x) (sqrt_pos.mpr (mass_pos g h x)).ne'
  map_add' f k := by ext x;simp [mul_add]
  map_smul' c f := by ext x;simp [mul_left_comm]

end SKRatio.Fields
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedJet
attribute [-instance] _root_.OAI.SKRatio.Certificate.Expr.instAdd _root_.OAI.SKRatio.Certificate.Expr.instDiv _root_.OAI.SKRatio.Certificate.Expr.instMul _root_.OAI.SKRatio.Certificate.Expr.instNeg _root_.OAI.SKRatio.Certificate.Expr.instOfNat _root_.OAI.SKRatio.Certificate.Expr.instSub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real
namespace SKRatio.Certificate

namespace Expr

def sec (e : Expr) (x : ℝ) : ℝ := match e with
  | rat _ => 0
  | var => 0
  | add a b => a.sec x+b.sec x
  | neg a => -a.sec x
  | mul a b => a.sec x*b.val x+2*a.der x*b.der x+a.val x*b.sec x
  | sq a => 2*(a.der x^2+a.val x*a.sec x)
  | inv a => 2*a.der x^2*((a.val x)⁻¹)^3-a.sec x*((a.val x)⁻¹)^2
  | exp a => Real.exp (a.val x)*(a.sec x+a.der x^2)
  | tanh a => (1-(Real.tanh (a.val x))^2)*a.sec x-
      2*Real.tanh (a.val x)*(1-(Real.tanh (a.val x))^2)*a.der x^2

def compute (e : Expr) (B : Box) : Option Jet := match e with
  | rat q => some (Jet.rat q)
  | var => some (Jet.var B)
  | add a b => do let A ← a.compute B; let C ← b.compute B; return Jet.add A C
  | neg a => do let A ← a.compute B; return Jet.neg A
  | mul a b => do let A ← a.compute B; let C ← b.compute B; return Jet.mul A C
  | sq a => do let A ← a.compute B; return Jet.sq A
  | inv a => do let A ← a.compute B; Jet.inv A
  | exp a => do let A ← a.compute B; Jet.exp A
  | tanh a => do let A ← a.compute B; Jet.tanh A

end Expr
end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedQuadrature
attribute [-instance] _root_.OAI.SKRatio.Certificate.Expr.instAdd _root_.OAI.SKRatio.Certificate.Expr.instDiv _root_.OAI.SKRatio.Certificate.Expr.instMul _root_.OAI.SKRatio.Certificate.Expr.instNeg _root_.OAI.SKRatio.Certificate.Expr.instOfNat _root_.OAI.SKRatio.Certificate.Expr.instSub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real Set MeasureTheory
namespace SKRatio.Certificate

namespace Expr

def cell (e : Expr) (a b : ℚ) : Option Box := do
  if ¬a<b then none else
    let JA ← e.compute (Box.rat a)
    let JB ← e.compute (Box.rat b)
    let J ← e.compute ⟨a,b⟩
    return Box.widen (Box.mul (Box.rat ((b-a)/2)) (Box.add JA.val JB.val))
      ((b-a)^3 * J.sec.absUpper/12)

def quad (e : Expr) (h : ℚ) : ℕ → ℚ → Option Box
  | 0,_ => some (Box.rat 0)
  | n+1,a => do
    let A ← e.cell a (a+h)
    let B ← e.quad h n (a+h)
    return Box.add A B

def check (e : Expr) (a h : ℚ) (n : ℕ) (A : Box) : Bool :=
  match e.quad h n a with
  | none => false
  | some B => A.contains B

end Expr
end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedBatches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real Set MeasureTheory
namespace SKRatio.Certificate

def batchCheck (B : ℕ → Box) (m : ℕ) (A : Box) : Bool :=
  A.contains (normalizedBox (sumBoxes B m))

end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarReduction
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

def variational (β : ℝ) (b r : ℝ → ℝ) : ℝ :=
  (∫ h, diagonal (fieldLaw β) β h*(b h^2+r h^2) ∂fieldLaw β) +
  (∫ h, b h*h ∂fieldLaw β)*(∫ h, b h*v h ∂fieldLaw β) +
  (∫ h, b h ∂fieldLaw β)*(∫ h, b h*(h*v h) ∂fieldLaw β) -
  β^2*(∫ h, b h ∂fieldLaw β)*(∫ h, b h*v h ∂fieldLaw β) +
  2*β^2*(∫ h, b h ∂fieldLaw β)*(∫ h, b h*(m h*v h) ∂fieldLaw β) +
  β^2*(∫ z : ℝ×ℝ, b z.1*kernel z.1 z.2*b z.2 ∂(fieldLaw β).prod (fieldLaw β)) +
  β*(∫ h, r h*sqrt (radicand (fieldLaw β) b r h) ∂fieldLaw β)

end SKRatio.Scalar

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarCoherent
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

def F (β : ℝ) (h : ℝ) : ℝ :=
  (v h+a β)*h + 2*β^2*m h*v h + (50/100-β^2*a β/l β)*v h +
    (12/100)*m h + 3*β^2*G β*g h

def U₀ (β : ℝ) : ℝ := l β+18/1000+
  β^2*(a β^2/l β-a β-(3/2)*G β^2)-β^2*R β

def U₁ (β : ℝ) : ℝ := (4644/10000)-β*sd (fieldLaw β) v/2+
  β^2*(∫ h, m h*v h ∂fieldLaw β)-
    β^2*((3/2)*sd (fieldLaw β) g^2+R β)

def coherentUpper (β : ℝ) (b : ℝ → ℝ) : ℝ :=
  (∫ h, b h*h ∂fieldLaw β)*(∫ h, b h*v h ∂fieldLaw β)+
  (∫ h, b h ∂fieldLaw β)*(∫ h, b h*((h-β^2+2*β^2*m h)*v h) ∂fieldLaw β)+
  β^2*((3/2)*(∫ h, b h*g h ∂fieldLaw β)^2+R β*(∫ h, b h^2 ∂fieldLaw β))-
  β^2/(4*l β)*((∫ h, b h*v h ∂fieldLaw β)+a β*(∫ h, b h ∂fieldLaw β))^2

end SKRatio.Scalar

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarInterpolation
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

def crossBound (j z : ℝ) : ℝ := sqrt (densityFactor j z)*
  (sd (fieldLaw z) (F z)+(a j-a z)*z+
    2*(z^2-j^2)*sd (fieldLaw z) (fun h => m h*v h)+
    (z^2*a j/l j-j^2*a z/l z)*sd (fieldLaw z) v+
    3*(z^2*G j-j^2*G z)*sd (fieldLaw z) g)

def slackBound₀ (j z : ℝ) : ℝ := l j+18/1000+
  j^2*(a z^2/l z-a z-(3/2)*G j^2)-z^2*R z

def slackBound₁ (j z : ℝ) : ℝ := 4644/10000-z*sd (fieldLaw z) v/2+
  j^2*(∫ h, m h*v h ∂fieldLaw j)-z^2*((3/2)*sd (fieldLaw z) g^2+R z)

end SKRatio.Scalar

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedInterpolation
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open Real MeasureTheory ProbabilityTheory
namespace SKRatio.Certificate
open Scalar

structure Valid (β : ℝ) (X : Enclosures) : Prop where
  mem_a : a β ∈ X.av
  mem_G : G β ∈ X.gv
  mem_M : (∫ h, m h*v h ∂fieldLaw β) ∈ X.mv
  mem_R : R β ∈ X.rv
  mem_v : sd (fieldLaw β) v ∈ X.vs
  mem_g : sd (fieldLaw β) g ∈ X.gs
  mem_mv : sd (fieldLaw β) (fun h => m h*v h) ∈ X.ms
  mem_F : sd (fieldLaw β) (F β) ∈ X.fs

end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_UniformGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace SKRatio.Fields
open Real Matrix Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def linearObservable (a : Fin n → ℝ) (x : Spin n) : ℝ := ∑ i, a i*spinValue (x i)

end SKRatio.Fields

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_GaussianEvents
attribute [-instance] _root_.OAI.SKRatio.Planted.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology ENNReal
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Gaussian
open Calculus
variable {n : ℕ}

def matrixGood (β δ : ℝ) (n : ℕ) : Set (Disorder n) :=
  {g | euclideanOpNorm (coupling g) ≤ 2*β+δ ∧
    (∀ i k, |coupling g i k| ≤ δ) ∧
    (∀ i, ∑ k, coupling g i k^2 ≤ β^2+δ)}

end SKRatio.Gaussian

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Entropy_AnnealedTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Planted
open Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def badMass (B : Set (Disorder n)) (g : Disorder n) : ℝ :=
  FiniteLaw.mean (mass g 0) (fun x => if gauge x g ∈ B then 1 else 0)

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_FiniteChain_EntropicCovariance
attribute [-instance] _root_.OAI.SKRatio.Planted.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter Real
namespace SKRatio.Observation
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α]

def var (p : Prior α) (f : α → ℝ) : ℝ := FiniteLaw.variance p f

def ent (p : Prior α) (f : α → ℝ) : ℝ := FiniteLaw.entropy p f

variable {ι : Type*} [Fintype ι]

def reweight (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0 < f x) : Prior α where
  mass x := p x*f x/avg p f
  nonneg x := div_nonneg (mul_nonneg (p.nonneg x) (hf x).le) (avg_pos p hf).le
  sum_one := by rw [← Finset.sum_div];exact div_self (avg_pos p hf).ne'

def gibbsPrior {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) : Prior (Spin n) :=
  ⟨mass g h,mass_nonneg g h,sum_mass g h⟩

end SKRatio.Observation

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Entropy_GaussianChannel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Set Filter
namespace SKRatio.Observation.Channel
variable {α : Type*} [Fintype α] {d : ℕ}

variable (v : α → Fin d → ℝ)

lemma density_pos (p : Prior α) (t : ℝ) (z : Fin d → ℝ) :
    0 < density v p t z := (exp_pos _).trans_le (density_jensen v p t z)

def interaction (p : Prior α) (x y : α) : ℝ :=
  ((∑ i, (v x i+v y i-mean v p i)^2)-normSq v x-normSq v y+secondMoment v p)/2

def pairShift (p : Prior α) (x y : α) : ℝ :=
  (normSq v x+normSq v y-secondMoment v p)/2

def pairKernel (p : Prior α) (t : ℝ) (x y : α) (z : Fin d → ℝ) : ℝ :=
  exp ((∑ i, (sqrt t*(v x i+v y i-mean v p i))*z i)-t*pairShift v p x y)

def majorant (p : Prior α) (a : α → ℝ) (t : ℝ) (z : Fin d → ℝ) : ℝ :=
  (∑ x, a x*likelihood v t x z)^2 * exp (-(sqrt t * (∑ i, mean v p i * z i) - t*secondMoment v p/2))

def quadraticIntegrand (p : Prior α) (a : α → ℝ) (t : ℝ) (z : Fin d → ℝ) : ℝ :=
  (∑ x, a x*likelihood v t x z)^2 / density v p t z

def posterior (p : Prior α) (t : ℝ) (z : Fin d → ℝ) : Prior α where
  mass x := p x * likelihood v t x z / density v p t z
  nonneg x := div_nonneg (mul_nonneg (p.nonneg x) (likelihood_pos v t x z).le)
    (density_pos v p t z).le
  sum_one := by
    rw [← Finset.sum_div]
    exact div_self (density_pos v p t z).ne'

def divergenceIntegrand (p q : Prior α) (t : ℝ) (z : Fin d → ℝ) : ℝ :=
  density v q t z * log (density v q t z/density v p t z) - density v q t z + density v p t z

end SKRatio.Observation.Channel

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Entropy_GaussianHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Real Set Filter
namespace SKRatio.Observation

namespace History
variable {α : Type*} {d : ℕ}

variable (v : α → Fin d → ℝ)

variable [Fintype α]

def density (p : Prior α) (t : ℝ) {k : ℕ} (h : History d k) : ℝ :=
  ∑ x, p x*likelihood v t x h

lemma density_pos (p : Prior α) (t : ℝ) {k : ℕ} (h : History d k) :
    0 < density v p t h := by
  have he : ∃ x, 0 < p x := by
    by_contra hn
    push Not at hn
    have hz : ∑ x, p x = 0 := Finset.sum_eq_zero (fun x _ => le_antisymm (hn x) (p.nonneg x))
    linarith [p.sum_one]
  obtain ⟨x,hx⟩ := he
  exact Finset.sum_pos' (fun y _ => mul_nonneg (p.nonneg y) (likelihood_pos v t y h).le)
    ⟨x, Finset.mem_univ _, mul_pos hx (likelihood_pos v t x h)⟩

def posterior (p : Prior α) (t : ℝ) {k : ℕ} (h : History d k) : Prior α where
  mass x := p x*likelihood v t x h/density v p t h
  nonneg x := div_nonneg (mul_nonneg (p.nonneg x) (likelihood_pos v t x h).le) (density_pos v p t h).le
  sum_one := by rw [← Finset.sum_div]; exact div_self (density_pos v p t h).ne'

def remainingEntropy (p : Prior α) (f : α → ℝ) (t : ℝ) (k : ℕ) : ℝ :=
  ∫ h : History d k, density v p t h*ent (posterior v p t h) f ∂reference d k

end History
end SKRatio.Observation

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Entropy_ProductEntropy
attribute [-instance] _root_.OAI.SKRatio.Planted.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Real
namespace SKRatio.Observation
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

def productPrior (q : Fin n → Prior Bool) : Prior (Spin n) where
  mass x := ∏ i, q i (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (q i).nonneg (x i))
  sum_one := by
    rw [← Fintype.prod_sum]
    simp only [Prior.sum_one,Finset.prod_const_one]

def productSiteEntropy (q : Fin n → Prior Bool) (f : Spin n → ℝ) (i : Fin n) : ℝ :=
  avg (productPrior q) (fun x => ent (q i) (fun b => f (Function.update x i b)))

end SKRatio.Observation

namespace SKRatio.Fields
open Observation
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def sitePrior (g : Disorder n) (h : Fin n → ℝ) (i : Fin n) (x : Spin n) : Prior Bool where
  mass b := (if b then weight g h x else weight g h (flip i x)) /
    (weight g h x+weight g h (flip i x))
  nonneg b := div_nonneg (by split <;> exact (weight_pos _ _ _).le)
    (add_pos (weight_pos _ _ _) (weight_pos _ _ _)).le
  sum_one := by simp only [Fintype.sum_bool,Bool.false_eq_true,↓reduceIte,←add_div];
                 rw [add_comm,div_self (add_pos (weight_pos _ _ _) (weight_pos _ _ _)).ne']

end SKRatio.Fields

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Entropy_GibbsObservation
attribute [-instance] _root_.OAI.SKRatio.Planted.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Matrix MatrixOrder Topology
open MeasureTheory Real Matrix
namespace SKRatio.Observation
open Calculus Fields
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def shiftedCoupling (g : Disorder n) : Matrix (Fin n) (Fin n) ℝ := Matrix.of (coupling g) + (2:ℝ) • 1

def observationMatrix (g : Disorder n) : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt (shiftedCoupling g)

def gibbsFeature (g : Disorder n) (x : Spin n) : Fin n → ℝ :=
  (observationMatrix g).mulVec (fun i => spinValue (x i))

def observedField (g : Disorder n) (t : ℝ) (h₀ : Fin n → ℝ) :
    {k : ℕ} → History n k → Fin n → ℝ
  | 0,_ => h₀
  | _+1,h => observedField g t h₀ h.1+sqrt t • (observationMatrix g).mulVec h.2

def fieldPrior (h : ℝ) : Prior Bool where
  mass b := exp (h*spinValue b)/(exp h+exp (-h))
  nonneg b := div_nonneg (exp_pos _).le (add_pos (exp_pos _) (exp_pos _)).le
  sum_one := by
    simp only [Fintype.sum_bool,spinValue_true,spinValue_false,mul_one,mul_neg_one,←add_div]
    exact div_self (add_pos (exp_pos _) (exp_pos _)).ne'

end SKRatio.Observation

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_PlantedCriterion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Planted
open Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def formBad (ρ : ℝ) (n : ℕ) : Set (Disorder n) :=
  {g | ∃ p : Fin n → ℝ, (1-ρ)*(∑ i, p i^2) < gradientForm (coupling g) p}

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_PlantedSquares
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open SKRatioClock.Regression MatrixNet
attribute [local instance] Classical.propDecidable

def affineDisorder {n : ℕ} (β : ℝ) (z : Disorder n) : Disorder n :=
  fun e => (β / sqrt n)*z e+β^2/n

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_RowGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open Set Real
namespace SKRatio.Planted
open MatrixNet
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def diagonalField (ζ : Fin n → ℝ) (g : Disorder n) (j : Fin n) : ℝ :=
  ζ j+∑ k, coupling g j k

def eraseRow (i : Fin n) (g : Disorder n) : Disorder n :=
  fun e => if e∈incidentEdges i then 0 else g e

def outsideDisorder (β : ℝ) (i : Fin n)
    (y : {e // e∉incidentEdges i} → ℝ) : Disorder n :=
  fun e => if he : e∈incidentEdges i then 0 else β/sqrt n*y ⟨e,he⟩+β^2/(n:ℝ)

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_WeightedSquares
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open SKRatioClock.Regression MatrixNet
attribute [local instance] Classical.propDecidable

def squareError {n : ℕ} (β : ℝ) (g : Disorder n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => coupling g i j^2-β^2/n

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_AugmentedSquares
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open SKRatioClock.Regression MatrixNet
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def diagonalSquareError {X : Type*} (β : ℝ) (G : X × X → ℝ) (b : ℝ → X)
    (p : (Fin n → ℝ) × Disorder n) (i : Fin n) : ℝ :=
  ∑ e : incidentEdges i, (p.2 e^2-β^2/(n:ℝ))*
    G (b (diagonalField p.1 p.2 i),b (diagonalField p.1 p.2 (otherEnd i e)))

end SKRatio.Planted

end
end

end OAI
end


