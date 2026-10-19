-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature
-- name    : OAI_InformationTheory_BooleanNoise_MediumCurvature
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:26:13.072031+00:00
-- url     : https://prove2.me/theorems/277028e8-8900-4034-85da-857ebf225247
-- title:
--   Series coefficients of a curvature numerator
-- statement:
--   For $k\in\mathbb{N}$ define
--   $$
--   a_k=\frac1{2k+1}+\frac1{2k+3}.
--   $$
--
--   These are the coefficients of the series expansion of the numerator of the second derivative of $r$ in the medium range of correlations. They are used to compare the curvature with explicit polynomials.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/MediumCurvature.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/MediumCurvature.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CourtadeKumar mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model__CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement__CourtadeKumar
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_ComparisonEstimates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds

namespace OAI

noncomputable section

open Finset Set
open scoped BigOperators

namespace LeanBlast.CourtadeKumar

def curvatureNumeratorCoeff (k : ℕ) : ℝ :=
  1 / (2 * (k : ℝ) + 1) + 1 / (2 * (k : ℝ) + 3)

end LeanBlast.CourtadeKumar

end

end OAI


