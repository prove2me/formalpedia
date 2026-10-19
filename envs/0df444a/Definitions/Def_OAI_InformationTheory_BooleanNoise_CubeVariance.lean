-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeVariance
-- name    : OAI_InformationTheory_BooleanNoise_CubeVariance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:40:57.602164+00:00
-- url     : https://prove2.me/theorems/a9c120c5-97e8-4352-a089-ef6ac468d972
-- title:
--   Relative entropy between two $\pm1$ laws with given means
-- statement:
--   For $a,m\in\mathbb{R}$ define
--   $$
--   D(a\,\|\,m)=\frac{1+a}{2}\log\frac{1+a}{1+m}+\frac{1-a}{2}\log\frac{1-a}{1-m}.
--   $$
--   For $a,m\in(-1,1)$ this is the Kullback–Leibler divergence (in nats) from the law of a sign with mean $m$ to that with mean $a$.
--
--   It controls entropy differences in terms of variances on the cube.
--
--   **Formalization Note** Lean's conventions $\log0=0$ and $x/0=0$ apply at the boundary values.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/CubeVariance.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/CubeVariance.lean by skeleton subtraction
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
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity
import Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PairEntropy
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LambdaScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_JensenGaps

namespace OAI

open scoped BigOperators

noncomputable section

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

def binaryRelativeEntropy (a m : ℝ) : ℝ :=
  (1 + a) / 2 * Real.log ((1 + a) / (1 + m)) +
    (1 - a) / 2 * Real.log ((1 - a) / (1 - m))

end LeanBlast.CourtadeKumar

end

end OAI


