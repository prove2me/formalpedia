-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_LambdaScalars
-- name    : OAI_InformationTheory_BooleanNoise_LambdaScalars
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:36:27.233048+00:00
-- url     : https://prove2.me/theorems/56cc38a9-5174-4119-8524-63a5b108f1e8
-- title:
--   The function $\lambda(z)=-\log(1-z)/z$
-- statement:
--   For real $z$ define
--   $$
--   \lambda(z)=\begin{cases}\dfrac{-\log(1-z)}{z},&z\ne0,\\1,&z=0.\end{cases}
--   $$
--
--   For $|z|<1$ this is the power series $\sum_{k\ge0}\frac{z^k}{k+1}$, continuous at $0$ with $\lambda(0)=1$. It appears in closed forms for sums of entropy series coefficients used in the curvature estimates.
--
--   **Formalization Note** For $z\ge1$, Lean's convention $\log x=\log|x|$ (with $\log0=0$) applies.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/LambdaScalars.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/LambdaScalars.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Set Filter

namespace LeanBlast.CourtadeKumar

def lambda (z : ℝ) : ℝ := if z = 0 then 1 else -Real.log (1 - z) / z

@[simp] theorem lambda_zero : lambda 0 = 1 := by simp [lambda]

end LeanBlast.CourtadeKumar

end

end OAI


