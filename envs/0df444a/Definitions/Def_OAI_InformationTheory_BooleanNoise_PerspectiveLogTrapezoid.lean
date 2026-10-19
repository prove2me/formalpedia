-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveLogTrapezoid
-- name    : OAI_InformationTheory_BooleanNoise_PerspectiveLogTrapezoid
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:45:37.367999+00:00
-- url     : https://prove2.me/theorems/f9473d20-1ac4-41b6-af83-ef01f68f473e
-- title:
--   A logarithmic trapezoid gap and its derivative
-- statement:
--   For real $q,w$ define
--   $$
--   G(q,w)=(1+w-2q)\bigl(\log(1-q)-\log(w-q)\bigr)+(1+w)\log w,
--   $$
--   together with the expression
--   $$
--   G'(q,w)=\log(1-q)-\log(w-q)-\frac{1+w-2q}{w-q}+\log w+\frac{1+w}{w},
--   $$
--   which is the derivative of $G$ in $w$ wherever the logarithms are taken at positive arguments.
--
--   This function measures the error of a trapezoid-type comparison for logarithms. Its sign is used in the perspective inequalities of the curvature analysis.
--
--   **Formalization Note** That $G'$ is the derivative is proved separately. Lean's conventions for $\log$ and division apply outside the intended domain $q<1$, $w>q$, $w>0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/PerspectiveLogTrapezoid.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/PerspectiveLogTrapezoid.lean by skeleton subtraction
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
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeVariance
import Definitions.Def_OAI_InformationTheory_BooleanNoise_NormalizedPair

namespace OAI

noncomputable section

namespace LeanBlast.CourtadeKumar

 def trapezoidGap (q w : ℝ) : ℝ :=
  (1 + w - 2 * q) * (Real.log (1 - q) - Real.log (w - q)) +
    (1 + w) * Real.log w

 def trapezoidGapDeriv (q w : ℝ) : ℝ :=
  Real.log (1 - q) - Real.log (w - q) - (1 + w - 2 * q) / (w - q) +
    Real.log w + (1 + w) / w

end LeanBlast.CourtadeKumar

end

end OAI


