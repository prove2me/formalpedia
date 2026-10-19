-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveCalculus
-- name    : OAI_InformationTheory_BooleanNoise_PerspectiveCalculus
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:47:08.198259+00:00
-- url     : https://prove2.me/theorems/798715b5-4a13-4eee-be49-dbdadc8d3866
-- title:
--   The log-corrected perspective of a function and its derivative formulas
-- statement:
--   For a function $f:\mathbb{R}\to\mathbb{R}$ and real $x,C,v$ define the log-corrected perspective
--   $$
--   P_f(x,C,v)=v\,f\Bigl(\frac xv\Bigr)-C\,v\log v,
--   $$
--   and, given candidate derivatives $f'$ and $f''$, the expressions
--   $$
--   \partial_vP=f\Bigl(\frac xv\Bigr)-\frac xv\,f'\Bigl(\frac xv\Bigr)-C(\log v+1),\qquad \partial_v^2P=\frac{\bigl(\frac xv\bigr)^2f''\bigl(\frac xv\bigr)-C}{v}.
--   $$
--
--   The perspective $v f(x/v)$ of a convex function is jointly convex. The logarithmic correction $-Cv\log v$ adjusts the curvature in $v$. These formulas are the calculus behind convexity arguments in the induction on dimension.
--
--   **Formalization Note** The derivative expressions are definitions; their validity as derivatives, for $v>0$ and differentiable $f$, is proved separately.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/PerspectiveCalculus.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/PerspectiveCalculus.lean by skeleton subtraction
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
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveLogTrapezoid

namespace OAI

noncomputable section

open Set

namespace LeanBlast.CourtadeKumar

def logCorrectedPerspective (f : ℝ → ℝ) (x C v : ℝ) : ℝ :=
  v * f (x / v) - C * v * Real.log v

def logCorrectedPerspectiveDeriv (f f' : ℝ → ℝ) (x C v : ℝ) : ℝ :=
  f (x / v) - (x / v) * f' (x / v) - C * (Real.log v + 1)

def logCorrectedPerspectiveSecondDeriv (f'' : ℝ → ℝ) (x C v : ℝ) : ℝ :=
  ((x / v) ^ 2 * f'' (x / v) - C) / v

end LeanBlast.CourtadeKumar

end

end OAI


