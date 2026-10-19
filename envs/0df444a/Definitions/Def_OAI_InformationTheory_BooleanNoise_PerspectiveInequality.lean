-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveInequality
-- name    : OAI_InformationTheory_BooleanNoise_PerspectiveInequality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:48:00.873418+00:00
-- url     : https://prove2.me/theorems/f69a0f72-9792-4889-beef-1e634cac744d
-- title:
--   The logarithmic barrier and the auxiliary $\lambda$-combinations
-- statement:
--   Let $\lambda(z)=-\log(1-z)/z$ (with $\lambda(0)=1$) and let $\ell(b)=-\log(1-b)$ be the logarithmic barrier, with $\ell(0)=0$. Define
--   $$
--   \Phi(b)=9-b-3b^2-b^3-3(1-b^4)\lambda(b)-2(1-b^4)\lambda(b^2),
--   $$
--   $$
--   A(b)=3\ell(b^4)-b^3\ell(b)-b^2\ell(b^2),\qquad A(0)=0,
--   $$
--   and the expression
--   $$
--   A'(b)=\frac{12b^3}{1-b^4}-3b^2\ell(b)-\frac{b^3}{1-b}-2b\,\ell(b^2)-\frac{2b^3}{1-b^2}.
--   $$
--
--   These explicit elementary functions arise when the perspective inequality is reduced to a one-variable inequality in $b\in[0,1)$. Their positivity is certified by polynomial (Bernstein) bounds.
--
--   **Formalization Note** $A'$ is the derivative of $A$ on $(-1,1)$, as proved separately.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/PerspectiveInequality.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/PerspectiveInequality.lean by skeleton subtraction
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
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveCalculus

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Set Filter

namespace LeanBlast.CourtadeKumar

def logBarrier (b : ℝ) : ℝ := -Real.log (1 - b)

@[simp] theorem logBarrier_zero : logBarrier 0 = 0 := by simp [logBarrier]

def lambdaDerivativeFactor (b : ℝ) : ℝ :=
  9 - b - 3 * b ^ 2 - b ^ 3 - 3 * (1 - b ^ 4) * lambda b -
    2 * (1 - b ^ 4) * lambda (b ^ 2)

def lambdaAuxiliary (b : ℝ) : ℝ :=
  3 * logBarrier (b ^ 4) - b ^ 3 * logBarrier b - b ^ 2 * logBarrier (b ^ 2)

def lambdaAuxiliaryDerivative (b : ℝ) : ℝ :=
  12 * b ^ 3 / (1 - b ^ 4) - 3 * b ^ 2 * logBarrier b - b ^ 3 / (1 - b) -
    2 * b * logBarrier (b ^ 2) - 2 * b ^ 3 / (1 - b ^ 2)

@[simp] theorem lambdaAuxiliary_zero : lambdaAuxiliary 0 = 0 := by
  simp [lambdaAuxiliary]

end LeanBlast.CourtadeKumar

end

end OAI


