-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_NormalizedPair
-- name    : OAI_InformationTheory_BooleanNoise_NormalizedPair
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:42:11.637114+00:00
-- url     : https://prove2.me/theorems/51f42733-5573-446a-81a1-dc4ef30f3ee2
-- title:
--   Raw and normalized even moments of a two-point perturbation
-- statement:
--   For $a,b\in\mathbb{R}$ and $j\in\mathbb{N}$ define
--   $$
--   R_j(a,b)=\frac{1+a}{2}\Bigl(\frac{b}{1+a}\Bigr)^{2j}+\frac{1-a}{2}\Bigl(\frac{b}{1-a}\Bigr)^{2j},\qquad N_j(a,b)=\begin{cases}1,&j=0,\\ \dfrac{R_j(a,b)}{1-a^2},&j\ge1.\end{cases}
--   $$
--
--   $R_j$ is the $2j$-th moment of the relative perturbation $b/(1\pm a)$ under the sign law with mean $a$. Normalized moments organize the series expansion of the pair entropy gap $h(a)-\frac{h(a+b)+h(a-b)}2$ in powers of $b$.
--
--   **Formalization Note** Lean's convention $x/0=0$ applies when $a=\pm1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/NormalizedPair.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/NormalizedPair.lean by skeleton subtraction
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

namespace OAI

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

noncomputable def rawPairMoment (a b : ℝ) (j : ℕ) : ℝ :=
  (1 + a) / 2 * (b / (1 + a)) ^ (2 * j) +
    (1 - a) / 2 * (b / (1 - a)) ^ (2 * j)

noncomputable def normalizedPairMoment (a b : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 1 else rawPairMoment a b j / (1 - a ^ 2)

@[simp]
theorem normalizedPairMoment_zero (a b : ℝ) : normalizedPairMoment a b 0 = 1 := by
  simp [normalizedPairMoment]

@[simp]
theorem normalizedPairMoment_succ (a b : ℝ) (j : ℕ) :
    normalizedPairMoment a b (j + 1) = rawPairMoment a b (j + 1) / (1 - a ^ 2) := by
  simp [normalizedPairMoment]

end LeanBlast.CourtadeKumar

end OAI


