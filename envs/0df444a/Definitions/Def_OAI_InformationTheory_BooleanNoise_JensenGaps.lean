-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_JensenGaps
-- name    : OAI_InformationTheory_BooleanNoise_JensenGaps
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:37:12.569155+00:00
-- url     : https://prove2.me/theorems/73bc0acc-8aff-4935-b6fb-74ea464bb5a8
-- title:
--   Entropy series coefficients for Jensen-gap expansions
-- statement:
--   For $j\in\mathbb{N}$, the entropy series coefficient is
--   $$
--   c_j=\frac{1}{(2j+2)(2j+1)},
--   $$
--   the coefficient of $v^{2j+2}$ in the power series of $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$.
--
--   Under this name the coefficients are used to expand Jensen gaps $\mathbb{E}\psi(g)-\psi(\mathbb{E}g)$ as nonnegative combinations of even moments.
--
--   **Formalization Note** `entropySeriesCoeff` is an abbreviation for `psiCoeff`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/JensenGaps.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/JensenGaps.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators

universe u

namespace LeanBlast.CourtadeKumar

section Weighted

variable {ι : Type u} [Fintype ι]

 abbrev entropySeriesCoeff (j : ℕ) : ℝ := psiCoeff j

end Weighted

end LeanBlast.CourtadeKumar

end

end OAI


