-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_PairEntropy
-- name    : OAI_InformationTheory_BooleanNoise_PairEntropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:35:42.701979+00:00
-- url     : https://prove2.me/theorems/82f7f5f2-791b-4b09-8e74-56fbdaa8b733
-- title:
--   The pair entropy gap and pair dissipation vanish at zero difference
-- statement:
--   Let $h(v)=\log2-\psi(v)$ be the entropy of a sign with mean $v$. Define
--   $$
--   \Delta(a,b)=h(a)-\frac{h(a+b)+h(a-b)}{2},\qquad \delta(a,b)=\frac b2\bigl(\operatorname{artanh}(a+b)-\operatorname{artanh}(a-b)\bigr).
--   $$
--   Then for all $a$,
--   $$
--   \Delta(a,0)=0,\qquad \delta(a,0)=0 .
--   $$
--
--   $\Delta$ and $\delta$ are the one-coordinate contributions to the information deficit and to the dissipation. They vanish when the function does not depend on the split coordinate.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/PairEntropy.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/PairEntropy.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace LeanBlast.CourtadeKumar

@[simp] theorem pairEntropyGap_zero (a : ℝ) : pairEntropyGap a 0 = 0 := by
  simp [pairEntropyGap]

@[simp] theorem pairDissipation_zero (a : ℝ) : pairDissipation a 0 = 0 := by
  simp [pairDissipation]

end LeanBlast.CourtadeKumar

end

end OAI


