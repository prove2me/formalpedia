-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_ComparisonEstimates
-- name    : OAI_InformationTheory_BooleanNoise_ComparisonEstimates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:18:08.028831+00:00
-- url     : https://prove2.me/theorems/ad8636ac-dfb5-4616-b817-0b675dcff74b
-- title:
--   Comparison functions for the small-correlation regime
-- statement:
--   For $u>0$ define
--   $$
--   C(u)=\frac{100}{81}+\log\frac9{10}-\log u,\qquad \beta(u)=\Bigl(1+\frac{u^2}3\Bigr)C(u)-\frac13 .
--   $$
--
--   These explicit comparison functions bound entropy-type quantities for small values of the correlation, where series expansions alone are not uniform.
--
--   **Formalization Note** For $u\le0$, Lean's convention $\log u=\log|u|$, with $\log0=0$, applies.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/ComparisonEstimates.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/ComparisonEstimates.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open Set

namespace LeanBlast.CourtadeKumar

def comparisonC (u : ℝ) : ℝ :=
  100 / 81 + Real.log (9 / 10) - Real.log u

def comparisonBracket (u : ℝ) : ℝ :=
  (1 + u ^ 2 / 3) * comparisonC u - 1 / 3

end LeanBlast.CourtadeKumar

end

end OAI


