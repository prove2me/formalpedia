-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries
-- name    : OAI_InformationTheory_BooleanNoise_EntropySeries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:21:44.433648+00:00
-- url     : https://prove2.me/theorems/de951e1d-06ec-4d48-837d-53109d2d40c7
-- title:
--   Power series coefficients of the entropy function $\psi$
-- statement:
--   For $k\in\mathbb{N}$ define
--   $$
--   c_k=\frac{1}{(2k+2)(2k+1)},\qquad c_0=\frac12 .
--   $$
--
--   These are the coefficients of the even power series $\psi(v)=\sum_{k\ge0}c_kv^{2k+2}$ of $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$, valid for $|v|<1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/EntropySeries.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/EntropySeries.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open Set Filter Finset
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

def psiCoeff (k : ℕ) : ℝ := 1 / ((2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1))

@[simp] theorem psiCoeff_zero : psiCoeff 0 = 1 / 2 := by norm_num [psiCoeff]

end LeanBlast.CourtadeKumar

end

end OAI


