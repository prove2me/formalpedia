-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds
-- name    : OAI_InformationTheory_BooleanNoise_EntropyBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:22:49.876996+00:00
-- url     : https://prove2.me/theorems/c62a932b-1acb-4a27-b2ba-a41ff0e6366a
-- title:
--   The power series of $\psi$
-- statement:
--   For $v\in\mathbb{R}$ define
--   $$
--   \Psi(v)=\sum_{k=0}^{\infty}\frac{v^{2k+2}}{(2k+2)(2k+1)} .
--   $$
--
--   For $|v|\le1$ the series converges, and it is used to prove two-sided polynomial bounds on $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$.
--
--   **Formalization Note** The sum is Lean's `tsum`, which is $0$ for non-summable families, i.e. for $|v|>1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/EntropyBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/EntropyBounds.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open Set Filter Finset
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

def psiSeries (v : ℝ) : ℝ := ∑' k : ℕ, psiCoeff k * v ^ (2 * (k + 1))

end LeanBlast.CourtadeKumar

end

end OAI


