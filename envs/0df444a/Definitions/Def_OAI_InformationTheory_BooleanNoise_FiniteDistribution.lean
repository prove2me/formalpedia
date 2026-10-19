-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution
-- name    : OAI_InformationTheory_BooleanNoise_FiniteDistribution
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:12:34.320021+00:00
-- url     : https://prove2.me/theorems/83ab64e0-d89c-48bc-8f1f-06364703a180
-- title:
--   The law of a $\pm1$ variable with prescribed mean
-- statement:
--   For $v\in\mathbb{R}$ and a bit $b$, define
--   $$
--   P_v(\mathrm{true})=\frac{1+v}{2},\qquad P_v(\mathrm{false})=\frac{1-v}{2}.
--   $$
--   For $-1\le v\le1$ this is the distribution of a random sign with mean $v$.
--
--   It converts real-valued noise-smoothed functions back into probabilities of the function value, when expressing mutual information through entropies.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/FiniteDistribution.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/FiniteDistribution.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

def signProbability (v : ℝ) (b : Bool) : ℝ :=
  if b then (1 + v) / 2 else (1 - v) / 2

end LeanBlast.CourtadeKumar

end

end OAI


