-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow
-- name    : OAI_InformationTheory_BooleanNoise_SemigroupFlow
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:31:52.154291+00:00
-- url     : https://prove2.me/theorems/cb1acfdb-ae4a-418e-b319-2e9a9635d3ba
-- title:
--   The noise semigroup in continuous time
-- statement:
--   For $F:\{0,1\}^n\to\mathbb{R}$ and $t\in\mathbb{R}$, let
--   $$
--   P_tF=T_{e^{-t}}F,
--   $$
--   where $T_u$ is the noise operator with correlation $u$. In particular $P_0F=F$.
--
--   $P_t$ is the heat (Ornstein–Uhlenbeck) semigroup on the cube. Differentiating information quantities along it produces the dissipation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/SemigroupFlow.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/SemigroupFlow.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

def noiseFlow (F : Cube n → ℝ) (t : ℝ) : Cube n → ℝ :=
  noiseOperator (Real.exp (-t)) F

@[simp]
theorem noiseFlow_zero (F : Cube n → ℝ) : noiseFlow F 0 = F := by
  funext x
  simp [noiseFlow]

end LeanBlast.CourtadeKumar

end

end OAI


