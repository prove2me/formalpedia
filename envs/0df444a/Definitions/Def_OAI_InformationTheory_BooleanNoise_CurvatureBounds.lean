-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds
-- name    : OAI_InformationTheory_BooleanNoise_CurvatureBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:28:18.261977+00:00
-- url     : https://prove2.me/theorems/65170f06-cfd1-427e-bea7-5d0f69970e58
-- title:
--   The curvature model function and a coarse bound for small arguments
-- statement:
--   For real $u$ and $t$, and for $z$, define
--   $$
--   \kappa(u,t)=\frac{(1+u^2)t-u}{(1-u^2)^2t^3},\qquad \beta(z)=\frac{\frac43+\frac23\cdot\frac{z}{1-z}}{(1-z)^2\bigl(1+\frac z3\bigr)^3}.
--   $$
--
--   With $t=\operatorname{artanh}u$, $\kappa$ is the second derivative of $r$ written in terms of $w=\psi^{-1}(s)$. The function $\beta$ is an explicit upper bound for it in the small range, where $z$ is a squared variable.
--
--   **Formalization Note** Lean's convention $x/0=0$ applies at the singular points.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/CurvatureBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/CurvatureBounds.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

def curvatureModel (u t : ℝ) : ℝ :=
  ((1 + u ^ 2) * t - u) / ((1 - u ^ 2) ^ 2 * t ^ 3)

 def smallCoarseBound (z : ℝ) : ℝ :=
  ((4 / 3) + (2 / 3) * (z / (1 - z))) / ((1 - z) ^ 2 * (1 + z / 3) ^ 3)

end LeanBlast.CourtadeKumar

end

end OAI


