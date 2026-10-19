-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity
-- name    : OAI_InformationTheory_BooleanNoise_LRegularity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:29:27.017547+00:00
-- url     : https://prove2.me/theorems/284e47ba-bbea-46c7-928c-7fe21880815b
-- title:
--   The second derivative of the gap function $L$
-- statement:
--   For $x<\log2$ define $L''(x)=r''(\log2-x)$, and set $L''(x)=0$ for $x\ge\log2$. Here $r''$ is the explicit second-derivative expression of $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$, which equals $\frac43$ for $s\le0$.
--
--   This records the curvature of the gap function $L(x)=r(\log2-x)-2(\log2-x)$, used to prove its regularity and convexity properties.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/LRegularity.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/LRegularity.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

def LSecondDeriv (x : ℝ) : ℝ :=
  if x < ell then rSecondDeriv (ell - x) else 0

end LeanBlast.CourtadeKumar

end

end OAI


