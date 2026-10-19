-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds__SoftChannel204
-- name    : OAI_InformationTheory_BooleanNoise_CurvatureBounds__SoftChannel204
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T14:00:44.959984+00:00
-- url     : https://prove2.me/theorems/0dafe6ef-0232-418e-9d27-1d391c17b8ae
-- title:
--   The curvature model of the rate function
-- statement:
--   These notions belong to a formal proof of sharp information inequalities for soft channels on the Boolean cube. For $g:\{0,1\}^n\to[-1,1]$ let $h(v)=\log2-\psi(v)$, where $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$, so $h(v)$ is the entropy in nats of a random sign with mean $v$. The information of $g$ is $I(g)=h(\mathbb Eg)-\mathbb Eh(g)$, and $T_\rho$ is the noise operator with correlation $\rho$. The main results are the soft contraction $I(T_\rho g)\le\psi(|\rho|\,\psi^{-1}(I(g)))$ and its attainment by scaled dictators. Further results identify $I(T_\rho g)$ with a mutual information and give the Courtade–Kumar bound of $1-H(\varepsilon)$ bits for Boolean functions. The last is the sharp production inequality $r(I(g))\le\mathcal D(g)$, where $\mathcal D(g)=\sum_i\mathbb E[\operatorname{artanh}(g)\,\partial_ig]$ and $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$.
--
--   1. **Curvature model.** For real $u$ and $t$,
--   $$
--   \kappa(u,t)=\frac{(1+u^2)t-u}{(1-u^2)^2t^3}.
--   $$
--   With $t=\operatorname{artanh}u$ and $u=\psi^{-1}(s)$, this is the second derivative $r''(s)$ of the rate function $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$. Upper bounds on its numerator $((1+u^2)\operatorname{artanh}u-u)/u^3$ control the curvature of $r$.
--
--   **Formalization Note** Lean's convention $x/0=0$ applies at the singular points.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/CurvatureBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/CurvatureBounds.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SoftChannel204 mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SoftChannel204
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Model
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature__SoftChannel204

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

def curvatureModel (u t : ℝ) : ℝ :=
  ((1 + u ^ 2) * t - u) / ((1 - u ^ 2) ^ 2 * t ^ 3)

end LeanBlast.CourtadeKumar

end

end OAI


