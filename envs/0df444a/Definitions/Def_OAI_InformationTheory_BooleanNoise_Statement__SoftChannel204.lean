-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement__SoftChannel204
-- name    : OAI_InformationTheory_BooleanNoise_Statement__SoftChannel204
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T14:28:45.168+00:00
-- url     : https://prove2.me/theorems/5ff5e832-cf3f-47ee-bf1d-4b18da6c6b46
-- title:
--   Boundary values of $t\log t$ and binary entropy
-- statement:
--   These notions belong to a formal proof of sharp information inequalities for soft channels on the Boolean cube. For $g:\{0,1\}^n\to[-1,1]$ let $h(v)=\log2-\psi(v)$, where $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$, so $h(v)$ is the entropy in nats of a random sign with mean $v$. The information of $g$ is $I(g)=h(\mathbb Eg)-\mathbb Eh(g)$, and $T_\rho$ is the noise operator with correlation $\rho$. The main results are the soft contraction $I(T_\rho g)\le\psi(|\rho|\,\psi^{-1}(I(g)))$ and its attainment by scaled dictators. Further results identify $I(T_\rho g)$ with a mutual information and give the Courtade–Kumar bound of $1-H(\varepsilon)$ bits for Boolean functions. The last is the sharp production inequality $r(I(g))\le\mathcal D(g)$, where $\mathcal D(g)=\sum_i\mathbb E[\operatorname{artanh}(g)\,\partial_ig]$ and $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$.
--
--   With $\phi(t)=t\log t$ and $H(\varepsilon)=-\bigl(\phi(\varepsilon)+\phi(1-\varepsilon)\bigr)/\log2$ the binary entropy in bits,
--   $$
--   \phi(0)=0,\qquad H(0)=0,\qquad H(1)=0 .
--   $$
--
--   These are the boundary cases $\varepsilon\in\{0,1\}$ of the Courtade–Kumar bound $I\le1-H(\varepsilon)$: without noise the bound reads $I\le1$.
--
--   **Formalization Note** $\phi(0)=0$ holds because Lean sets $\log0=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/Statement.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/Statement.lean by skeleton subtraction
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
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PairEntropy__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LambdaScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_JensenGaps__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeVariance__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_NormalizedPair__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveLogTrapezoid__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveCalculus__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveInequality__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Comparison__SoftChannel204

namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

@[simp] theorem xlogx_zero : xlogx 0 = 0 := by simp [xlogx]

@[simp] theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  simp [binaryEntropy, xlogx]

@[simp] theorem binaryEntropy_one : binaryEntropy 1 = 0 := by
  simp [binaryEntropy, xlogx]

end LeanBlast.CourtadeKumar

end

end OAI


