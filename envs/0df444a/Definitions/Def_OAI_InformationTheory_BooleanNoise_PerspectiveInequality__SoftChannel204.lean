-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveInequality__SoftChannel204
-- name    : OAI_InformationTheory_BooleanNoise_PerspectiveInequality__SoftChannel204
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T14:24:51.591895+00:00
-- url     : https://prove2.me/theorems/36e65587-362c-4be6-b648-b8d3a153fa3a
-- title:
--   Logarithmic barrier and auxiliary $\lambda$-functions
-- statement:
--   These notions belong to a formal proof of sharp information inequalities for soft channels on the Boolean cube. For $g:\{0,1\}^n\to[-1,1]$ let $h(v)=\log2-\psi(v)$, where $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$, so $h(v)$ is the entropy in nats of a random sign with mean $v$. The information of $g$ is $I(g)=h(\mathbb Eg)-\mathbb Eh(g)$, and $T_\rho$ is the noise operator with correlation $\rho$. The main results are the soft contraction $I(T_\rho g)\le\psi(|\rho|\,\psi^{-1}(I(g)))$ and its attainment by scaled dictators. Further results identify $I(T_\rho g)$ with a mutual information and give the Courtade–Kumar bound of $1-H(\varepsilon)$ bits for Boolean functions. The last is the sharp production inequality $r(I(g))\le\mathcal D(g)$, where $\mathcal D(g)=\sum_i\mathbb E[\operatorname{artanh}(g)\,\partial_ig]$ and $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$.
--
--   Let $\lambda(z)=-\log(1-z)/z$ (with $\lambda(0)=1$) and let $\ell(b)=-\log(1-b)$ be the logarithmic barrier, with $\ell(0)=0$. Define
--   $$
--   \Phi(b)=9-b-3b^2-b^3-3(1-b^4)\lambda(b)-2(1-b^4)\lambda(b^2),
--   $$
--   $$
--   A(b)=3\ell(b^4)-b^3\ell(b)-b^2\ell(b^2),\qquad A(0)=0,
--   $$
--   and the expression
--   $$
--   A'(b)=\frac{12b^3}{1-b^4}-3b^2\ell(b)-\frac{b^3}{1-b}-2b\,\ell(b^2)-\frac{2b^3}{1-b^2}.
--   $$
--
--   These explicit elementary functions arise when the perspective inequality is reduced to a one-variable inequality in $b\in[0,1)$. Their positivity is certified by polynomial (Bernstein) bounds.
--
--   **Formalization Note** $A'$ is the derivative of $A$ on $(-1,1)$, as proved separately.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/PerspectiveInequality.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/PerspectiveInequality.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Set Filter

namespace LeanBlast.CourtadeKumar

def logBarrier (b : ℝ) : ℝ := -Real.log (1 - b)

@[simp] theorem logBarrier_zero : logBarrier 0 = 0 := by simp [logBarrier]

def lambdaDerivativeFactor (b : ℝ) : ℝ :=
  9 - b - 3 * b ^ 2 - b ^ 3 - 3 * (1 - b ^ 4) * lambda b -
    2 * (1 - b ^ 4) * lambda (b ^ 2)

def lambdaAuxiliary (b : ℝ) : ℝ :=
  3 * logBarrier (b ^ 4) - b ^ 3 * logBarrier b - b ^ 2 * logBarrier (b ^ 2)

def lambdaAuxiliaryDerivative (b : ℝ) : ℝ :=
  12 * b ^ 3 / (1 - b ^ 4) - 3 * b ^ 2 * logBarrier b - b ^ 3 / (1 - b) -
    2 * b * logBarrier (b ^ 2) - 2 * b ^ 3 / (1 - b ^ 2)

@[simp] theorem lambdaAuxiliary_zero : lambdaAuxiliary 0 = 0 := by
  simp [lambdaAuxiliary]

end LeanBlast.CourtadeKumar

end

end OAI


