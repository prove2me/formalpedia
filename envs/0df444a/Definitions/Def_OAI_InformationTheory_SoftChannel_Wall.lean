-- Prove2me | Definitions.Def_OAI_InformationTheory_SoftChannel_Wall
-- name    : OAI_InformationTheory_SoftChannel_Wall
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T14:51:36.896139+00:00
-- url     : https://prove2.me/theorems/b869ed4b-291c-4326-8600-4e546f9e78e2
-- title:
--   Wall quantities for the joining argument
-- statement:
--   These notions belong to a formal proof of sharp information inequalities for soft channels on the Boolean cube. For $g:\{0,1\}^n\to[-1,1]$ let $h(v)=\log2-\psi(v)$, where $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$, so $h(v)$ is the entropy in nats of a random sign with mean $v$. The information of $g$ is $I(g)=h(\mathbb Eg)-\mathbb Eh(g)$, and $T_\rho$ is the noise operator with correlation $\rho$. The main results are the soft contraction $I(T_\rho g)\le\psi(|\rho|\,\psi^{-1}(I(g)))$ and its attainment by scaled dictators. Further results identify $I(T_\rho g)$ with a mutual information and give the Courtade–Kumar bound of $1-H(\varepsilon)$ bits for Boolean functions. The last is the sharp production inequality $r(I(g))\le\mathcal D(g)$, where $\mathcal D(g)=\sum_i\mathbb E[\operatorname{artanh}(g)\,\partial_ig]$ and $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$.
--
--   For a mean $m$, a half-difference $d$ and an entropy level $e$:
--
--   1. **Artanh averages.** $A(m,d)=\frac12(\operatorname{artanh}(m+d)+\operatorname{artanh}(m-d))$, the half-difference $C(m,d)$, and the $m$-derivative of $A$.
--   2. **Auxiliary slope.** $\frac1{1-u^2}-\operatorname{artanh}(u)^2$.
--   3. **Wall demand.**
--   $$
--   W(m,d,e)=r\bigl(h(m)-e\bigr)-r\bigl(H_2(m,d)-e\bigr),
--   $$
--   with $H_2(m,d)=\frac12(h(m+d)+h(m-d))$, and its derivative in $m$.
--
--   The wall demand is the amount of dissipation that a split of the first coordinate must supply.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/SoftChannel/Wall.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/SoftChannel/Wall.lean by skeleton subtraction
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
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment__SoftChannel204
import Definitions.Def_OAI_InformationTheory_SoftChannel_Canonical
import Definitions.Def_OAI_InformationTheory_SoftChannel_Thinning
import Definitions.Def_OAI_InformationTheory_SoftChannel_Payment
import Definitions.Def_OAI_InformationTheory_SoftChannel_HighReserve
import Definitions.Def_OAI_InformationTheory_SoftChannel_RateSlope

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology
namespace LeanBlast.CourtadeKumar

def wallA (m d : ℝ) : ℝ := (Real.artanh (m+d)+Real.artanh (m-d))/2
def wallC (m d : ℝ) : ℝ := (Real.artanh (m+d)-Real.artanh (m-d))/2
def wallADeriv (m d : ℝ) : ℝ := (1/(1-(m+d)^2)-1/(1-(m-d)^2))/2

def entropySlopeAux (u : ℝ) : ℝ := 1/(1-u^2)-Real.artanh u^2

def wallDemand (m d e : ℝ) : ℝ := r (entropy m-e)-r (pairH m d-e)
def wallDemandDeriv (m d e : ℝ) : ℝ :=
  -rDeriv (entropy m-e)*Real.artanh m+rDeriv (pairH m d-e)*wallA m d

end LeanBlast.CourtadeKumar
end
end

end OAI


