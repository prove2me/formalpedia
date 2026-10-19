-- Prove2me | Definitions.Def_OAI_InformationTheory_SoftChannel_Payment
-- name    : OAI_InformationTheory_SoftChannel_Payment
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T14:40:47.532139+00:00
-- url     : https://prove2.me/theorems/fb09d490-725d-4251-a5c9-c4661c3cbf3b
-- title:
--   Thinning a pair toward a common output
-- statement:
--   These notions belong to a formal proof of sharp information inequalities for soft channels on the Boolean cube. For $g:\{0,1\}^n\to[-1,1]$ let $h(v)=\log2-\psi(v)$, where $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$, so $h(v)$ is the entropy in nats of a random sign with mean $v$. The information of $g$ is $I(g)=h(\mathbb Eg)-\mathbb Eh(g)$, and $T_\rho$ is the noise operator with correlation $\rho$. The main results are the soft contraction $I(T_\rho g)\le\psi(|\rho|\,\psi^{-1}(I(g)))$ and its attainment by scaled dictators. Further results identify $I(T_\rho g)$ with a mutual information and give the Courtade–Kumar bound of $1-H(\varepsilon)$ bits for Boolean functions. The last is the sharp production inequality $r(I(g))\le\mathcal D(g)$, where $\mathcal D(g)=\sum_i\mathbb E[\operatorname{artanh}(g)\,\partial_ig]$ and $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$.
--
--   For $c,d$ and a thinning parameter $l\in(0,1]$:
--
--   1. **Pair entropy.** $H_2(c,d)=\frac12\bigl(h(c+d)+h(c-d)\bigr)$.
--   2. **Thinned point and information.** $x_l=1-l(1-c)$, and
--   $$
--   I_l=h(x_l)-l\,H_2(c,d),\qquad J_l=H_2(x_l,ld)-l\,H_2(c,d),
--   $$
--   with their derivatives in $l$, and auxiliary terms $\log2-\log(1+x_l)$ and $-\frac12\log\bigl(1-(ld)^2/(1+x_l)^2\bigr)$.
--   3. **Normalized demand.** $\bigl(r(I_l)-r(J_l)\bigr)/l$ and its derivative in $l$.
--
--   At $l=1$ the demand is $r$ of the pair entropy gap. Its monotonicity in $l$ is the payment estimate.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/SoftChannel/Payment.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/SoftChannel/Payment.lean by skeleton subtraction
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

namespace OAI

section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace LeanBlast.CourtadeKumar
open SoftChannel204

def pairH (c d : ℝ) : ℝ := (entropy (c+d)+entropy (c-d))/2
def thinX (c l : ℝ) : ℝ := 1-l*(1-c)
def thinI (c d l : ℝ) : ℝ := entropy (thinX c l)-l*pairH c d
def thinJ (c d l : ℝ) : ℝ := pairH (thinX c l) (l*d)-l*pairH c d

def thinIDeriv (c d l : ℝ) : ℝ := (1-c)*Real.artanh (thinX c l)-pairH c d
def thinJDeriv (c d l : ℝ) : ℝ :=
  ((1-(c+d))*Real.artanh (thinX (c+d) l)+(1-(c-d))*Real.artanh (thinX (c-d) l))/2-pairH c d

def thinA (c l : ℝ) : ℝ := ell-Real.log (1+thinX c l)
def thinK (c d l : ℝ) : ℝ := -(1/2:ℝ)*Real.log (1-(l*d)^2/(1+thinX c l)^2)

def normalizedDemand (c d l : ℝ) : ℝ := (r (thinI c d l)-r (thinJ c d l))/l

def normalizedDemandDeriv (c d l : ℝ) : ℝ :=
  ((rDeriv (thinI c d l)*thinIDeriv c d l-rDeriv (thinJ c d l)*thinJDeriv c d l)*l-
    (r (thinI c d l)-r (thinJ c d l)))/l^2

end LeanBlast.CourtadeKumar
end
end

end OAI


