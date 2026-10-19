-- Prove2me | Definitions.Def_OAI_InformationTheory_SoftChannel_HighReserve
-- name    : OAI_InformationTheory_SoftChannel_HighReserve
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T14:46:35.495504+00:00
-- url     : https://prove2.me/theorems/ac9ef512-cbfe-490c-adc4-2a36eba18d95
-- title:
--   Soft cutoff and the mean reserve
-- statement:
--   These notions belong to a formal proof of sharp information inequalities for soft channels on the Boolean cube. For $g:\{0,1\}^n\to[-1,1]$ let $h(v)=\log2-\psi(v)$, where $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$, so $h(v)$ is the entropy in nats of a random sign with mean $v$. The information of $g$ is $I(g)=h(\mathbb Eg)-\mathbb Eh(g)$, and $T_\rho$ is the noise operator with correlation $\rho$. The main results are the soft contraction $I(T_\rho g)\le\psi(|\rho|\,\psi^{-1}(I(g)))$ and its attainment by scaled dictators. Further results identify $I(T_\rho g)$ with a mutual information and give the Courtade–Kumar bound of $1-H(\varepsilon)$ bits for Boolean functions. The last is the sharp production inequality $r(I(g))\le\mathcal D(g)$, where $\mathcal D(g)=\sum_i\mathbb E[\operatorname{artanh}(g)\,\partial_ig]$ and $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$.
--
--   1. **Soft cutoff.** $s_*=\psi(77/100)$.
--   2. **Centred rate.** $\bigl(I-(\log2-\tfrac12)\bigr)\bigl(r'(I)-2\bigr)-\bigl(r(I)-2I\bigr)$.
--   3. **Mean reserve.** For $|m|<1$ and $0\le I<h(m)$,
--   $$
--   R(m,I)=2I+(1-m^2)\,L\Bigl(\frac{h(m)-I}{1-m^2}\Bigr),
--   $$
--   where $L(x)=r(\log2-x)-2(\log2-x)$.
--
--   Above the soft cutoff, the mean reserve dominates $r(I)$ and is itself bounded by the dissipation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/SoftChannel/HighReserve.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/SoftChannel/HighReserve.lean by skeleton subtraction
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

namespace OAI

section

noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace LeanBlast.CourtadeKumar

def softCutoff : ℝ := psi (77/100)
def centeredRate (I : ℝ) : ℝ := (I-(ell-1/2))*(rDeriv I-2)-rGap I

def meanReserve (m I : ℝ) : ℝ :=
  2*I+(1-m^2)*L ((entropy m-I)/(1-m^2))

end LeanBlast.CourtadeKumar
end
end

end OAI


