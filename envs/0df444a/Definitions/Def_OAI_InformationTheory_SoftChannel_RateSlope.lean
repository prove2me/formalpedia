-- Prove2me | Definitions.Def_OAI_InformationTheory_SoftChannel_RateSlope
-- name    : OAI_InformationTheory_SoftChannel_RateSlope
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T14:48:33.831405+00:00
-- url     : https://prove2.me/theorems/af0db4e6-2a81-4008-906e-297ed0082bce
-- title:
--   A slope polynomial with a Bernstein certificate
-- statement:
--   These notions belong to a formal proof of sharp information inequalities for soft channels on the Boolean cube. For $g:\{0,1\}^n\to[-1,1]$ let $h(v)=\log2-\psi(v)$, where $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$, so $h(v)$ is the entropy in nats of a random sign with mean $v$. The information of $g$ is $I(g)=h(\mathbb Eg)-\mathbb Eh(g)$, and $T_\rho$ is the noise operator with correlation $\rho$. The main results are the soft contraction $I(T_\rho g)\le\psi(|\rho|\,\psi^{-1}(I(g)))$ and its attainment by scaled dictators. Further results identify $I(T_\rho g)$ with a mutual information and give the Courtade–Kumar bound of $1-H(\varepsilon)$ bits for Boolean functions. The last is the sharp production inequality $r(I(g))\le\mathcal D(g)$, where $\mathcal D(g)=\sum_i\mathbb E[\operatorname{artanh}(g)\,\partial_ig]$ and $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$.
--
--   1. **Slope polynomials.** $T(z)=1+\frac z3+\frac{z^2}5$ and
--   $$
--   P(z)=2(1-z)^2T(z)^2\bigl((1-z)T(z)+1\bigr)-N(z),
--   $$
--   where $N$ is the curvature numerator polynomial.
--   2. **Certificate.** Ten positive rational Bernstein coefficients for $P$, starting $\frac83,\frac{512}{225},\frac{334}{175},\dots$.
--
--   Positivity of $P$ on $[0,1]$ bounds the slope of the rate function used in the wall comparison.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/SoftChannel/RateSlope.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/SoftChannel/RateSlope.lean by skeleton subtraction
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

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace LeanBlast.CourtadeKumar

def slopeT (z : ℝ) : ℝ := 1+z/3+z^2/5
def slopePolynomial (z : ℝ) : ℝ :=
  2*(1-z)^2*slopeT z^2*((1-z)*slopeT z+1)-curvatureN z
def RateSlope_slopeBernstein : Fin 10 → ℝ :=
  ![(8/3:ℝ),
    (512/225:ℝ),
    (334/175:ℝ),
    (5861/3750:ℝ),
    (93828088/75796875:ℝ),
    (102326753/109484375:ℝ),
    (8980934524/13685546875:ℝ),
    (71721266999/175957031250:ℝ),
    (9531748404/48876953125:ℝ),
    (18341751592/733154296875:ℝ)]

end LeanBlast.CourtadeKumar
end
end

end OAI


