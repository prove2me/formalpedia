-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveLogTrapezoid__SoftChannel204
-- name    : OAI_InformationTheory_BooleanNoise_PerspectiveLogTrapezoid__SoftChannel204
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T14:22:11.16818+00:00
-- url     : https://prove2.me/theorems/b93455b7-8546-4aa6-9bd4-56fe847ba77f
-- title:
--   A logarithmic trapezoid error and its derivative
-- statement:
--   These notions belong to a formal proof of sharp information inequalities for soft channels on the Boolean cube. For $g:\{0,1\}^n\to[-1,1]$ let $h(v)=\log2-\psi(v)$, where $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$, so $h(v)$ is the entropy in nats of a random sign with mean $v$. The information of $g$ is $I(g)=h(\mathbb Eg)-\mathbb Eh(g)$, and $T_\rho$ is the noise operator with correlation $\rho$. The main results are the soft contraction $I(T_\rho g)\le\psi(|\rho|\,\psi^{-1}(I(g)))$ and its attainment by scaled dictators. Further results identify $I(T_\rho g)$ with a mutual information and give the Courtade–Kumar bound of $1-H(\varepsilon)$ bits for Boolean functions. The last is the sharp production inequality $r(I(g))\le\mathcal D(g)$, where $\mathcal D(g)=\sum_i\mathbb E[\operatorname{artanh}(g)\,\partial_ig]$ and $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$.
--
--   For real $q,w$ define
--   $$
--   G(q,w)=(1+w-2q)\bigl(\log(1-q)-\log(w-q)\bigr)+(1+w)\log w,
--   $$
--   together with the expression
--   $$
--   G'(q,w)=\log(1-q)-\log(w-q)-\frac{1+w-2q}{w-q}+\log w+\frac{1+w}{w},
--   $$
--   which is the derivative of $G$ in $w$ wherever the logarithms are taken at positive arguments.
--
--   This function measures the error of a trapezoid-type comparison for logarithms. Its sign is used in the perspective inequalities of the curvature analysis.
--
--   **Formalization Note** That $G'$ is the derivative is proved separately. Lean's conventions for $\log$ and division apply outside the intended domain $q<1$, $w>q$, $w>0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/PerspectiveLogTrapezoid.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/PerspectiveLogTrapezoid.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace LeanBlast.CourtadeKumar

 def trapezoidGap (q w : ℝ) : ℝ :=
  (1 + w - 2 * q) * (Real.log (1 - q) - Real.log (w - q)) +
    (1 + w) * Real.log w

 def trapezoidGapDeriv (q w : ℝ) : ℝ :=
  Real.log (1 - q) - Real.log (w - q) - (1 + w - 2 * q) / (w - q) +
    Real.log w + (1 + w) / w

end LeanBlast.CourtadeKumar

end

end OAI


