-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveCalculus__SoftChannel204
-- name    : OAI_InformationTheory_BooleanNoise_PerspectiveCalculus__SoftChannel204
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T14:23:38.628281+00:00
-- url     : https://prove2.me/theorems/c677554a-ef9b-4f5f-9d5c-a7f41d7a1a1a
-- title:
--   Log-corrected perspectives and their derivatives
-- statement:
--   These notions belong to a formal proof of sharp information inequalities for soft channels on the Boolean cube. For $g:\{0,1\}^n\to[-1,1]$ let $h(v)=\log2-\psi(v)$, where $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$, so $h(v)$ is the entropy in nats of a random sign with mean $v$. The information of $g$ is $I(g)=h(\mathbb Eg)-\mathbb Eh(g)$, and $T_\rho$ is the noise operator with correlation $\rho$. The main results are the soft contraction $I(T_\rho g)\le\psi(|\rho|\,\psi^{-1}(I(g)))$ and its attainment by scaled dictators. Further results identify $I(T_\rho g)$ with a mutual information and give the Courtade–Kumar bound of $1-H(\varepsilon)$ bits for Boolean functions. The last is the sharp production inequality $r(I(g))\le\mathcal D(g)$, where $\mathcal D(g)=\sum_i\mathbb E[\operatorname{artanh}(g)\,\partial_ig]$ and $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$.
--
--   For a function $f:\mathbb{R}\to\mathbb{R}$ and real $x,C,v$ define the log-corrected perspective
--   $$
--   P_f(x,C,v)=v\,f\Bigl(\frac xv\Bigr)-C\,v\log v,
--   $$
--   and, given candidate derivatives $f'$ and $f''$, the expressions
--   $$
--   \partial_vP=f\Bigl(\frac xv\Bigr)-\frac xv\,f'\Bigl(\frac xv\Bigr)-C(\log v+1),\qquad \partial_v^2P=\frac{\bigl(\frac xv\bigr)^2f''\bigl(\frac xv\bigr)-C}{v}.
--   $$
--
--   The perspective $v f(x/v)$ of a convex function is jointly convex. The logarithmic correction $-Cv\log v$ adjusts the curvature in $v$. These formulas are the calculus behind convexity arguments in the induction on dimension.
--
--   **Formalization Note** The derivative expressions are definitions; their validity as derivatives, for $v>0$ and differentiable $f$, is proved separately.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/PerspectiveCalculus.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/PerspectiveCalculus.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open Set

namespace LeanBlast.CourtadeKumar

def logCorrectedPerspective (f : ℝ → ℝ) (x C v : ℝ) : ℝ :=
  v * f (x / v) - C * v * Real.log v

def logCorrectedPerspectiveDeriv (f f' : ℝ → ℝ) (x C v : ℝ) : ℝ :=
  f (x / v) - (x / v) * f' (x / v) - C * (Real.log v + 1)

def logCorrectedPerspectiveSecondDeriv (f'' : ℝ → ℝ) (x C v : ℝ) : ℝ :=
  ((x / v) ^ 2 * f'' (x / v) - C) / v

end LeanBlast.CourtadeKumar

end

end OAI


