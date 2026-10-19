-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_NormalizedPair__SoftChannel204
-- name    : OAI_InformationTheory_BooleanNoise_NormalizedPair__SoftChannel204
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T14:19:24.934854+00:00
-- url     : https://prove2.me/theorems/f49043b6-75cd-4245-87e6-7a75f3fc388b
-- title:
--   Moments of a two-point relative perturbation
-- statement:
--   These notions belong to a formal proof of sharp information inequalities for soft channels on the Boolean cube. For $g:\{0,1\}^n\to[-1,1]$ let $h(v)=\log2-\psi(v)$, where $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$, so $h(v)$ is the entropy in nats of a random sign with mean $v$. The information of $g$ is $I(g)=h(\mathbb Eg)-\mathbb Eh(g)$, and $T_\rho$ is the noise operator with correlation $\rho$. The main results are the soft contraction $I(T_\rho g)\le\psi(|\rho|\,\psi^{-1}(I(g)))$ and its attainment by scaled dictators. Further results identify $I(T_\rho g)$ with a mutual information and give the Courtade–Kumar bound of $1-H(\varepsilon)$ bits for Boolean functions. The last is the sharp production inequality $r(I(g))\le\mathcal D(g)$, where $\mathcal D(g)=\sum_i\mathbb E[\operatorname{artanh}(g)\,\partial_ig]$ and $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$.
--
--   For $a,b\in\mathbb{R}$ and $j\in\mathbb{N}$ define
--   $$
--   R_j(a,b)=\frac{1+a}{2}\Bigl(\frac{b}{1+a}\Bigr)^{2j}+\frac{1-a}{2}\Bigl(\frac{b}{1-a}\Bigr)^{2j},\qquad N_j(a,b)=\begin{cases}1,&j=0,\\ \dfrac{R_j(a,b)}{1-a^2},&j\ge1.\end{cases}
--   $$
--
--   $R_j$ is the $2j$-th moment of the relative perturbation $b/(1\pm a)$ under the sign law with mean $a$. Normalized moments organize the series expansion of the pair entropy gap $h(a)-\frac{h(a+b)+h(a-b)}2$ in powers of $b$.
--
--   **Formalization Note** Lean's convention $x/0=0$ applies when $a=\pm1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/NormalizedPair.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/NormalizedPair.lean by skeleton subtraction
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

namespace OAI

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

noncomputable def rawPairMoment (a b : ℝ) (j : ℕ) : ℝ :=
  (1 + a) / 2 * (b / (1 + a)) ^ (2 * j) +
    (1 - a) / 2 * (b / (1 - a)) ^ (2 * j)

noncomputable def normalizedPairMoment (a b : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 1 else rawPairMoment a b j / (1 - a ^ 2)

@[simp]
theorem normalizedPairMoment_zero (a b : ℝ) : normalizedPairMoment a b 0 = 1 := by
  simp [normalizedPairMoment]

@[simp]
theorem normalizedPairMoment_succ (a b : ℝ) (j : ℕ) :
    normalizedPairMoment a b (j + 1) = rawPairMoment a b (j + 1) / (1 - a ^ 2) := by
  simp [normalizedPairMoment]

end LeanBlast.CourtadeKumar

end OAI


