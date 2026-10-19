-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment__SoftChannel204
-- name    : OAI_InformationTheory_BooleanNoise_Attainment__SoftChannel204
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T14:33:35.876604+00:00
-- url     : https://prove2.me/theorems/606686f1-2086-4f5b-bfe9-646c59e264af
-- title:
--   Vanishing information for constant and fully noisy functions
-- statement:
--   These notions belong to a formal proof of sharp information inequalities for soft channels on the Boolean cube. For $g:\{0,1\}^n\to[-1,1]$ let $h(v)=\log2-\psi(v)$, where $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$, so $h(v)$ is the entropy in nats of a random sign with mean $v$. The information of $g$ is $I(g)=h(\mathbb Eg)-\mathbb Eh(g)$, and $T_\rho$ is the noise operator with correlation $\rho$. The main results are the soft contraction $I(T_\rho g)\le\psi(|\rho|\,\psi^{-1}(I(g)))$ and its attainment by scaled dictators. Further results identify $I(T_\rho g)$ with a mutual information and give the Courtade–Kumar bound of $1-H(\varepsilon)$ bits for Boolean functions. The last is the sharp production inequality $r(I(g))\le\mathcal D(g)$, where $\mathcal D(g)=\sum_i\mathbb E[\operatorname{artanh}(g)\,\partial_ig]$ and $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$.
--
--   The Boolean cube is $\{0,1\}^n$, written as functions $x:\{0,\dots,n-1\}\to\{\mathrm{false},\mathrm{true}\}$. $\mathbb{E}g=2^{-n}\sum_xg(x)$ is the uniform average, and $x^{\oplus i}$ is $x$ with coordinate $i$ flipped. The information deficit of $g$ is $h(\mathbb{E}g)-\mathbb{E}h(g)$, where $h(v)=\log2-\psi(v)$ is the entropy of a sign with mean $v$, and $T_u$ is the noise operator. The following hold.
--
--   1. For a constant function $c$, $\mathbb{E}h(c)=h(c)$, and its information deficit is $0$.
--   2. For every correlation $u$, the deficit of $T_uc$ is $0$, since $T_u$ fixes constants.
--   3. For every $g$,
--   $$
--   h\bigl(\mathbb{E}\,T_0g\bigr)-\mathbb{E}\,h\bigl(T_0g\bigr)=0,
--   $$
--   because $T_0g$ is the constant $\mathbb{E}g$.
--
--   These trivial cases, without information or with complete noise, are the base cases of the information comparisons.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/Attainment.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/Attainment.lean by skeleton subtraction
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

namespace OAI

open scoped BigOperators

noncomputable section

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

@[simp] theorem entropyAverage_const (c : ℝ) :
    entropyAverage (fun _ : Cube n => c) = entropy c :=
  cubeAverage_const n (entropy c)

@[simp] theorem informationDeficit_const (c : ℝ) :
    informationDeficit (fun _ : Cube n => c) = 0 := by
  simp [informationDeficit]

@[simp] theorem informationDeficit_noise_const (u c : ℝ) :
    informationDeficit (noiseOperator u (fun _ : Cube n => c)) = 0 := by
  have h : noiseOperator u (fun _ : Cube n => c) = fun _ => c := by
    funext x
    exact noiseOperator_const u c x
  rw [h, informationDeficit_const]

@[simp] theorem informationDeficit_noise_zero (g : Cube n → ℝ) :
    informationDeficit (noiseOperator 0 g) = 0 := by
  have h : noiseOperator 0 g = fun _ => cubeAverage g := by
    funext x
    exact noiseOperator_zero_correlation g x
  rw [h, informationDeficit_const]

end LeanBlast.CourtadeKumar

end

end OAI


