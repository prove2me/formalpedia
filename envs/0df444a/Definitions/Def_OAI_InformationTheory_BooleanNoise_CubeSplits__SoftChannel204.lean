-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits__SoftChannel204
-- name    : OAI_InformationTheory_BooleanNoise_CubeSplits__SoftChannel204
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T14:09:14.757302+00:00
-- url     : https://prove2.me/theorems/9b15f964-1707-4a0d-a6b8-d5b083fbb523
-- title:
--   Restricting cube functions along the first coordinate
-- statement:
--   These notions belong to a formal proof of sharp information inequalities for soft channels on the Boolean cube. For $g:\{0,1\}^n\to[-1,1]$ let $h(v)=\log2-\psi(v)$, where $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$, so $h(v)$ is the entropy in nats of a random sign with mean $v$. The information of $g$ is $I(g)=h(\mathbb Eg)-\mathbb Eh(g)$, and $T_\rho$ is the noise operator with correlation $\rho$. The main results are the soft contraction $I(T_\rho g)\le\psi(|\rho|\,\psi^{-1}(I(g)))$ and its attainment by scaled dictators. Further results identify $I(T_\rho g)$ with a mutual information and give the Courtade–Kumar bound of $1-H(\varepsilon)$ bits for Boolean functions. The last is the sharp production inequality $r(I(g))\le\mathcal D(g)$, where $\mathcal D(g)=\sum_i\mathbb E[\operatorname{artanh}(g)\,\partial_ig]$ and $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$.
--
--   The Boolean cube is $\{0,1\}^n$, written as functions $x:\{0,\dots,n-1\}\to\{\mathrm{false},\mathrm{true}\}$. $\mathbb{E}g=2^{-n}\sum_xg(x)$ is the uniform average, and $x^{\oplus i}$ is $x$ with coordinate $i$ flipped. For $g$ on $\{0,1\}^{n+1}$ and $b\in\{0,1\}$, let $g_b(x)=g(b,x)$.
--
--   1. **Splitting.** $\{0,1\}\times\{0,1\}^n\cong\{0,1\}^{n+1}$, so
--   $$
--   \sum_xg(x)=\sum_xg_1(x)+\sum_xg_0(x),\qquad \mathbb{E}g=\frac{\mathbb{E}g_1+\mathbb{E}g_0}{2}=\mathbb{E}\,\frac{g_1+g_0}{2}.
--   $$
--   2. **Averages.** Averaging commutes with division by a constant and with taking halves of sums. The pair mean $m=\frac{g_1+g_0}2$ and half-difference $d=\frac{g_1-g_0}2$ satisfy $m\pm d=g_{1/0}$ and $\mathbb{E}m=\mathbb{E}g$.
--   3. **Variance.** $\mathrm{Var}(g)=\mathbb{E}(g-\mathbb{E}g)^2$.
--   4. **Dimension zero.** On $\{0,1\}^0$ the average is the single value. Both the information deficit and the dissipation vanish there.
--
--   These identities drive induction on the dimension: a function on $n+1$ coordinates is analysed through its two restrictions to $n$ coordinates.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/CubeSplits.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/CubeSplits.lean by skeleton subtraction
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

namespace OAI

open scoped BigOperators

noncomputable section

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

def cubeSplitEquiv (n : ℕ) : Bool × Cube n ≃ Cube (n + 1) where
  toFun z := Fin.cases z.1 z.2
  invFun x := (x 0, fun i => x i.succ)
  left_inv z := by cases z; rfl
  right_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem sum_cube_split (g : Cube (n + 1) → ℝ) :
    (∑ x, g x) = (∑ x, restrict g true x) + ∑ x, restrict g false x := by
  rw [← (cubeSplitEquiv n).sum_comp g, Fintype.sum_prod_type, Fintype.sum_bool]
  rfl

theorem cubeAverage_split (g : Cube (n + 1) → ℝ) :
    cubeAverage g = (cubeAverage (restrict g true) + cubeAverage (restrict g false)) / 2 := by
  unfold cubeAverage
  rw [sum_cube_split, pow_succ]
  have hN : (2 : ℝ) ^ n ≠ 0 := ne_of_gt (cube_denominator_pos n)
  field_simp

theorem cubeAverage_div (g : Cube n → ℝ) (c : ℝ) :
    cubeAverage (fun x => g x / c) = cubeAverage g / c := by
  simp only [cubeAverage, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  ring

theorem cubeAverage_half_sum (g h : Cube n → ℝ) :
    cubeAverage (fun x => (g x + h x) / 2) = (cubeAverage g + cubeAverage h) / 2 := by
  rw [cubeAverage_div, cubeAverage_add]

theorem cubeAverage_split_pair (g : Cube (n + 1) → ℝ) :
    cubeAverage g = cubeAverage (fun x => (restrict g true x + restrict g false x) / 2) := by
  rw [cubeAverage_half_sum, cubeAverage_split]

@[simp] theorem pairMean_add_halfDifference (g : Cube (n + 1) → ℝ) (x : Cube n) :
    pairMean g x + pairHalfDifference g x = restrict g true x := by
  unfold pairMean pairHalfDifference
  ring

@[simp] theorem pairMean_sub_halfDifference (g : Cube (n + 1) → ℝ) (x : Cube n) :
    pairMean g x - pairHalfDifference g x = restrict g false x := by
  unfold pairMean pairHalfDifference
  ring

@[simp] theorem cubeAverage_pairMean (g : Cube (n + 1) → ℝ) :
    cubeAverage (pairMean g) = cubeAverage g := by
  exact (cubeAverage_split_pair g).symm

def cubeVariance (g : Cube n → ℝ) : ℝ :=
  cubeAverage (fun x => (g x - cubeAverage g) ^ 2)

theorem cubeAverage_dim_zero (g : Cube 0 → ℝ) :
    cubeAverage g = g (fun i => Fin.elim0 i) := by
  have heq : g = fun _ => g (fun i => Fin.elim0 i) := by
    funext x
    congr 1
    exact Subsingleton.elim _ _
  rw [heq, cubeAverage_const]

@[simp] theorem informationDeficit_dim_zero (g : Cube 0 → ℝ) : informationDeficit g = 0 := by
  simp only [informationDeficit, entropyAverage, cubeAverage_dim_zero]
  ring

@[simp] theorem dissipation_dim_zero (g : Cube 0 → ℝ) : dissipation g = 0 := by
  simp [dissipation]

end LeanBlast.CourtadeKumar

end

end OAI


