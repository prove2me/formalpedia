-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits
-- name    : OAI_InformationTheory_BooleanNoise_CubeSplits
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:32:38.278586+00:00
-- url     : https://prove2.me/theorems/3d1d265f-8068-42ea-8b97-f032d0e7c552
-- title:
--   Splitting the cube $\{0,1\}^{n+1}$ along the first coordinate
-- statement:
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
-- (upload_full_project.md Phase 3): Definitions bundle for the CourtadeKumar mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model__CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement__CourtadeKumar
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_ComparisonEstimates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity
import Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow

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


