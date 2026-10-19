-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise
-- name    : OAI_InformationTheory_BooleanNoise_FiniteNoise
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:09:06.885078+00:00
-- url     : https://prove2.me/theorems/d52290f0-1f57-4ad4-b01c-909660287d0a
-- title:
--   Basic identities for cube averages and the noise operator
-- statement:
--   The Boolean cube is $\{0,1\}^n$, written as functions $x:\{0,\dots,n-1\}\to\{\mathrm{false},\mathrm{true}\}$. $\mathbb{E}g=2^{-n}\sum_xg(x)$ is the uniform average, and $x^{\oplus i}$ is $x$ with coordinate $i$ flipped. Let $T_u$ be the noise operator with kernel $K_u(x,y)=\prod_i\bigl(\frac{1+u}{2}$ or $\frac{1-u}{2}\bigr)$, according as $x_i=y_i$ or not. The following identities hold.
--
--   1. The cube has $2^n>0$ vertices. The average of a constant is that constant, and averaging is additive.
--   2. Each row of the kernel sums to one: $\sum_yK_u(x,y)=1$. Hence $T_u$ fixes constants.
--   3. At $u=0$: $K_0(x,y)=2^{-n}$, so
--   $$
--   T_0g=\mathbb{E}g .
--   $$
--   4. At $u=1$: $K_1(x,y)=\mathbf 1[x=y]$, so $T_1g=g$.
--
--   $T_u$ interpolates between the full average ($u=0$) and the identity ($u=1$). These endpoint values anchor the noise semigroup arguments.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/FiniteNoise.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/FiniteNoise.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CourtadeKumar mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model__CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement__CourtadeKumar
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators

noncomputable section

universe u

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

@[simp] theorem card_cube (n : ℕ) : Fintype.card (Cube n) = 2 ^ n :=
  LeanBlast.GotsmanLinial.card_cube n

theorem cube_denominator_pos (n : ℕ) : 0 < (2 : ℝ) ^ n := by positivity

@[simp] theorem cubeAverage_const (n : ℕ) (c : ℝ) :
    cubeAverage (fun _ : Cube n => c) = c := by
  simp [cubeAverage]

theorem cubeAverage_add (g h : Cube n → ℝ) :
    cubeAverage (fun x => g x + h x) = cubeAverage g + cubeAverage h := by
  simp [cubeAverage, Finset.sum_add_distrib, add_div]

theorem noiseKernel_row_sum (u : ℝ) (x : Cube n) :
    ∑ y, noiseKernel u x y = 1 := by
  unfold noiseKernel
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
    if x i = b then (1 + u) / 2 else (1 - u) / 2)]
  have hfactor : ∀ i : Fin n,
      (∑ b : Bool, if x i = b then (1 + u) / 2 else (1 - u) / 2) = 1 := by
    intro i
    cases x i <;> simp <;> ring
  simp_rw [hfactor]
  simp

@[simp] theorem noiseOperator_const (u c : ℝ) (x : Cube n) :
    noiseOperator u (fun _ => c) x = c := by
  rw [noiseOperator, ← Finset.sum_mul, noiseKernel_row_sum, one_mul]

@[simp] theorem noiseKernel_zero (x y : Cube n) :
    noiseKernel 0 x y = 1 / (2 : ℝ) ^ n := by
  simp [noiseKernel, one_div]

@[simp] theorem noiseOperator_zero_correlation (g : Cube n → ℝ) (x : Cube n) :
    noiseOperator 0 g x = cubeAverage g := by
  simp only [noiseOperator, noiseKernel_zero, ← Finset.mul_sum]
  unfold cubeAverage
  ring

@[simp] theorem noiseKernel_one (x y : Cube n) :
    noiseKernel 1 x y = if x = y then 1 else 0 := by
  simp only [noiseKernel, add_self_div_two, sub_self, zero_div]
  rw [Fintype.prod_boole]
  simp only [← funext_iff]

@[simp] theorem noiseOperator_one (g : Cube n → ℝ) (x : Cube n) :
    noiseOperator 1 g x = g x := by
  simp [noiseOperator]

end LeanBlast.CourtadeKumar

end

end OAI


