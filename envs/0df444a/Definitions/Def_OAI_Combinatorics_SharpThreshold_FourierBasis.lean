-- Prove2me | Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
-- name    : OAI_Combinatorics_SharpThreshold_FourierBasis
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:03:23.795751+00:00
-- url     : https://prove2.me/theorems/8c7f4208-0642-403a-94f9-846ee4dfb718
-- title:
--   The $p$-biased Fourier–Walsh basis
-- statement:
--   Let $\iota$ be a finite set of coordinates and $p\in\mathbb{R}$. A point of the cube is $x\in\{0,1\}^\iota$, with $p$-biased weight $w_p(x)=\prod_ip^{[x_i]}(1-p)^{1-[x_i]}$.
--
--   1. The one-dimensional character is
--   $$
--   \chi_p(b)=\frac{[b]-p}{\sqrt{p(1-p)}} ,
--   $$
--      so $\chi_p(1)=(1-p)/\sqrt{p(1-p)}$ and $\chi_p(0)=-p/\sqrt{p(1-p)}$.
--   2. For $S\subseteq\iota$ the character is $\chi_S(x)=\prod_{i\in S}\chi_p(x_i)$, with $\chi_\emptyset=1$.
--   3. The Fourier coefficient of $g:\{0,1\}^\iota\to\mathbb{R}$ is $\hat g(S)=\sum_xw_p(x)g(x)\chi_S(x)$.
--
--   For $0<p<1$ the characters form an orthonormal basis of $L^2(w_p)$. This is the basis in which the low-degree part of a graph property is analyzed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/FourierBasis.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/FourierBasis.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SharpThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit

namespace OAI

universe u v

noncomputable section

open scoped BigOperators

namespace Problem313.BiasedFourier

variable {ι : Type u} [Fintype ι]

def scalarWeight (p : ℝ) (b : Bool) : ℝ :=
  if b = true then p else 1 - p

def weight (p : ℝ) (x : ι → Bool) : ℝ :=
  ∏ i, scalarWeight p (x i)

def chi (p : ℝ) (b : Bool) : ℝ :=
  ((if b = true then (1 : ℝ) else 0) - p) / Real.sqrt (p * (1 - p))

def char (p : ℝ) (S : Finset ι) (x : ι → Bool) : ℝ :=
  ∏ i ∈ S, chi p (x i)

def coeff (p : ℝ) (g : (ι → Bool) → ℝ) (S : Finset ι) : ℝ := by
  classical
  exact ∑ x, weight p x * g x * char p S x

@[simp] theorem scalarWeight_false (p : ℝ) : scalarWeight p false = 1 - p := rfl
@[simp] theorem scalarWeight_true (p : ℝ) : scalarWeight p true = p := rfl
@[simp] theorem chi_false (p : ℝ) :
    chi p false = -p / Real.sqrt (p * (1 - p)) := by simp [chi]
@[simp] theorem chi_true (p : ℝ) :
    chi p true = (1 - p) / Real.sqrt (p * (1 - p)) := rfl
omit [Fintype ι] in
@[simp] theorem char_empty (p : ℝ) (x : ι → Bool) : char p ∅ x = 1 := by
  simp [char]

end Problem313.BiasedFourier

end

end OAI


