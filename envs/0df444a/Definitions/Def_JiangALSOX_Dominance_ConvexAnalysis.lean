-- Prove2me | Definitions.Def_JiangALSOX_Dominance_ConvexAnalysis
-- name    : JiangALSOX_Dominance_ConvexAnalysis
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:04:48.980555+00:00
-- url     : https://prove2.me/theorems/6207304f-8650-4a94-b22c-de06207ca21c
-- title:
--   Normal cones, partial extended subdifferentials and complementarity
-- statement:
--   For $X\subseteq\mathbb R^n$, its normal cone at $x\in X$ is
--   $$N_X(x)=\{h: h^\top(y-x)\le0\text{ for every }y\in X\};$$
--   it is empty for $x\notin X$. For a possibly partially defined extended-valued function $f$, a subgradient at $x$ is a vector $h$ such that $f(x)=a$ is a finite real number and
--   $$a+h^\top(y-x)\le f(y)$$
--   for every $y$ where $f(y)$ is defined, including infinite values. The subdifferential is empty if $f(x)$ is undefined or infinite. This explicitly distinguishes the domain of a signed expectation from points where its positive and negative parts are both infinite.
--
--   The relation $a\perp b$ means $a\ge0$, $b\ge0$, and $ab=0$. These are independent convex-analysis and scalar definitions, with no assertion of existence of a multiplier or an optimizer.
-- source:
--   Nan Jiang and Weijun Xie, ALSO-X and ALSO-X+: Better Convex Approximations for Chance Constrained Programs, arXiv:2012.04763v4 (14 October 2021), https://arxiv.org/abs/2012.04763v4, p. 5, notation; p. 42, subdifferentials and complementarity in (KKT1)–(KKT2)

import Mathlib

namespace JiangALSOX.Dominance

def normalCone {n : ℕ} (X : Set (Fin n → ℝ)) (x : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {h | x ∈ X ∧ ∀ y ∈ X, dotProduct h (y - x) ≤ 0}

def partialSubdiff {n : ℕ} (f : (Fin n → ℝ) → Option EReal)
    (x : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {h | ∃ a : ℝ, f x = some (a : EReal) ∧
    ∀ (y : Fin n → ℝ) (b : EReal), f y = some b →
      ((a + dotProduct h (y - x) : ℝ) : EReal) ≤ b}

def complementary (a b : ℝ) : Prop := 0 ≤ a ∧ 0 ≤ b ∧ a * b = 0

end JiangALSOX.Dominance


