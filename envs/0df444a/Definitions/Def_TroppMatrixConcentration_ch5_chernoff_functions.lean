-- Prove2me | Definitions.Def_TroppMatrixConcentration_ch5_chernoff_functions
-- name    : TroppMatrixConcentration_ch5_chernoff_functions
-- status  : Definition
-- author  : @tc
-- created : 2026-10-07T13:47:56.358111+00:00
-- url     : https://prove2.me/theorems/8af7e651-139d-4ac0-b6c1-94470e9f1f56
-- title:
--   Matrix Chernoff scalar transform coefficient and tail functions
-- statement:
--   Define $c(L,\theta)=(e^{\theta L}-1)/L$ for $L\ne0$, and $c(0,\theta)=\theta$ by continuous extension. Define the lower-tail expression
--   $$d\left[e^{-\varepsilon}/(1-\varepsilon)^{1-\varepsilon}\right]^{a/L}$$
--   and the upper-tail expression
--   $$d\left[e^\varepsilon/(1+\varepsilon)^{1+\varepsilon}\right]^{a/L}$$
--   when $L\ne0$, using real powers. When $L=0$, define both tail expressions to be $d$. The theorem statements restrict the lower-tail deviation to $0\le\varepsilon<1$ and the upper-tail deviation to $\varepsilon\ge0$, so their bases are positive. They impose $L\ge0$ and positive dimension. At $L=0$ all permitted summands vanish, so the relevant non-strict relative tail events occur at zero. These scalar definitions introduce no probabilistic assumptions or conclusions.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Theorem 5.1.1, equations (5.1.5–6), printed p. 60; Lemma 5.4.1, printed p. 70.

import Definitions.Def_TroppMatrixConcentration_probability
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
namespace TroppMatrixConcentration

def chernoffCgfCoefficient (L θ : ℝ) : ℝ :=
  if L = 0 then θ else (Real.exp (θ * L) - 1) / L

def chernoffLowerTail (dimension : ℕ) (a L ε : ℝ) : ℝ :=
  if L = 0 then (dimension : ℝ)
  else (dimension : ℝ) * Real.rpow
    (Real.exp (-ε) / Real.rpow (1 - ε) (1 - ε)) (a / L)

def chernoffUpperTail (dimension : ℕ) (a L ε : ℝ) : ℝ :=
  if L = 0 then (dimension : ℝ)
  else (dimension : ℝ) * Real.rpow
    (Real.exp ε / Real.rpow (1 + ε) (1 + ε)) (a / L)

end TroppMatrixConcentration


