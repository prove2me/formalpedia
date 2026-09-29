-- Prove2me | Definitions.Def_GeneralCK_information
-- name    : GeneralCK_information
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T19:31:32.969184+00:00
-- url     : https://prove2.me/theorems/23c78214-53b1-41df-af46-2aabc48facc9
-- title:
--   Uniform cube weight, Boolean mean, and channel posterior
-- statement:
--   For dimension $n$, define the uniform cube weight $w_n=2^{-n}$. For a Boolean function $f$, define its mean $m_f=w_n\sum_x\mathbf1_{f(x)=1}$ and the channel posterior expression $t_{f,p}(y)=\sum_x\mathbf1_{f(x)=1}K_p(x,y)$. In the probability range $0\le p\le1$, these are respectively $\Pr[f(X)=1]$ and $\Pr[f(X)=1\mid Y=y]$ for uniform input. The expressions are defined for all real $p$ and support the finite conditional-entropy identity used by the mission. Here $K_p(x,y)$ is the product over coordinates of $1-p$ for equal coordinates and $p$ for unequal coordinates.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/InformationIdentity.lean#L6-L12

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_statement

open scoped BigOperators

namespace GeneralCK.Information
open scoped BigOperators

noncomputable def cubeWeight (n : ℕ) : ℝ := (2 : ℝ) ^ (-(n : ℤ))

noncomputable def posterior {n : ℕ} (f : Cube n → Bool) (p : ℝ) (y : Cube n) : ℝ :=
  ∑ x, if f x = true then noiseKernel p x y else 0

noncomputable def meanIndicator {n : ℕ} (f : Cube n → Bool) : ℝ :=
  cubeWeight n * ∑ x, if f x = true then (1 : ℝ) else 0







































end GeneralCK.Information


