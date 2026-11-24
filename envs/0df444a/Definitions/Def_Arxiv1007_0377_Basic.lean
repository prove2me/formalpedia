-- Prove2me | Definitions.Def_Arxiv1007_0377_Basic
-- name    : Arxiv1007_0377_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T23:59:37.697513+00:00
-- url     : https://prove2.me/theorems/66014f5e-106e-4bb0-8339-9540409b6475
-- title:
--   Solution branches of $N^2=\epsilon\mu$ and the switching conditions (6), (7)
-- statement:
--   Objects of the main text of Hickey, Akyurtlu and Kussow (2010), eqs. (1), (2), (6) and (7), PDF p. 2.
--
--   A scalar, isotropic, homogeneous medium has, at a given real frequency, a complex relative permittivity $\epsilon=\epsilon_r+i\epsilon_i$ and a complex relative permeability $\mu=\mu_r+i\mu_i$. Its complex refractive index $N=n+i\kappa$ ($n,\kappa\in\mathbb{R}$) satisfies $N^2=\epsilon\mu$.
--
--   1. **Real and imaginary parts of $\epsilon\mu$.** $A=\epsilon_r\mu_r-\epsilon_i\mu_i=\operatorname{Re}(\epsilon\mu)$ and $B=\epsilon_r\mu_i+\epsilon_i\mu_r=\operatorname{Im}(\epsilon\mu)$.
--   2. **The quartic (eq. 1).** The polynomial $n^4-\left(\tfrac{B}{2}\right)^2-A\,n^2$, with complex coefficients, in the indeterminate $n$.
--   3. **The radicand (eqs. 2, 6).** $R=\epsilon_r\mu_r-\epsilon_i\mu_i+|\epsilon||\mu|$.
--   4. **The real branches (eq. 2).** $n_\pm=\pm\sqrt{R}/\sqrt2$.
--   5. **Condition (6).** $R=0$.
--   6. **Condition (7).** $\epsilon_r=-\epsilon_i\mu_r/\mu_i$.
--
--   **Formalization Note** $\epsilon$ and $\mu$ are complex numbers. Where the paper treats them as functions of frequency (the derivative of $n_+$), the statement takes maps $\mathbb{R}\to\mathbb{C}$ and evaluates these definitions pointwise. Condition (7) is only meaningful for $\mu_i\neq0$, and every statement that uses it assumes $\mu_i\neq0$. In Lean, division by $0$ returns $0$.
-- source:
--   Hickey, Akyurtlu and Kussow, Relationship between the Kramers-Kronig relations and negative index of refraction, arXiv:1007.0377v2 (2010), https://arxiv.org/abs/1007.0377, main text (unsectioned), eqs. (1), (2), (6), (7), PDF p. 2

import Mathlib

/-!
Hickey, Akyurtlu and Kussow, *Relationship between the Kramers-Kronig relations and negative
index of refraction*, arXiv:1007.0377v2 (2010): the solution branches of `N² = ε μ` for a scalar
medium with complex permittivity `ε = ε_r + i ε_i` and permeability `μ = μ_r + i μ_i`
(eqs. (1), (2), (6), (7), PDF p. 2).
-/

open Polynomial

noncomputable section

namespace Arxiv1007_0377

/-- Eq. (1), PDF p. 2: the combination `ε_r μ_r - ε_i μ_i` (the real part of `ε μ`). -/
def epsMuRe (ε μ : ℂ) : ℝ := ε.re * μ.re - ε.im * μ.im

/-- Eq. (1), PDF p. 2: the combination `ε_r μ_i + ε_i μ_r` (the imaginary part of `ε μ`). -/
def epsMuIm (ε μ : ℂ) : ℝ := ε.re * μ.im + ε.im * μ.re

/-- Eq. (1), PDF p. 2: the quartic
`n⁴ - ((ε_r μ_i + ε_i μ_r)/2)² - (ε_r μ_r - ε_i μ_i) n² = 0` satisfied by `n = Re N`,
as a polynomial in `n` with complex coefficients. -/
def indexQuartic (ε μ : ℂ) : ℂ[X] :=
  X ^ 4 - C (((epsMuIm ε μ / 2) ^ 2 : ℝ) : ℂ) - C ((epsMuRe ε μ : ℝ) : ℂ) * X ^ 2

/-- Eqs. (2) and (6), PDF p. 2: the radicand `ε_r μ_r - ε_i μ_i + |ε||μ|` of the real
solution branches. -/
def branchRadicand (ε μ : ℂ) : ℝ := ε.re * μ.re - ε.im * μ.im + ‖ε‖ * ‖μ‖

/-- Eq. (2), PDF p. 2: the non-negative real solution branch
`n_+ = √(ε_r μ_r - ε_i μ_i + |ε||μ|) / √2`. -/
def nPlus (ε μ : ℂ) : ℝ := Real.sqrt (branchRadicand ε μ) / Real.sqrt 2

/-- Eq. (2), PDF p. 2: the non-positive real solution branch
`n_- = -√(ε_r μ_r - ε_i μ_i + |ε||μ|) / √2`. -/
def nMinus (ε μ : ℂ) : ℝ := -(Real.sqrt (branchRadicand ε μ) / Real.sqrt 2)

/-- Eq. (6), PDF p. 2: the condition `ε_r μ_r - ε_i μ_i + |ε||μ| = 0` at which the paper says the
branches `n_±` lose analyticity. -/
def Condition6 (ε μ : ℂ) : Prop := branchRadicand ε μ = 0

/-- Eq. (7), PDF p. 2: the condition `ε_r = -ε_i μ_r / μ_i` (meaningful for `μ_i ≠ 0`). -/
def Condition7 (ε μ : ℂ) : Prop := ε.re = -(ε.im * μ.re) / μ.im

end Arxiv1007_0377


