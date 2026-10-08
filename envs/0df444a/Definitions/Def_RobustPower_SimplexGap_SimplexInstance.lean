-- Prove2me | Definitions.Def_RobustPower_SimplexGap_SimplexInstance
-- name    : RobustPower_SimplexGap_SimplexInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:12:54.11431+00:00
-- url     : https://prove2.me/theorems/2ed1ab4b-1394-42c6-9fd4-a8519a84f1b1
-- title:
--   (2.29), p. 19 — the corner simplex, the cost vector eₙ and the uniform scenario model of Theorem 2.6
-- statement:
--   This file fixes the data of the instance in Theorem 2.6 of Bertsimas and Goyal.
--
--   1. The **corner simplex** (2.29) in $\mathbb R^n$ is
--   $$\Delta_n=\Big\{\,b\in\mathbb R^n \;:\; \sum_{j=1}^n b_j\le 1,\ b\ge 0\,\Big\}.$$
--   2. The cost vector $e_n=(0,\dots,0,1)\in\mathbb R^n$ has its $n$-th coordinate equal to one and all others zero.
--   3. A scenario model $(\Omega,\mu,b)$, with $\Omega$ a measurable space, $\mu$ a measure on $\Omega$ and $b:\Omega\to\mathbb R^n$, is **uniform on the simplex** if $b$ is measurable, the uncertainty set $I_b(\Omega)=\{b(\omega)\mid\omega\in\Omega\}$ equals $\Delta_n$, and the law of $b$ under $\mu$ is the normalized Lebesgue measure on $\Delta_n$:
--   $$\mu\big(b^{-1}(S)\big)=\frac{\operatorname{vol}(S\cap\Delta_n)}{\operatorname{vol}(\Delta_n)}\quad\text{for every Borel } S\subseteq\mathbb R^n.$$
--
--   This is the paper's "uniform probability measure on $I_b(\Omega)$, i.e., $\mu(S)=\operatorname{volume}(\{b(\omega)\mid\omega\in S\})/\operatorname{volume}(I_b(\Omega))$". The model $\Omega=\Delta_n$, $b=$ identity is one such model.
--
--   **Formalization Note** In Lean the coordinates are indexed by `Fin n` from $0$, so $e_n$ is the indicator of index $n-1$ (`lastUnit n`). The paper's formula for $\mu(S)$ is read as a statement about the push-forward $b_*\mu$, which is the form that is meaningful when $b$ is not injective. "volume" is Lebesgue measure on $\mathbb R^n$ (`volume` on `Fin n → ℝ`). That $\operatorname{vol}(\Delta_n)$ is finite and nonzero is not assumed; it is a fact.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 19, Theorem 2.6, (2.29)

import Mathlib

namespace RobustPower.SimplexGap

open MeasureTheory

/-- The uncertainty set (2.29): the corner simplex `{b ∈ ℝⁿ | ∑ⱼ bⱼ ≤ 1, b ≥ 0}`. -/
def cornerSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {b | ∑ j, b j ≤ 1 ∧ 0 ≤ b}

/-- The cost vector `d = eₙ = (0, …, 0, 1)` of Theorem 2.6: its last coordinate (index `n - 1`
with `0`-based `Fin n`) is one and all others are zero. -/
def lastUnit (n : ℕ) : Fin n → ℝ :=
  fun j => if (j : ℕ) = n - 1 then 1 else 0

/-- The scenario model of Theorem 2.6: `b : Ω → ℝⁿ` is measurable, its range (the uncertainty set
`I_b(Ω)`) is the corner simplex (2.29), and `μ` is uniform on it, i.e. the law of `b` under `μ` is
Lebesgue measure restricted to the simplex and divided by the simplex's volume. -/
def IsUniformOnSimplex {Ω : Type*} [MeasurableSpace Ω] (n : ℕ) (μ : Measure Ω)
    (b : Ω → Fin n → ℝ) : Prop :=
  Measurable b ∧ Set.range b = cornerSimplex n ∧
    μ.map b = (volume (cornerSimplex n))⁻¹ • volume.restrict (cornerSimplex n)

end RobustPower.SimplexGap


