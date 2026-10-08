-- Prove2me | Definitions.Def_FastRatesSVM_GeomNoise_TsybakovNoise
-- name    : FastRatesSVM_GeomNoise_TsybakovNoise
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:29.429762+00:00
-- url     : https://prove2.me/theorems/751fd113-f3d0-4bda-ae87-af2c5548b214
-- title:
--   Definition 2.2 — Tsybakov noise exponent $q$: $P_X(|2\eta-1| \le t) \le C t^q$ for small $t$
-- statement:
--   Let $0 \le q \le \infty$ and let $P$ be a probability measure on $X \times \{-1, 1\}$ with marginal $P_X$ and regression function $\eta$. The distribution $P$ has **Tsybakov noise exponent** $q$ if there is a constant $C > 0$ such that for all sufficiently small $t > 0$
--
--   $$P_X\big(\{x \in X : |2\eta(x) - 1| \le t\}\big) \le C\, t^q,$$
--
--   with the convention $t^\infty := 0$ for $t \in (0, 1)$.
--
--   The function $|2\eta - 1|$ measures how far the label of $x$ is from a fair coin flip, so the condition bounds the mass of the very noisy region. Every distribution has exponent $0$; exponent $\infty$ means that $\eta$ is bounded away from $\tfrac12$ almost surely.
--
--   **Formalization Note** "For all sufficiently small $t > 0$" is encoded as: there is $t_0 \in (0, 1)$ such that the bound holds for all $t \in (0, t_0]$; requiring $t_0 < 1$ loses nothing and keeps the convention $t^\infty = 0$ inside its range $t \in (0,1)$. The exponent is an element of $[0, \infty]$ (`ENNReal`); for $q = \infty$ the right side is $0$, for $q < \infty$ it is $C t^q$ with the real power. $P$ is represented by $\mu = P_X$ (a measure on `EuclideanSpace ℝ (Fin d)`) and the function $\eta$.
-- source:
--   Steinwart, Scovel, Fast Rates for Support Vector Machines Using Gaussian Kernels, arXiv:0708.1838v1, p. 6, Definition 2.2, equation (5)

import Mathlib

open MeasureTheory

namespace FastRatesSVM.GeomNoise

/-- **Tsybakov noise exponent** `q ∈ [0, ∞]`, Definition 2.2, p. 6 (Steinwart–Scovel,
arXiv:0708.1838v1): there are `C > 0` and a threshold `t₀ ∈ (0, 1)` such that for all
`t ∈ (0, t₀]`, `P_X({x ∈ X : |2η(x) − 1| ≤ t}) ≤ C · t^q`, with the paper's convention
`t^∞ := 0` for `t ∈ (0, 1)`. The distribution `P` on `X × {−1, 1}` is represented by its marginal
`μ = P_X` and a version `η` of its regression function `P(y = 1 | x)`. -/
def HasTsybakovNoiseExponent {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d)))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (η : EuclideanSpace ℝ (Fin d) → ℝ)
    (q : ENNReal) : Prop :=
  ∃ C t₀ : ℝ, 0 < C ∧ 0 < t₀ ∧ t₀ < 1 ∧
    ∀ t : ℝ, 0 < t → t ≤ t₀ →
      μ {x | x ∈ X ∧ |2 * η x - 1| ≤ t} ≤
        if q = ⊤ then 0 else ENNReal.ofReal (C * t ^ q.toReal)

end FastRatesSVM.GeomNoise


