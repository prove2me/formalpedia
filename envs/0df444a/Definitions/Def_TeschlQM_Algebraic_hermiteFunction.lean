-- Prove2me | Definitions.Def_TeschlQM_Algebraic_hermiteFunction
-- name    : TeschlQM_Algebraic_hermiteFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T01:47:01.517977+00:00
-- url     : https://prove2.me/theorems/b92f90eb-2b16-403c-8f68-302ea95dbd22
-- title:
--   Hermite polynomials Hₙ (8.42), Hermite functions ψₙ (8.41) and their products (8.43)
-- statement:
--   The (physicists') **Hermite polynomials** are
--   $$H_n(x) = (-1)^n e^{x^2} \frac{d^n}{dx^n} e^{-x^2}, \qquad n \in \mathbb N_0.$$
--   For $\omega > 0$ the **Hermite functions** are
--   $$\psi_n(x) = \frac{1}{\sqrt{2^n n!}} \Big(\frac{\omega}{\pi}\Big)^{1/4} H_n(\sqrt\omega\, x)\, e^{-\omega x^2/2}, \qquad x \in \mathbb R,$$
--   and on $\mathbb R^3$, for $n = (n_1, n_2, n_3) \in \mathbb N_0^3$,
--   $$\psi_{n_1,n_2,n_3}(x) = \psi_{n_1}(x_1)\,\psi_{n_2}(x_2)\,\psi_{n_3}(x_3).$$
--
--   These are the eigenfunctions of the harmonic oscillator in Theorem 8.5.
--
--   **Formalization Note.** $H_n$ is defined by the Rodrigues formula of (8.42) with `iteratedDeriv`; Mathlib's `Polynomial.hermite` (the probabilists' family, $H_{n+1} = xH_n - H_n'$) is not used. $(\omega/\pi)^{1/4}$ is `Real.rpow`, meaningful for $\omega > 0$, which every theorem using it assumes.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 179, Eqs. (8.41)–(8.43)

import Mathlib

namespace TeschlQM.Algebraic

/-- Teschl (8.42), p. 179: the (physicists') **Hermite polynomial**
`Hₙ(x) = (−1)ⁿ e^{x²} dⁿ/dxⁿ e^{−x²}`. (Mathlib's `Polynomial.hermite` is the probabilists'
family and is not used.) -/
noncomputable def physHermite (n : ℕ) (x : ℝ) : ℝ :=
  (-1) ^ n * Real.exp (x ^ 2) * iteratedDeriv n (fun y : ℝ => Real.exp (-y ^ 2)) x

/-- Teschl (8.41), p. 179: the one-dimensional **Hermite function**
`ψₙ(x) = (2ⁿ n!)^{−1/2} (ω/π)^{1/4} Hₙ(√ω x) e^{−ωx²/2}`. -/
noncomputable def hermiteFunction (ω : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  ((1 / Real.sqrt (2 ^ n * n.factorial)) * (ω / Real.pi) ^ (1 / 4 : ℝ) *
    physHermite n (Real.sqrt ω * x) * Real.exp (-(ω * x ^ 2) / 2) : ℝ)

/-- Teschl (8.43), p. 179: the product
`ψ_{n₁,n₂,n₃}(x) = ψ_{n₁}(x₁) ψ_{n₂}(x₂) ψ_{n₃}(x₃)` on `ℝ³`, `n ∈ ℕ₀³`. -/
noncomputable def hermiteProduct (ω : ℝ) (n : Fin 3 → ℕ) (x : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  ∏ j : Fin 3, hermiteFunction ω (n j) (x j)

end TeschlQM.Algebraic


