-- Prove2me | Definitions.Def_TeschlQM_Algebraic_ladder
-- name    : TeschlQM_Algebraic_ladder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T01:57:23.35203+00:00
-- url     : https://prove2.me/theorems/5d85190e-5274-4622-98a6-057f92aa65ab
-- title:
--   Ladder operators A± on 𝔇_ω (8.35)
-- statement:
--   Let $\omega > 0$. In one dimension let
--   $$\mathfrak D_\omega = \operatorname{span}\{x^k e^{-\omega x^2/2} \mid k \in \mathbb N_0\},$$
--   a space of functions $\mathbb R \to \mathbb C$. The **creation** and **annihilation operators** are
--   $$A_\pm = \frac{1}{\sqrt 2}\Big(\sqrt\omega\, x \mp \frac{1}{\sqrt\omega}\frac{d}{dx}\Big), \qquad (A_\pm f)(x) = \frac{1}{\sqrt 2}\Big(\sqrt\omega\, x f(x) \mp \frac{1}{\sqrt\omega} f'(x)\Big).$$
--
--   They factor the one-dimensional harmonic oscillator, $H = \omega(2A_+A_- + 1)$ on $\mathfrak D_\omega$.
--
--   **Formalization Note.** `ladderPlus ω` and `ladderMinus ω` act on all functions `ℝ → ℂ` through `deriv`; the statements about them restrict to `core1 ω`, whose elements are smooth. The book's $\mathfrak D(A_\pm) = \mathfrak D$ is the space `core1 ω` (for $\omega = 1$ the book's 𝔇 in one dimension).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 178, Eq. (8.35)

import Mathlib

namespace TeschlQM.Algebraic

/-- The one-dimensional domain `𝔇_ω = span{x^k e^{−ωx²/2} | k ∈ ℕ₀}`, as a space of functions
`ℝ → ℂ` (Teschl (8.34) in one dimension, p. 178). -/
noncomputable def core1 (ω : ℝ) : Submodule ℂ (ℝ → ℂ) :=
  Submodule.span ℂ
    (Set.range fun k : ℕ => fun x : ℝ => ((x ^ k * Real.exp (-(ω * x ^ 2) / 2) : ℝ) : ℂ))

/-- Teschl (8.35), p. 178: the **creation operator**
`A₊ f = (1/√2)(√ω x f − (1/√ω) f′)`. -/
noncomputable def ladderPlus (ω : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (1 / Real.sqrt 2 : ℝ) *
    ((Real.sqrt ω * x : ℝ) * f x - (1 / Real.sqrt ω : ℝ) * deriv f x)

/-- Teschl (8.35), p. 178: the **annihilation operator**
`A₋ f = (1/√2)(√ω x f + (1/√ω) f′)`. -/
noncomputable def ladderMinus (ω : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (1 / Real.sqrt 2 : ℝ) *
    ((Real.sqrt ω * x : ℝ) * f x + (1 / Real.sqrt ω : ℝ) * deriv f x)

end TeschlQM.Algebraic


