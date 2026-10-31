-- Prove2me | Definitions.Def_KallMayerSLP_ICC_zeta
-- name    : KallMayerSLP_ICC_zeta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:09:57.92608+00:00
-- url     : https://prove2.me/theorems/96e0937a-689d-4a64-a42c-d20dd416a52a
-- title:
--   Scalar random variable $\zeta(x,\xi)=t(\xi)^{\mathrm T}x-h(\xi)$
-- statement:
--   Let $\xi$ be a random vector with values in a space $\Xi$, let $t(\xi)\in\mathbb R^n$ be a random row and $h(\xi)\in\mathbb R$ a random variable. For a decision $x\in\mathbb R^n$, the case $s=1$ of the book's model is the real random variable
--   $$
--   \zeta(x,\xi)=t(\xi)^{\mathrm T}x-h(\xi).
--   $$
--   This is the quantity whose positive and negative parts are treated as losses in separate integrated chance constraints.
--
--   **Formalization Note** The book's affine form (1.2) of the data in $\xi$ is, in its words, "not used explicitly" in the chapter, so `t` and `h` are arbitrary functions on `Ξ`. Indices are $0$-based: `Fin n` stands for $\{1,\dots,n\}$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §4.1.1, p.149 (PDF 159)

import Mathlib

open Matrix

namespace KallMayerSLP.ICC

/-- **The scalar random variable `ζ(x, ξ) = t(ξ)ᵀx − h(ξ)` (the case `s = 1`).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §4.1.1, p.149 (PDF 159).

**Formalization Note.** `Ξ` is the space the random vector `ξ` takes its values in (`ℝʳ` in the
book), `t ξ` is the `n`-dimensional row `t(ξ)`, `h ξ` is the real number `h(ξ)`. Index base `0`:
`Fin n` stands for `{1, …, n}`. The book's affine form (1.2) of `t, h` in `ξ` is "not used
explicitly" (p.75), so `t` and `h` are arbitrary functions here. -/
def zeta {Ξ : Type*} {n : ℕ} (t : Ξ → Fin n → ℝ) (h : Ξ → ℝ) (x : Fin n → ℝ) (ξ : Ξ) : ℝ :=
  t ξ ⬝ᵥ x - h ξ

end KallMayerSLP.ICC


