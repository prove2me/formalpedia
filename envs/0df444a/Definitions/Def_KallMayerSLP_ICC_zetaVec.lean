-- Prove2me | Definitions.Def_KallMayerSLP_ICC_zetaVec
-- name    : KallMayerSLP_ICC_zetaVec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:10:00.131218+00:00
-- url     : https://prove2.me/theorems/b17ebd6d-4f91-4e44-ae7b-f25ccbab8dec
-- title:
--   Random vector $\zeta(x,\xi)=T(\xi)x-h(\xi)$
-- statement:
--   Let $T(\xi)$ be a random $s\times n$ matrix and $h(\xi)\in\mathbb R^s$ a random vector, both depending on the random vector $\xi$. For $x\in\mathbb R^n$,
--   $$
--   \zeta(x,\xi)=T(\xi)x-h(\xi)\in\mathbb R^s.
--   $$
--   Its $i$-th component is the $i$-th row of $T(\xi)$ applied to $x$, minus $h_i(\xi)$. This is the object of the joint integrated chance constraints.
--
--   **Formalization Note** `T` and `h` are arbitrary functions on `Ξ`, since the affine form (1.2) is "not used explicitly" in the chapter. Indices are $0$-based.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, (1.1), p.75 (PDF 85); §4.1.2, p.154 (PDF 164)

import Mathlib

open Matrix

namespace KallMayerSLP.ICC

/-- **The random vector `ζ(x, ξ) = T(ξ)x − h(ξ)`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, (1.1), p.75 (PDF 85), and §4.1.2,
p.154 (PDF 164).

**Formalization Note.** `T ξ` is the `s × n` matrix `T(ξ)`, `h ξ ∈ ℝˢ`. The `i`-th component is
`T ξ i ⬝ᵥ x - h ξ i`, the `i`-th row of `T(ξ)` applied to `x`. Index base `0`. The book's affine
form (1.2) of `T, h` in `ξ` is "not used explicitly" (p.75), so `T` and `h` are arbitrary functions
here. -/
def zetaVec {Ξ : Type*} {s n : ℕ} (T : Ξ → Matrix (Fin s) (Fin n) ℝ) (h : Ξ → Fin s → ℝ)
    (x : Fin n → ℝ) (ξ : Ξ) : Fin s → ℝ :=
  T ξ *ᵥ x - h ξ

end KallMayerSLP.ICC


