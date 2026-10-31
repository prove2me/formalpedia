-- Prove2me | Definitions.Def_KallMayerSLP_ProbConstr_feasibleEvent
-- name    : KallMayerSLP_ProbConstr_feasibleEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:09:24.152023+00:00
-- url     : https://prove2.me/theorems/8e5cb125-8441-419b-a060-718224604bb5
-- title:
--   The event $S(x)=\{\xi \mid T(\xi)x\ge h(\xi)\}$
-- statement:
--   Let $\xi$ be a random vector with values in $\mathbb R^r$, let $T(\xi)$ be a random $m\times n$ matrix and $h(\xi)$ a random vector in $\mathbb R^m$. For a decision $x\in\mathbb R^n$ the event that the random linear system holds is
--   $$
--   S(x)=\{\xi\in\mathbb R^r \mid T(\xi)x\ge h(\xi)\},
--   $$
--   the inequality being componentwise. The joint probability function of the chapter is $G(x)=\mathbb P_\xi(S(x))$.
--
--   **Formalization Note** $\mathbb R^r$, $\mathbb R^n$, $\mathbb R^m$ are `Fin r → ℝ`, `Fin n → ℝ`, `Fin m → ℝ`. The data $T(\cdot)$, $h(\cdot)$ are arbitrary functions of the realization; the book's affine data $T(\xi)=T+\sum_j T^j\xi_j$, $h(\xi)=h+\sum_j h^j\xi_j$ are a special case.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Chapter 2, §2.1, p.96 (PDF 106), definition of S(x) after (2.12); Notations p.ix (PDF 10)

import Mathlib

open Matrix

namespace KallMayerSLP.ProbConstr

/-- The event `S(x) := {ξ | T(ξ)x ≥ h(ξ)}` of the realizations `ξ ∈ ℝ^r` for which the random
linear system holds at the decision `x ∈ ℝ^n`.

Kall & Mayer 2005, Chapter 2, §2.1, p.96 (PDF 106), the display after (2.12).

**Formalization Note.** `ℝ^r`, `ℝ^n`, `ℝ^m` are `Fin r → ℝ`, `Fin n → ℝ`, `Fin m → ℝ`. The random
technology matrix `T(ξ)` (an `m × n` matrix) and right-hand side `h(ξ)` are arbitrary functions of
the realization `ξ`; the book's affine data `T(ξ) = T + Σ_j T^j ξ_j`, `h(ξ) = h + Σ_j h^j ξ_j`
(Notations, p.ix) are a special case. `T(ξ)x ≥ h(ξ)` is componentwise, i.e. `h ξ ≤ T ξ *ᵥ x` in
the pointwise order of `Fin m → ℝ`. -/
def feasibleEvent {r m n : ℕ} (T : (Fin r → ℝ) → Matrix (Fin m) (Fin n) ℝ)
    (h : (Fin r → ℝ) → Fin m → ℝ) (x : Fin n → ℝ) : Set (Fin r → ℝ) :=
  {ξ | h ξ ≤ T ξ *ᵥ x}

end KallMayerSLP.ProbConstr


