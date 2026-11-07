-- Prove2me | Definitions.Def_QuasiStrictNE_RatGame
-- name    : QuasiStrictNE_RatGame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:05:59.507701+00:00
-- url     : https://prove2.me/theorems/aa84fac5-3875-47e9-8153-ea837e58adbd
-- title:
--   Rational bimatrix game
-- statement:
--   A **rational bimatrix game** consists of the numbers $m,n$ of pure strategies of players 1 and 2 and two rational payoff matrices $A,B\in\mathbb Q^{m\times n}$ (player 1 receives $A_{ij}$ and player 2 receives $B_{ij}$ when player 1 plays $i$ and player 2 plays $j$).
--
--   **Formalization Note** The conditions $m,n\ge 1$ are imposed where they are needed (they are part of a valid instance of the search problems).
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Definition 1, p.4

import Mathlib

namespace QuasiStrictNE

/-- **A rational bimatrix game** (Hansen & Nie, *On Existence and Computational Complexity of
Quasi-strict Equilibria*, arXiv:2611.06350, Definition 1, p.4: "A bimatrix game is given by a pair
I := (A, B) of matrices A, B ∈ R^{m×n} … When considering the computational problem of finding an
equilibrium, the payoff matrices are defined on the rational number field Q").

`m` and `n` are the numbers of pure strategies of players 1 and 2; `A` and `B` are their rational
`m × n` payoff matrices.

**Formalization Note** The conditions `1 ≤ m`, `1 ≤ n` are stated where needed (in the search
problems they are part of a valid instance). -/
structure RatGame where
  m : ℕ
  n : ℕ
  A : Matrix (Fin m) (Fin n) ℚ
  B : Matrix (Fin m) (Fin n) ℚ

end QuasiStrictNE


