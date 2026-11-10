-- Prove2me | Definitions.Def_NashOrTriangle_IsTriangle
-- name    : NashOrTriangle_IsTriangle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:43:30.08998+00:00
-- url     : https://prove2.me/theorems/9cfccb77-a604-4cc6-8ff2-33267baedf61
-- title:
--   $t$-triangle of a binary game
-- statement:
--   In a binary game, a **$t$-triangle** consists of distinct rows $a_1, \dots, a_t$ and distinct columns $b_1, \dots, b_t$ with
--   $$
--   M(a_i, b_j) = 1 \iff i \le j .
--   $$
--   It is an upper triangular $t \times t$ submatrix, a finite piece of the "guess the larger number" game $M(i,j) = \mathbf 1[i \ge j]$ (whose triangles use reversed orders).
--
--   **Formalization Note** Indices run over $\{0, \dots, t-1\}$; "distinct" is injectivity of $i \mapsto a_i$ and $j \mapsto b_j$.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), §1.1, p.3 (PDF p.4)

import Mathlib

namespace NashOrTriangle

/-- A **`t`-triangle** of a binary game: distinct rows `a₁, …, a_t` and distinct columns
`b₁, …, b_t` with `M(aᵢ, bⱼ) = 1` iff `i ≤ j` (upper triangular, diagonal included).

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), §1.1, printed p. 3 (PDF p. 4): "In a binary game, a t-triangle consists of distinct rows
a1, . . . , at and distinct columns b1, . . . , bt with M(ai, bj) = 1 iff i ≤ j."

**Formalization Note** Indices are `Fin t` (0-based); "distinct" is injectivity. -/
def IsTriangle {A B : Type*} (M : A → B → ℚ) {t : ℕ} (a : Fin t → A) (b : Fin t → B) : Prop :=
  Function.Injective a ∧ Function.Injective b ∧ ∀ i j, M (a i) (b j) = 1 ↔ i ≤ j

end NashOrTriangle


