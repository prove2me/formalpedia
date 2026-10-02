-- Prove2me | Definitions.Def_LeblSCV_Levi_VanishesToOrder
-- name    : LeblSCV_Levi_VanishesToOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:40:26.879319+00:00
-- url     : https://prove2.me/theorems/8d3842de-0212-44ad-bc68-ae49caf1df60
-- title:
--   The book's $O(\ell)$: a smooth function vanishing to order $\ell$ at a point
-- statement:
--   The book uses a shorthand for the big-oh notation: a smooth function $E$ is **$O(\ell)$ at a point $x_0$** if all its derivatives of order $0, 1, \dots, \ell-1$ vanish at $x_0$. For example, $E$ is $O(3)$ at the origin when $E(0) = 0$ and all first and second derivatives of $E$ vanish at $0$.
--
--   **Formalization Note.** `VanishesToOrder l E x₀`: $E$ is $C^\infty$ on an open neighbourhood of $x_0$ and `iteratedFDeriv ℝ i E x₀ = 0` for every `i < l`. This is the book's definition, not Mathlib's `Asymptotics.IsBigO`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 60 (definition of O(ℓ)), recalled on p. 73

import Mathlib

open scoped ContDiff

namespace LeblSCV.Levi

/-- Lebl p. 60 / p. 73: a smooth function `E` is `O(ℓ)` at `x₀` if it is smooth near `x₀` and
all its derivatives of order `0, 1, …, ℓ − 1` vanish at `x₀`. -/
def VanishesToOrder {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (l : ℕ) (E : X → ℝ) (x₀ : X) : Prop :=
  ∃ N : Set X, IsOpen N ∧ x₀ ∈ N ∧ ContDiffOn ℝ ∞ E N ∧
    ∀ i < l, iteratedFDeriv ℝ i E x₀ = 0

end LeblSCV.Levi


