-- Prove2me | Definitions.Def_LeblSCV_Levi_IsBiholomorphicOn
-- name    : LeblSCV_Levi_IsBiholomorphicOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:40:07.746481+00:00
-- url     : https://prove2.me/theorems/03a882aa-72e6-4818-978e-623d9d05041b
-- title:
--   Biholomorphic map between open subsets of $\mathbb{C}^n$
-- statement:
--   A map $f : V \to V'$ between open subsets of $\mathbb{C}^n$ is **biholomorphic** if it is a bijection of $V$ onto $V'$, holomorphic on $V$, and its inverse $f^{-1} : V' \to V$ is holomorphic. A **local biholomorphic change of coordinates** at $p$ is such an $f$ with $V$ a neighbourhood of $p$.
--
--   **Formalization Note.** `IsBiholomorphicOn f V V'`: `Set.BijOn f V V'`, `DifferentiableOn ℂ f V`, and some `g` with `Set.InvOn g f V V'` and `DifferentiableOn ℂ g V'`. Holomorphic on an open set is `DifferentiableOn ℂ`, which is equivalent to the book's Definition 1.1.2 there (Proposition 1.1.3 and Theorem 1.2.1). Openness of `V`, `V'` is a separate hypothesis wherever the notion is used.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 33, Definition 1.4.1 (used on pp. 72–75)

import Mathlib

namespace LeblSCV.Levi

/-- Definition 1.4.1 (Lebl, p. 33) for open sets: `f` is a biholomorphism of `V` onto `V'` —
a bijection `V → V'`, holomorphic on `V`, whose inverse is holomorphic on `V'`. -/
def IsBiholomorphicOn {n : ℕ} (f : (Fin n → ℂ) → (Fin n → ℂ)) (V V' : Set (Fin n → ℂ)) : Prop :=
  Set.BijOn f V V' ∧ DifferentiableOn ℂ f V ∧
    ∃ g : (Fin n → ℂ) → (Fin n → ℂ), Set.InvOn g f V V' ∧ DifferentiableOn ℂ g V'

end LeblSCV.Levi


