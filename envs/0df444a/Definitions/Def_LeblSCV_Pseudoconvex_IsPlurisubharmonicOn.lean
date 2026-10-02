-- Prove2me | Definitions.Def_LeblSCV_Pseudoconvex_IsPlurisubharmonicOn
-- name    : LeblSCV_Pseudoconvex_IsPlurisubharmonicOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T03:46:18.366698+00:00
-- url     : https://prove2.me/theorems/9d093cf3-31d3-4df6-b2e9-4a5be1efd544
-- title:
--   Plurisubharmonic function (p. 84)
-- statement:
--   Let $U \subset \mathbb{C}^n$ be open. A function $f : U \to \mathbb{R} \cup \{-\infty\}$ is **plurisubharmonic** if it is upper-semicontinuous and, for every $a, b \in \mathbb{C}^n$, the function of one variable
--   $$\xi \mapsto f(a + b\xi)$$
--   is subharmonic where it is defined, namely on the open set $\{\xi \in \mathbb{C} : a + b\xi \in U\}$.
--
--   Plurisubharmonic functions are the several-complex-variables analogue of convex functions: a function is plurisubharmonic exactly when it is subharmonic on every complex line.
--
--   **Formalization Note.** **Formalization Note.** $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)`, so its norm, balls and distances are Euclidean, as in the book. Values in $\mathbb{R}\cup\{-\infty\}$ are modelled in `EReal` together with the requirement $f \neq +\infty$ on $U$; upper semicontinuity is Mathlib's `UpperSemicontinuousOn` for the order of `EReal`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 84 (definition following Definition 2.4.8)

import Mathlib
import Definitions.Def_LeblSCV_Pseudoconvex_IsSubharmonicOn

namespace LeblSCV.Pseudoconvex

/-- Plurisubharmonic function (Lebl, p. 84, the definition following Definition 2.4.8):
for open `U ⊂ ℂⁿ`, `f : U → ℝ ∪ {−∞}` is *plurisubharmonic* if it is upper-semicontinuous and
for every `a, b ∈ ℂⁿ` the function of one variable `ξ ↦ f(a + bξ)` is subharmonic where
defined, i.e. on `{ξ ∈ ℂ : a + bξ ∈ U}`.
`ℂⁿ` is `EuclideanSpace ℂ (Fin n)`; values in `ℝ ∪ {−∞}` are `EReal` with `⊤` excluded on `U`. -/
def IsPlurisubharmonicOn {n : ℕ} (f : EuclideanSpace ℂ (Fin n) → EReal)
    (U : Set (EuclideanSpace ℂ (Fin n))) : Prop :=
  UpperSemicontinuousOn f U ∧ (∀ z ∈ U, f z ≠ ⊤) ∧
    ∀ a b : EuclideanSpace ℂ (Fin n),
      IsSubharmonicOn (fun ξ : ℂ => f (a + ξ • b)) {ξ : ℂ | a + ξ • b ∈ U}

end LeblSCV.Pseudoconvex


