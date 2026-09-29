-- Prove2me | Definitions.Def_IPProximity_Eisenbrand_IsCycle
-- name    : IPProximity_Eisenbrand_IsCycle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:30:12.920884+00:00
-- url     : https://prove2.me/theorems/c22d4223-8a63-42b9-92ad-7a7afebaff72
-- title:
--   Cycle of $z^* - x^*$, Eq. (14)
-- statement:
--   Let $A\in\mathbb Z^{m\times n}$, $z\in\mathbb Z^n$ and $x\in\mathbb R^n$. A vector $y\in\mathbb Z^n$ is a **cycle** of $z-x$ if $Ay=0$ and, for each coordinate $i$,
--   $$|y_i|\le|(z-x)_i|\qquad\text{and}\qquad y_i\,(z-x)_i\ge 0 .$$
--   In words: $y$ is an integer vector in the kernel of $A$ that is sign-compatible with $z-x$ and dominated by it coordinatewise. The definition is taken literally from Eq. (14) of the paper; in particular $y=0$ is always a cycle, which is why Lemma 3.2 is stated for nonzero cycles.
-- source:
--   Eisenbrand & Weismantel, Proximity Results and Faster Algorithms for Integer Programming Using the Steinitz Lemma, ACM Trans. Algorithms 16(1), Article 5 (2019), p. 5:7, Eq. (14)

import Mathlib

namespace IPProximity.Eisenbrand

/-- Eq. (14) of Eisenbrand–Weismantel (p. 5:7), taken literally: an integer vector `y` is a
*cycle* of `z - x` if `A y = 0` and, for each `i`, `|yᵢ| ≤ |(z - x)ᵢ|` and `yᵢ · (z - x)ᵢ ≥ 0`.
The zero vector is always a cycle. -/
def IsCycle {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (z : Fin n → ℤ) (x : Fin n → ℝ)
    (y : Fin n → ℤ) : Prop :=
  Matrix.mulVec A y = 0 ∧
    ∀ i, |(y i : ℝ)| ≤ |(z i : ℝ) - x i| ∧ 0 ≤ (y i : ℝ) * ((z i : ℝ) - x i)

end IPProximity.Eisenbrand


