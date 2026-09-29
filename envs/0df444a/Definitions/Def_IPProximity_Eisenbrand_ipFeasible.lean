-- Prove2me | Definitions.Def_IPProximity_Eisenbrand_ipFeasible
-- name    : IPProximity_Eisenbrand_ipFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:28:48.404652+00:00
-- url     : https://prove2.me/theorems/6a4019e4-db93-4754-8042-a0fb0bbe9f63
-- title:
--   The feasible integer solutions of (10)
-- statement:
--   For $A\in\mathbb Z^{m\times n}$, $b\in\mathbb Z^m$ and $u\in\mathbb N^n$, this is the set of feasible solutions of the integer program (10),
--   $$\{z\in\mathbb Z^n : Az=b,\ 0\le z_i\le u_i \text{ for all } i\}.$$
--   It is finite, since every coordinate lies in $\{0,\dots,u_i\}$.
-- source:
--   Eisenbrand & Weismantel, Proximity Results and Faster Algorithms for Integer Programming Using the Steinitz Lemma, ACM Trans. Algorithms 16(1), Article 5 (2019), p. 5:7, Eq. (10)

import Mathlib

namespace IPProximity.Eisenbrand

/-- The set `{z ∈ ℤⁿ : A z = b, 0 ≤ z ≤ u}` of feasible integer solutions of the integer
program (10) of Eisenbrand–Weismantel (p. 5:7). -/
def ipFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (u : Fin n → ℕ) :
    Set (Fin n → ℤ) :=
  {z | Matrix.mulVec A z = b ∧ ∀ i, 0 ≤ z i ∧ z i ≤ (u i : ℤ)}

end IPProximity.Eisenbrand


