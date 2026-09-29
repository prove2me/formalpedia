-- Prove2me | Definitions.Def_IPProximity_Eisenbrand_lpPolytope
-- name    : IPProximity_Eisenbrand_lpPolytope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:28:27.329187+00:00
-- url     : https://prove2.me/theorems/dc336678-6447-4197-a0a5-1b9cf087f1a5
-- title:
--   The feasible region of the LP relaxation of (10)
-- statement:
--   Let $m,n\ge 0$, let $A\in\mathbb Z^{m\times n}$, $b\in\mathbb Z^m$, $c\in\mathbb Z^n$ and $u\in\mathbb N^n$. The integer program (10) of Eisenbrand and Weismantel is
--   $$\max\{c^{T}x : Ax=b,\ 0\le x\le u,\ x\in\mathbb Z^n\},$$
--   and its linear programming (LP) relaxation is the same problem with $x\in\mathbb R^n$.
--
--   For integral data $A\in\mathbb Z^{m\times n}$, $b\in\mathbb Z^m$ and upper bounds $u\in\mathbb N^n$, this defines the polytope
--   $$P(A,b,u)=\{x\in\mathbb R^n : Ax=b,\ 0\le x_i\le u_i \text{ for all } i\},$$
--   the feasible region of the LP relaxation of (10). Its extreme points are the *vertices* referred to in Theorem 3.3.
--
--   **Formalization Note** The entries of $A$, $b$ and $u$ are cast from $\mathbb Z$ (resp. $\mathbb N$) to $\mathbb R$; the equation $Ax=b$ is `Matrix.mulVec` of the cast matrix.
-- source:
--   Eisenbrand & Weismantel, Proximity Results and Faster Algorithms for Integer Programming Using the Steinitz Lemma, ACM Trans. Algorithms 16(1), Article 5 (2019), p. 5:7, Eq. (10) (LP relaxation)

import Mathlib

namespace IPProximity.Eisenbrand

/-- The feasible region `{x ∈ ℝⁿ : A x = b, 0 ≤ x ≤ u}` of the linear programming relaxation of
the integer program (10) of Eisenbrand–Weismantel (p. 5:7); the integral data `A, b, u` are cast
to `ℝ`. -/
def lpPolytope {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (u : Fin n → ℕ) :
    Set (Fin n → ℝ) :=
  {x | Matrix.mulVec (A.map (Int.cast : ℤ → ℝ)) x = (fun i => (b i : ℝ)) ∧
    ∀ i, 0 ≤ x i ∧ x i ≤ (u i : ℝ)}

end IPProximity.Eisenbrand


