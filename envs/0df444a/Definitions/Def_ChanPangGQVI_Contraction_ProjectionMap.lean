-- Prove2me | Definitions.Def_ChanPangGQVI_Contraction_ProjectionMap
-- name    : ChanPangGQVI_Contraction_ProjectionMap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:02:20.866352+00:00
-- url     : https://prove2.me/theorems/db8ff45b-9761-4070-a736-bd5b1cefe977
-- title:
--   The translated feasible map $K(x)=m(x)+\tilde K$ and the projection map $F_\lambda(x)=P_{K(x)}(x-\lambda f(x))$
-- statement:
--   Let $m, f:\mathbb R^n\to\mathbb R^n$ be point-to-point mappings, let $\tilde K\subseteq\mathbb R^n$ be a set, and let $\lambda$ be a real number. The point-to-set mapping $K$ is the translate of the fixed set $\tilde K$ by $m(x)$:
--
--   $$
--   K(x)=m(x)+\tilde K=\{z : z=m(x)+k \text{ for some } k\in\tilde K\}.
--   $$
--
--   The **projection map** of Theorem 5.3 is
--
--   $$
--   F_\lambda(x)=P_{K(x)}\bigl(x-\lambda f(x)\bigr),
--   $$
--
--   the projection (nearest point) of the point $x-\lambda f(x)$ on the set $K(x)$.
--
--   A fixed point of $F_\lambda$ is a point $x$ with $x\in K(x)$ that is its own projection after a step of length $\lambda$ along $-f(x)$; by Theorem 5.1 such points are exactly the solutions of the GQVI$(K,f)$ when $\lambda>0$ and $K(x)$ is closed and convex. The iteration $x^{k+1}=F_\lambda(x^k)$ is the solution method studied in Theorem 5.3.
--
--   **Formalization Note** `Kmap m Ktil x` is $K(x)$ and `Flam m f Ktil lam x` is $F_\lambda(x)$, built on the mission's `proj`. When $\tilde K$ is nonempty, closed and convex, so is every $K(x)$, and `proj` returns the unique nearest point.
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 221, Theorem 5.3 (definitions of K(x) = m(x) + K̃ and F_λ); cf. (1), p. 212

import Mathlib
import Definitions.Def_ChanPangGQVI_Shared_Projection

namespace ChanPangGQVI.Contraction

/-- Chan and Pang 1982, p. 221, Theorem 5.3: the point-to-set mapping `K(x) = m(x) + K̃`, the
translate of the fixed set `K̃` by the vector `m(x)`:
`K(x) = {z : z = m(x) + k for some k ∈ K̃}` (cf. (1), p. 212). -/
def Kmap {n : ℕ} (m : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (Ktil : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {z | ∃ k ∈ Ktil, z = m x + k}

/-- Chan and Pang 1982, p. 221, Theorem 5.3: the mapping
`F_λ(x) = P_{K(x)}(x - λ f(x))` with `K(x) = m(x) + K̃`, i.e. the projection of
`x - λ f(x)` on the set `K(x)`. -/
noncomputable def Flam {n : ℕ} (m f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (Ktil : Set (EuclideanSpace ℝ (Fin n))) (lam : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  ChanPangGQVI.Shared.proj (Kmap m Ktil x) (x - lam • f x)

end ChanPangGQVI.Contraction


