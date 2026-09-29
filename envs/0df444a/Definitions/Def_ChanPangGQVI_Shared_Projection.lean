-- Prove2me | Definitions.Def_ChanPangGQVI_Shared_Projection
-- name    : ChanPangGQVI_Shared_Projection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:42:06.496556+00:00
-- url     : https://prove2.me/theorems/a384ea9e-84a3-4e27-a739-e6a9b6348ce7
-- title:
--   Nearest point and the projection $P_S(z)$ of a point on a set
-- statement:
--   Work in $\mathbb R^n$ with the Euclidean norm $\|\cdot\|$. For a set $S\subseteq\mathbb R^n$ and a point $z$, a point $p$ is a **nearest point of $S$ to $z$** if
--
--   $$
--   p\in S\qquad\text{and}\qquad \|p-z\|\le\|q-z\|\quad\text{for all } q\in S,
--   $$
--
--   that is, $p$ solves $\min_{x\in S}\|x-z\|$. The **projection** of $z$ on $S$ is
--
--   $$
--   P_S(z)=\operatorname{sol}\min_{x\in S}\|x-z\| .
--   $$
--
--   For a nonempty closed convex set $S$ the nearest point exists and is unique, so $P_S(z)$ is well defined; this is the only case in which the projection is used in this series.
--
--   This definition is shared by two missions of this series: II, existence via projection (Theorem 5.1 and Lemma 5.1, p. 220) and III, the projection contraction (Theorem 5.1, p. 220; the map $F_\lambda$, the translate identity $P_{K(x)}(y)=m(x)+P_{\tilde K}(y-m(x))$, the Lipschitz estimate and Theorem 5.3, p. 221).
--
--   **Formalization Note** `IsProj S z p` is the nearest-point predicate. `proj S z` returns a nearest point when one exists and the junk value $z$ otherwise (for instance when $S=\emptyset$). Every statement of the series that applies `proj` assumes the relevant sets nonempty, closed and convex, so the junk value is never reached there; Theorem 5.1 uses the relational form `IsProj` directly.
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 220, Theorem 5.1 (definition of P_{K(u)}(z))

import Mathlib

namespace ChanPangGQVI.Shared

/-- Chan and Pang 1982, p. 220, Theorem 5.1: `p` is a nearest point of the set `S` to the point
`z`, i.e. `p ∈ S` and `‖p - z‖ ≤ ‖q - z‖` for every `q ∈ S` ("`p` solves `min_{x ∈ S} ‖x - z‖`").
The norm is the Euclidean norm of `EuclideanSpace ℝ (Fin n)`. -/
def IsProj {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) (z p : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  p ∈ S ∧ ∀ q ∈ S, ‖p - z‖ ≤ ‖q - z‖

/-- Chan and Pang 1982, p. 220: the projection `P_S(z) = sol min_{x ∈ S} ‖x - z‖` of the point
`z` on the set `S`. When a nearest point exists it is returned (for a nonempty closed convex `S`
it exists and is unique, so this is the paper's `P_S(z)`); otherwise the junk value `z` is
returned. Every statement of this series that uses `proj` assumes `S` nonempty, closed and
convex, so the junk branch is never reached there. -/
noncomputable def proj {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (z : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  by
    classical
    exact if h : ∃ p, IsProj S z p then h.choose else z

end ChanPangGQVI.Shared


