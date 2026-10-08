-- Prove2me | Definitions.Def_GeometryOfGraphs_Clique_IsNormFun
-- name    : GeometryOfGraphs_Clique_IsNormFun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:09:59.323452+00:00
-- url     : https://prove2.me/theorems/4fa7ebb9-7ef9-40a1-9c4e-31407f287bdd
-- title:
--   Norm on real coordinate space
-- statement:
--   A **norm** on the real vector space $\mathbb R^d$ is a function $N:\mathbb R^d\to\mathbb R$ such that, for all vectors $u,v$ and scalars $a$,
--
--   $$
--   N(u)\ge 0,\quad N(u)=0\Rightarrow u=0,\quad N(au)=|a|N(u),\quad N(u+v)\le N(u)+N(v).
--   $$
--
--   These are the three norm axioms used throughout the paper. They distinguish a norm from a seminorm and provide the target spaces in the isometric-dimension definition.
--
--   **Formalization Note** A real $d$-dimensional vector space is represented by functions from a $d$-element coordinate set to $\mathbb R$, and the norm by a real-valued function on it satisfying the axioms above. This loses nothing: every $d$-dimensional real normed space is linearly isometric to $\mathbb R^d$ equipped with some such function. The condition $N(0)=0$ is not listed separately because it follows from homogeneity with $a=0$.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 218, norm axioms in Section 2

import Mathlib

namespace GeometryOfGraphs.Clique

/-- A norm on real coordinate space, expressed as a function. -/
def IsNormFun {d : ℕ} (N : (Fin d → ℝ) → ℝ) : Prop :=
  (∀ x, 0 ≤ N x) ∧
  (∀ x, N x = 0 → x = 0) ∧
  (∀ (a : ℝ) x, N (a • x) = |a| * N x) ∧
  (∀ x y, N (x + y) ≤ N x + N y)

end GeometryOfGraphs.Clique


