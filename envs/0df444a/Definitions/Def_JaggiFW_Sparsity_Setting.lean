-- Prove2me | Definitions.Def_JaggiFW_Sparsity_Setting
-- name    : JaggiFW_Sparsity_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:03:24.160576+00:00
-- url     : https://prove2.me/theorems/b460783f-25dd-4e42-a3cf-dadb0d06900a
-- title:
--   Squared Euclidean norm, sparsity, duality gap and curvature on real coordinate vectors
-- statement:
--   Let a vector in $\mathbb R^n$ be indexed by $1,\ldots,n$. Define its squared Euclidean norm and sparsity by
--   $$
--   f(x)=\sum_{i=1}^n x_i^2,\qquad \operatorname{card}(x)=|\{i:x_i\ne0\}|.
--   $$
--   For a domain $D$ and a differentiable objective $h$, define its Frank–Wolfe duality gap at $x$ by
--   $$
--   g_{h,D}(x)=\sup_{s\in D} Dh(x)[x-s].
--   $$
--   The curvature set consists of the values
--   $$
--   \frac{2}{\gamma^2}\bigl(h(x+\gamma(s-x))-h(x)-Dh(x)[\gamma(s-x)]\bigr)
--   $$
--   for $x,s\in D$ and $0<\gamma\le1$; its supremum is the curvature constant. These objects support the sparse simplex lower bound and the paper's curvature example.
--
--   **Formalization Note** The coordinate sum represents the Euclidean squared norm, although the ambient Lean function type carries a supremum norm. The derivative applied to a direction represents the gradient pairing. The value $\gamma=0$ is excluded because the quotient there is undefined in the paper. The duality-gap supremum agrees with the paper's maximum when the domain is compact and nonempty; theorem statements using it provide that condition through the simplex and $n>0$.
-- source:
--   Jaggi, Revisiting Frank-Wolfe: Projection-Free Sparse Convex Optimization, ICML 2013 (JMLR W&CP 28), PDF pp. 2–3, (2), (3); p. 5, Lemmas 3–4

import Mathlib

namespace JaggiFW.Sparsity

/-- The squared Euclidean norm on real coordinate vectors (PDF p. 5). -/
def sqNorm {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ 2

/-- The number of nonzero coordinates of a vector (PDF p. 5). -/
noncomputable def card {n : ℕ} (x : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ 0)).card

/-- The Frank–Wolfe duality gap of display (2), PDF p. 2. -/
noncomputable def dualityGap {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (D : Set (Fin n → ℝ)) (x : Fin n → ℝ) : ℝ :=
  sSup ((fun s => fderiv ℝ f x (x - s)) '' D)

/-- The set whose supremum is the curvature constant in display (3), PDF p. 3. -/
def curvatureSet {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (D : Set (Fin n → ℝ)) : Set ℝ :=
  {c | ∃ x ∈ D, ∃ s ∈ D, ∃ γ ∈ Set.Ioc (0 : ℝ) 1,
    c = 2 / γ ^ 2 *
      (f (x + γ • (s - x)) - f x - fderiv ℝ f x (γ • (s - x)))}

end JaggiFW.Sparsity


