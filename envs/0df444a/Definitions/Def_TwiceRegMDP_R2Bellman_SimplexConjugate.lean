-- Prove2me | Definitions.Def_TwiceRegMDP_R2Bellman_SimplexConjugate
-- name    : TwiceRegMDP_R2Bellman_SimplexConjugate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:06:16.687897+00:00
-- url     : https://prove2.me/theorems/05d281e1-7548-443c-8cf1-608c440134a3
-- title:
--   Legendre–Fenchel transform $\Omega^*$ of a function on the simplex
-- statement:
--   Let $\mathcal Z$ be a finite set, $\Delta_{\mathcal Z}$ the probability simplex of functions $a:\mathcal Z\to[0,1]$ with $\sum_z a(z)=1$, and $\Omega:\Delta_{\mathcal Z}\to\mathbb R$. Its Legendre–Fenchel transform over the simplex is
--   $$\Omega^*(y)=\max_{a\in\Delta_{\mathcal Z}}\ \langle a,y\rangle-\Omega(a),\qquad y\in\mathbb R^{\mathcal Z},$$
--   with $\langle a,y\rangle=\sum_z a(z)y(z)$. This is the "smoothed max" operator that turns a policy regularizer into a regularized Bellman optimality operator.
--
--   **Formalization Note.** `Ω` is a function on all of `Z → ℝ` but only its values on the simplex are used. The maximum is the real supremum of the image of the simplex; for continuous $\Omega$ on a nonempty $\mathcal Z$ it is attained.
-- source:
--   Derman, Geist and Mannor, Twice regularized MDPs and the equivalence between robustness and regularization, arXiv:2110.06267v1, p. 2 (Notations: Legendre–Fenchel transform) and p. 3 (Convex Analysis, Proposition 2.1)

import Mathlib

namespace TwiceRegMDP.R2Bellman

/-- The Legendre–Fenchel transform of `Ω : Δ_Z → ℝ`, taken over the simplex (p. 3):
`Ω^∗(y) = max_{a ∈ Δ_Z} ⟨a, y⟩ − Ω(a)`, written as the real supremum of the image of the simplex
(values of `Ω` off the simplex are never used). -/
noncomputable def simplexConj {Z : Type} [Fintype Z] (Ω : (Z → ℝ) → ℝ) (y : Z → ℝ) : ℝ :=
  sSup ((fun a : Z → ℝ => ∑ z, a z * y z - Ω a) '' stdSimplex ℝ Z)

end TwiceRegMDP.R2Bellman


