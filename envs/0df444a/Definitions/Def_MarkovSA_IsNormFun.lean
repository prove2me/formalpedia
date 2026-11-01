-- Prove2me | Definitions.Def_MarkovSA_IsNormFun
-- name    : MarkovSA_IsNormFun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:10.899979+00:00
-- url     : https://prove2.me/theorems/a87b4a91-c5d8-4f39-aabc-a9741fa8be4c
-- title:
--   Norm axioms for a function $m:E\to\mathbb R$
-- statement:
--   A function $m:E\to\mathbb R$ on a real vector space $E$ **satisfies the norm axioms** if for all $x,y\in E$ and $c\in\mathbb R$:
--
--   1. $m(x)=0$ if and only if $x=0$;
--   2. $m(x+y)\le m(x)+m(y)$;
--   3. $m(cx)=|c|\,m(x)$.
--
--   Nonnegativity follows. The paper uses two such functions besides the contraction norm: the smoothing norm $\|\cdot\|_s$ of the notation paragraph of Appendix A and the norm $\|\cdot\|_m$ of Proposition A.1 (2).
--
--   **Formalization Note** The contraction norm $\|\cdot\|_c$ is the norm of the space $E$; the other norms are functions with these axioms rather than a second norm structure on $E$.
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, Appendix A, Notation, p.24, and Proposition A.1 (2), p.25

import Mathlib

namespace MarkovSA

/-- `m : E → ℝ` satisfies the **norm axioms**: definiteness, the triangle inequality and absolute
homogeneity (nonnegativity follows). Used for the auxiliary norm `‖·‖_s` of the Notation paragraph
(Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, Appendix A, p.24) and for the norm `‖·‖_m` of Proposition A.1 (2), p.25.

**Formalization Note.** `‖·‖_s` is a function with the norm axioms, not a second `Norm` instance on `E`;
the ambient norm `‖·‖` of `E` is the contraction norm `‖·‖_c`. -/
def IsNormFun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (m : E → ℝ) : Prop :=
  (∀ x, m x = 0 ↔ x = 0) ∧ (∀ x y, m (x + y) ≤ m x + m y) ∧ ∀ (c : ℝ) x, m (c • x) = |c| * m x

end MarkovSA


