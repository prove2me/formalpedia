-- Prove2me | Definitions.Def_ZORiem_RGD_zoGrad
-- name    : ZORiem_RGD_zoGrad
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:26.338755+00:00
-- url     : https://prove2.me/theorems/78acbe99-7cb7-43e8-a064-4d1e14626a4b
-- title:
--   Definition 2.6, (2.5), p. 7 — zeroth-order Riemannian gradient estimator g_µ(x)
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, $M\subseteq E$, $R$ a map $E\times E\to E$ (a retraction, $R_x(\eta)=R(x,\eta)$), $f:E\to\mathbb R$ and $\mu\neq0$ a smoothing parameter. For $x\in E$ let $P_x$ be the orthogonal projection onto the tangent space $T_xM$. Given a vector $u_0\in E$ (in the paper, a standard Gaussian draw $u_0\sim N(0,I_n)$), set $u=P_xu_0\in T_xM$. The **zeroth-order Riemannian gradient estimator** is
--
--   $$g_\mu(x)=\frac{f\big(R_x(\mu u)\big)-f(x)}{\mu}\,u=\frac{f\big(R_x(\mu P_xu_0)\big)-f(x)}{\mu}\,P_xu_0 .$$
--
--   It uses two function values only and always lies in $T_xM$, so it can be fed to the retraction. Two definitions are made: the projected direction $u=P_xu_0$ (`dir`) and the estimator (`zoGrad`), both as functions of the draw $u_0$.
--
--   **Formalization Note** The smoothing parameter is written `mu`. The estimator is a deterministic function of $u_0$; its expectation is taken against `stdGaussian E` in the theorems.
-- source:
--   Li, Balasubramanian and Ma, arXiv:2003.11238v3, Definition 2.6, (2.5), p. 7

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle

namespace ZORiem.RGD

open ProjLikeRetr.Retractor

/-- Definition 2.6, p. 7: the projected direction `u = P u₀ ∈ T_xM`, where `P` is the orthogonal
projection onto `T_xM`. -/
noncomputable def dir {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Set E) (x u₀ : E) : E :=
  (tangentSpace M x).starProjection u₀

/-- Definition 2.6, (2.5), p. 7: the zeroth-order Riemannian gradient estimator
`g_µ(x) = ((f(R_x(µ P u₀)) - f(x)) / µ) P u₀`, as a function of the draw `u₀ ∈ E`. -/
noncomputable def zoGrad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Set E) (R : E → E → E) (f : E → ℝ) (mu : ℝ) (x u₀ : E) : E :=
  ((f (R x (mu • dir M x u₀)) - f x) / mu) • dir M x u₀

end ZORiem.RGD


