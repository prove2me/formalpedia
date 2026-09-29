-- Prove2me | Definitions.Def_RandomGradFree_Shared_smoothing
-- name    : RandomGradFree_Shared_smoothing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T06:29:48.456985+00:00
-- url     : https://prove2.me/theorems/af70eb77-df1e-4f5f-9e0c-353ef64e6911
-- title:
--   Gaussian smoothing $f_\mu(x) = \mathbb E_u f(x+\mu u)$ (Eq. (9))
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with norm $\|\cdot\|$, and let $u$ be a standard Gaussian random vector in $E$ (its coordinates in any orthonormal basis are independent $N(0,1)$ variables, i.e. $u$ has density $\kappa^{-1}e^{-\|u\|^2/2}$). For a function $f : E \to \mathbb R$ and a smoothing parameter $\mu \in \mathbb R$, the **Gaussian approximation** of $f$ is
--
--   $$
--   f_\mu(x) = \mathbb E_u\, f(x + \mu u) = \frac{1}{\kappa}\int_E f(x+\mu u)\, e^{-\frac12\|u\|^2}\,du, \qquad x \in E.
--   $$
--
--   This is the object on which every random gradient-free method of Nesterov and Spokoiny is built: the finite-difference oracle is an unbiased estimate of $\nabla f_\mu$, and $f_\mu$ stays close to $f$ ($\mu L_0(f) n^{1/2}$ for Lipschitz $f$, $\frac{\mu^2}{2}L_1(f)\,n$ for $f$ with Lipschitz gradient).
--
--   It serves chunk 01-nonsmooth-random-search (p. 532, Eqs. (9)-(10); used in Eq. (11) and the convexity bullet p. 533, Theorem 1 (18) p. 534, Eq. (21) pp. 534-535, Theorem 2 p. 535), chunk 02-smooth-random-search (p. 532; Eq. (11) and convexity p. 533, Theorem 1 (19) p. 534, Eq. (21) pp. 534-535) and chunk 03-accelerated-random-search (p. 532; Eqs. (11)-(12) p. 533, Theorem 1 (19) p. 534, Eq. (21) pp. 534-535, Lemma 5 p. 539).
--
--   **Formalization Note** The expectation is the Bochner integral against Mathlib's `stdGaussian E`. The paper's space $E$ with operator $B$ is modelled by choosing the inner product $\langle Bx, y\rangle$; then the paper's Gaussian with correlation operator $B^{-1}$ is the standard Gaussian of $E$; the σ-algebra on $E$ is the Borel one. The integral is only meaningful when $u \mapsto f(x+\mu u)$ is Gaussian-integrable; every theorem using this definition assumes $f$ Lipschitz (chunk 01) or $f$ with Lipschitz gradient (chunks 02, 03), which guarantees it.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 532, Section 2, Eqs. (9)-(10)

import Mathlib

namespace RandomGradFree.Shared

open MeasureTheory ProbabilityTheory

/-- Gaussian approximation (Nesterov–Spokoiny, Eq. (9)):
`f_μ(x) = E_u f(x + μ u)` with `u` a standard Gaussian vector of `E`. -/
noncomputable def smoothing {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (f : E → ℝ) (μ : ℝ) (x : E) : ℝ :=
  ∫ u, f (x + μ • u) ∂(stdGaussian E)

end RandomGradFree.Shared


