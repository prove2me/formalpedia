-- Prove2me | Definitions.Def_RandomGradFree_Shared_moment
-- name    : RandomGradFree_Shared_moment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T06:39:01.506025+00:00
-- url     : https://prove2.me/theorems/bce05f75-25c0-43fe-8398-ce02c905ac6c
-- title:
--   Gaussian moments $M_p = \mathbb E_u \|u\|^p$
-- statement:
--   Let $E$ be a finite-dimensional real inner product space and $u$ a standard Gaussian random vector in $E$. For a real exponent $p$, the **$p$-th Gaussian moment** is
--
--   $$
--   M_p = \mathbb E_u \|u\|^p = \frac{1}{\kappa}\int_E \|u\|^p e^{-\frac12\|u\|^2}\,du .
--   $$
--
--   These moments control the variance of the random gradient-free oracles; for instance $M_0 = 1$ and $M_2 = n$ where $n = \dim E$.
--
--   It serves chunks 01-nonsmooth-random-search, 02-smooth-random-search and 03-accelerated-random-search, each at p. 533 (definition of $M_p$ before Eq. (15)) and in Lemma 1, Eqs. (16)-(17), p. 534.
--
--   **Formalization Note** $\|u\|^p$ is the real power `Real.rpow`, so $p$ ranges over $\mathbb R$ (with $0^0 = 1$). The integral is against `stdGaussian E` on the Borel σ-algebra of $E$; for $p \ge 0$, the only exponents the paper uses, the integrand is integrable.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 533, Section 2, definition of M_p before Eq. (15)

import Mathlib

namespace RandomGradFree.Shared

open MeasureTheory ProbabilityTheory

/-- Gaussian moments (Nesterov–Spokoiny, p. 533): `M_p = E_u ‖u‖^p` for a standard
Gaussian vector `u` of `E`, with a real exponent `p`. -/
noncomputable def moment (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (p : ℝ) : ℝ :=
  ∫ u, ‖u‖ ^ p ∂(stdGaussian E)

end RandomGradFree.Shared


