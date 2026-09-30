-- Prove2me | Definitions.Def_TierneyMH_Peskun_lagInner
-- name    : TierneyMH_Peskun_lagInner
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T12:20:59.699862+00:00
-- url     : https://prove2.me/theorems/0f0a10fe-880c-451c-9b7f-16a211899923
-- title:
--   Lag-$k$ inner product $\langle f, H^k f\rangle$ in $L^2(\pi)$
-- statement:
--   Let $\pi$ be a measure and $H$ a transition kernel on a measurable space $E$. For $k \ge 0$ let $H^k$ be the $k$-fold composition of $H$ (with $H^0(x,\cdot) = \delta_x$), acting on functions by $(H^k f)(x) = \int f(y)\, H^k(x, dy)$. For $f : E \to \mathbb R$ the **lag-$k$ inner product** is
--
--   $$
--   \langle f, H^k f \rangle \;=\; \int_E f(x) \Bigl( \int_E f(y)\, H^k(x, dy) \Bigr) \pi(dx).
--   $$
--
--   In particular $\langle f, H^0 f\rangle = \int f^2\, d\pi$. When $X_0, X_1, \dots$ is a stationary chain with kernel $H$ started from $\pi$ and $\int f\, d\pi = 0$, this is the lag-$k$ autocovariance $\operatorname{Cov}(f(X_0), f(X_k))$.
--
--   **Formalization Note** $H^k$ is the $k$-th power in Mathlib's monoid of kernels on $E$ (multiplication is kernel composition). Integrals are Bochner integrals.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 5, proof of Theorem 4 (the quantities ⟨f, H^n f⟩)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace TierneyMH.Peskun

/-- The lag-`k` inner product `⟨f, Hᵏ f⟩ = ∫ f(x) (∫ f(y) Hᵏ(x, dy)) π(dx)` in `L²(π)`, where
`Hᵏ` is the `k`-fold composition of the kernel `H` (`H ^ 0` is the identity kernel, so
`lagInner π H f 0 = ∫ f² dπ`). -/
noncomputable def lagInner {E : Type*} [MeasurableSpace E] (π : Measure E) (H : Kernel E E)
    (f : E → ℝ) (k : ℕ) : ℝ :=
  ∫ x, f x * ∫ y, f y ∂((H ^ k) x) ∂π

end TierneyMH.Peskun


