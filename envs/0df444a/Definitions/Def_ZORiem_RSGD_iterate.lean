-- Prove2me | Definitions.Def_ZORiem_RSGD_iterate
-- name    : ZORiem_RSGD_iterate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T11:02:32.323451+00:00
-- url     : https://prove2.me/theorems/1704a631-6d46-4490-b8e9-edf0b4c02795
-- title:
--   Algorithm 2 (ZO-RSGD), p. 17 — the random iterate sequence and its probability space
-- statement:
--   **Zeroth-order Riemannian stochastic gradient descent (ZO-RSGD)** with constant step size $\eta$, smoothing parameter $\mu$ and batch size $m$ starts from $x_0$ and, at every iteration $k = 0, 1, 2, \dots$, draws a fresh batch $\omega_k = (u^k_{0,i}, \xi^k_i)_{i=1}^m$, computes the mini-batch estimator $\bar g_{\mu,\xi}(x_k)$ of (3.6) from it (with the Gaussian directions projected onto $T_{x_k}\mathcal M$), and updates
--
--   $$x_{k+1} = R_{x_k}\big(-\eta\,\bar g_{\mu,\xi}(x_k)\big).$$
--
--   The iterates are random variables on the sequence space $\Omega = ((E \times \Xi)^m)^{\mathbb N}$ equipped with the product of countably many copies of the law of one batch, so the batches $\omega_0, \omega_1, \dots$ are independent and identically distributed.
--
--   **Formalization Note** `iterate M R F mu η m x₀ k ω` is $x_k$ on the path $\omega$, defined by recursion on $k$; `pathLaw E Pξ m` is `Measure.infinitePi` of `batchLaw E Pξ m`. The algorithm is run without a stopping index, so $x_k$ exists for every $k$ (the convergence bound sums over $k = 0, \dots, N$ and uses $x_{N+1}$).
-- source:
--   Li, Balasubramanian and Ma, arXiv:2003.11238v3, Algorithm 2, p. 17

import Mathlib
import Definitions.Def_ZORiem_RSGD_zoGradBatch

namespace ZORiem.RSGD

open MeasureTheory ProbabilityTheory

/-- Algorithm 2 (ZO-RSGD), p. 17, with constant step `η`, run without a stopping time: `ω k` is
the `k`-th batch of draws `(u₀ᵢᵏ, ξᵢᵏ)_{i ≤ m}`, `x_0 = x₀` and
`x_{k+1} = R_{x_k}(−η ḡ_{µ,ξ}(x_k))`, where `ḡ_{µ,ξ}(x_k)` is computed from the batch `ω k` and
the directions are projected onto `T_{x_k}M`. -/
noncomputable def iterate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {Ξ : Type*} (M : Set E) (R : E → E → E) (F : E → Ξ → ℝ)
    (mu η : ℝ) (m : ℕ) (x₀ : E) : ℕ → (ℕ → Fin m → E × Ξ) → E
  | 0, _ => x₀
  | k + 1, ω => R (iterate M R F mu η m x₀ k ω)
      (-η • zoGradBatch M R F mu m (iterate M R F mu η m x₀ k ω) (ω k))

/-- The probability space of Algorithm 2: an i.i.d. sequence of batches, each with law
`batchLaw E Pξ m`. -/
noncomputable def pathLaw (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {Ξ : Type*} [MeasurableSpace Ξ]
    (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ] (m : ℕ) : Measure (ℕ → Fin m → E × Ξ) :=
  Measure.infinitePi (fun _ : ℕ => batchLaw E Pξ m)

end ZORiem.RSGD


