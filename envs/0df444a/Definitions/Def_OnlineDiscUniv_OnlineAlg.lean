-- Prove2me | Definitions.Def_OnlineDiscUniv_OnlineAlg
-- name    : OnlineDiscUniv_OnlineAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:07.991715+00:00
-- url     : https://prove2.me/theorems/8039e982-e7fc-4a0d-8315-6d9438cd7b65
-- title:
--   Randomized online algorithms, the input law and the discrepancy $D_{M,N}$
-- statement:
--   Vectors $\xi_1,\dots,\xi_N\in\mathbb R^M$ arrive one at a time; their $MN$ entries are independent with common law $\mu$. A **randomized online algorithm** with seed space $S$ uses a seed $U\in S$ independent of the input and chooses
--   $$
--   \varepsilon_k=A_{k,M,N}(U,\xi_1,\dots,\xi_k)\in\{-1,+1\},\qquad 1\le k\le N .
--   $$
--   Its normalized terminal discrepancy is
--   $$
--   D_{M,N}:=\Big\|\frac1{\sqrt N}\sum_{k=1}^N\varepsilon_k\xi_k\Big\|_\infty=\max_{1\le i\le M}\Big|\frac1{\sqrt N}\sum_{k=1}^N\varepsilon_k\xi_{k,i}\Big|.
--   $$
--
--   **Formalization Note** The input is a function $\xi:\{0,\dots,N-1\}\times\{0,\dots,M-1\}\to\mathbb R$ (column $k$ is the paper's $\xi_{k+1}$) with law the product of $\mu$ over all entries. Causality: the $k$-th sign takes equal values on inputs that agree in columns $0,\dots,k$. Each sign map is required to be jointly measurable in (seed, input), which the paper uses implicitly when it takes probabilities and expectations. The norm is the sup norm on $\mathbb R^M$.
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), §2.1, (2.1), p.5 (PDF p.6); p.1 (PDF p.2)

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace OnlineDiscUniv

/-- A **randomized online algorithm** for `N` vectors in `ℝ^M` with seed space `S` (Jo–Lee,
arXiv:2610.00103, artifact sha256 cb190f12…, §2.1, printed p.5, PDF p.6): signs
`ε_k = A_{k,M,N}(U, ξ_1, …, ξ_k) ∈ {−1, +1}`.

**Formalization Note** The input is `ξ : Fin N → Fin M → ℝ`, column `k` (0-based) being the
vector `ξ_{k+1}` of the paper. `sign k (u, ξ)` is the sign chosen for column `k` with seed `u`.
Causality is written as: `sign k (u, ξ) = sign k (u, ξ')` whenever `ξ` and `ξ'` agree in columns
`0, …, k` (so the sign may not depend on any later column). Joint measurability in
`(seed, input)` is required; it is implicit in the paper, where the probabilities and expectations
of the resulting discrepancy must be defined. -/
structure OnlineAlg (S : Type*) [MeasurableSpace S] (M N : ℕ) where
  sign : Fin N → S × (Fin N → Fin M → ℝ) → ℝ
  sign_pm : ∀ k p, sign k p = 1 ∨ sign k p = -1
  measurable_sign : ∀ k, Measurable (sign k)
  causal : ∀ (k : Fin N) (u : S) (ξ ξ' : Fin N → Fin M → ℝ),
    (∀ j : Fin N, j ≤ k → ξ j = ξ' j) → sign k (u, ξ) = sign k (u, ξ')

/-- The law of the input `(ξ_1, …, ξ_N)` (Jo–Lee, arXiv:2610.00103, §2.1, p.5, PDF p.6): the
`N` columns are independent and each has `M` i.i.d. coordinates of law `μ`. -/
noncomputable def inputLaw (μ : Measure ℝ) (M N : ℕ) : Measure (Fin N → Fin M → ℝ) :=
  Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin M => μ

/-- The normalized terminal discrepancy `D_{M,N} = ‖X_N‖_∞`, `X_N = N^{-1/2} ∑_k ε_k ξ_k`
(Jo–Lee, arXiv:2610.00103, (2.1), p.5, PDF p.6; p.1, PDF p.2), for seed `u` and input `ξ`.

**Formalization Note** The norm is Mathlib's sup norm on `Fin M → ℝ`, i.e. the maximum of the
absolute values of the `M` coordinates (`0` when `M = 0`). -/
noncomputable def disc {S : Type*} [MeasurableSpace S] {M N : ℕ} (A : OnlineAlg S M N) (u : S)
    (ξ : Fin N → Fin M → ℝ) : ℝ :=
  ‖(1 / Real.sqrt N) • ∑ k : Fin N, A.sign k (u, ξ) • ξ k‖

end OnlineDiscUniv


