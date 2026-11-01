-- Prove2me | Definitions.Def_HomotopyProxVM_IsExactRun
-- name    : HomotopyProxVM_IsExactRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:23.5213+00:00
-- url     : https://prove2.me/theorems/cce92f5f-c436-4f15-8351-1006947fe51c
-- title:
--   A run of the exact scheme (12)
-- statement:
--   A sequence $\{x^k\}$ is a **run of the exact scheme** (12) from $x^0$ with metrics $\{H_k\}$ and parameters $\{\tau_k\}$ if $x^0$ is its first term and, for every $k\ge0$,
--
--   $$
--   x^{k+1}=\operatorname{prox}^{H_k}_{\frac{1}{\tau_{k+1}}g}\Bigl(x^k-H_k^{-1}\bigl(\nabla f(x^k)-(\tfrac{1}{\tau_{k+1}}-1)\xi^0\bigr)\Bigr).
--   $$
--
--   Step $k$ uses $\tau_{k+1}$ and $H_k$, and the vector $\xi^0$ is computed once at $x^0$ and fixed for the whole run.
-- source:
--   Tran-Dinh, Liang & Toh, A New Homotopy Proximal Variable-Metric Framework for Composite Convex Minimization, arXiv:1812.05243v1, Algorithm 1, (12), p.7

import Mathlib
import Definitions.Def_HomotopyProxVM_IsExactStep

namespace HomotopyProxVM

/-- A run `{(xᵏ, τ_k)}` of the exact scheme (12) of Algorithm 1, Stage 2, from `x⁰`, with metrics
`H_k` (Tran-Dinh, Liang & Toh, arXiv:1812.05243v1, Algorithm 1, (12), p.7): `x 0 = x₀`, and step `k` uses `τ_{k+1}` and `H_k`.

**Formalization Note.** `ξ` is one fixed vector for the whole run, the subgradient `ξ⁰` computed
once at `x⁰`. -/
def IsExactRun {p : ℕ} (f : EuclideanSpace ℝ (Fin p) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin p))) (g : EuclideanSpace ℝ (Fin p) → ℝ)
    (ξ : EuclideanSpace ℝ (Fin p)) (H : ℕ → Matrix (Fin p) (Fin p) ℝ) (τ : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin p)) (x : ℕ → EuclideanSpace ℝ (Fin p)) : Prop :=
  x 0 = x₀ ∧ ∀ k, IsExactStep f D g ξ (H k) (τ (k + 1)) (x k) (x (k + 1))

end HomotopyProxVM


