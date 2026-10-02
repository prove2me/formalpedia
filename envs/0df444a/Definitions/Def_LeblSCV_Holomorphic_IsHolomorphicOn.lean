-- Prove2me | Definitions.Def_LeblSCV_Holomorphic_IsHolomorphicOn
-- name    : LeblSCV_Holomorphic_IsHolomorphicOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:59:45.444283+00:00
-- url     : https://prove2.me/theorems/b4310c63-1c15-4447-bd1e-6c8fd4be5a71
-- title:
--   Definition 1.1.2 — holomorphic function of several variables
-- statement:
--   Let $U \subset \mathbb{C}^n$ be open. A function $f : U \to \mathbb{C}$ is **holomorphic** if it is
--
--   1. **locally bounded**: every $p \in U$ has a neighborhood $N$ such that $f|_N$ is bounded; and
--   2. **complex-differentiable in each variable separately**: for all $z \in U$ and all $k = 1, 2, \dots, n$ the limit
--   $$\lim_{\xi \in \mathbb{C} \to 0} \frac{f(z_1, \dots, z_k + \xi, \dots, z_n) - f(z)}{\xi}$$
--   exists.
--
--   This is the book's definition. Joint (Fréchet) complex differentiability and smoothness are not assumed: that holomorphic functions in this sense are $C^\infty$ and are given locally by convergent power series is the content of Proposition 1.1.3 and Theorem 1.2.1.
--
--   **Formalization Note.** $f$ is a function on all of `Fin n → ℂ`; only its values on $U$ enter (locally bounded is tested on $N \cap U$, and for $U$ open the separate derivatives at $z \in U$ only see $f$ near $z$). The limit is encoded as complex differentiability at $\xi = 0$ of $\xi \mapsto f(z_1, \dots, z_k + \xi, \dots, z_n)$, written with `Function.update`. Openness of $U$ is a hypothesis of every theorem using this definition.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 14, Definition 1.1.2

import Mathlib

open Filter

namespace LeblSCV.Holomorphic

/-- Definition 1.1.2 (Lebl, p. 14). A function `f` on an open set `U ⊆ ℂⁿ` is holomorphic if it is
locally bounded (every `p ∈ U` has a neighborhood `N` on which `f` is bounded) and
complex-differentiable in each variable separately: for every `z ∈ U` and every `k`, the limit
`lim_{ξ → 0} (f(z_1, …, z_k + ξ, …, z_n) - f(z)) / ξ` exists, i.e. the one-variable function
`ξ ↦ f(z_1, …, z_k + ξ, …, z_n)` is complex-differentiable at `ξ = 0`.
Only the values of `f` on `U` matter when `U` is open. -/
def IsHolomorphicOn {n : ℕ} (f : (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ)) : Prop :=
  (∀ p ∈ U, ∃ N ∈ nhds p, ∃ M : ℝ, ∀ w ∈ N ∩ U, ‖f w‖ ≤ M) ∧
  (∀ z ∈ U, ∀ k : Fin n,
    DifferentiableAt ℂ (fun ξ : ℂ => f (Function.update z k (z k + ξ))) 0)

end LeblSCV.Holomorphic


