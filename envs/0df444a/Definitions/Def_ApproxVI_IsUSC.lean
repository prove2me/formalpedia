-- Prove2me | Definitions.Def_ApproxVI_IsUSC
-- name    : ApproxVI_IsUSC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:32.632017+00:00
-- url     : https://prove2.me/theorems/1885a92e-56af-4d99-bef0-6f448c7284b1
-- title:
--   Upper-semicontinuous set-valued map (sequential closed graph)
-- statement:
--   A set-valued map $H:\mathbb R^{d_1}\to\{\text{subsets of }\mathbb R^{d_2}\}$ is **upper-semicontinuous** if, whenever $x_n\to x$ in $\mathbb R^{d_1}$, $y_n\to y$ in $\mathbb R^{d_2}$ and $y_n\in H(x_n)$ for all $n$, then $y\in H(x)$.
--
--   This is the closed-graph property used in the definition of a Marchaud map.
--
--   **Formalization Note** Sequences are indexed from $0$ instead of $1$, which changes nothing; $\mathbb R^{d_i}$ carries its usual topology.
-- source:
--   Ramaswamy & Bhatnagar, Analyzing Approximate Value Iteration Algorithms, arXiv:1709.04673v5, §2, p.4

import Mathlib

namespace ApproxVI

open Filter Topology

/-- Upper-semicontinuity of a set-valued map, Ramaswamy & Bhatnagar, *Analyzing Approximate
Value Iteration Algorithms*, arXiv:1709.04673v5, §2, p.4: `H` is upper-semicontinuous if given
sequences `{xₙ}` in `ℝ^{d₁}` and `{yₙ}` in `ℝ^{d₂}` with `xₙ → x`, `yₙ → y` and
`yₙ ∈ H(xₙ)`, `n ≥ 1`, then `y ∈ H(x)` (the sequential closed-graph property).

**Formalization Note** `ℝ^{dᵢ}` is `Fin dᵢ → ℝ` with its product topology (the topology of
every norm on `ℝ^{dᵢ}`); a set-valued map is a function into `Set`. Sequences are indexed by
`ℕ` instead of `n ≥ 1`, which changes nothing. -/
def IsUSC {d₁ d₂ : ℕ} (H : (Fin d₁ → ℝ) → Set (Fin d₂ → ℝ)) : Prop :=
  ∀ (xs : ℕ → Fin d₁ → ℝ) (ys : ℕ → Fin d₂ → ℝ) (x : Fin d₁ → ℝ) (y : Fin d₂ → ℝ),
    Tendsto xs atTop (𝓝 x) → Tendsto ys atTop (𝓝 y) → (∀ n, ys n ∈ H (xs n)) → y ∈ H x

end ApproxVI


