-- Prove2me | Definitions.Def_TemporalAgg_IsLoadFunction
-- name    : TemporalAgg_IsLoadFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:37:02.999419+00:00
-- url     : https://prove2.me/theorems/57b4bdb7-b251-4264-9abb-e5ee9b65167b
-- title:
--   Definition 1.1 — load function
-- statement:
--   Let $\mathcal U$ be a set (the universe of realizations) and $n\in\mathbb N$. A function $f:\mathcal U^n\to\mathbb R_{\ge0}$ is a **load function** if for all $x=(x_1,\dots,x_n)$, $y=(y_1,\dots,y_n)\in\mathcal U^n$ and every $z\in\mathcal U^n$ with $z_i=x_i$ or $z_i=y_i$ for every $i$,
--
--   $$
--   f(z_1,\dots,z_n)\le f(x_1,\dots,x_n)+f(y_1,\dots,y_n).
--   $$
--
--   Splicing two inputs coordinatewise costs at most the sum of their loads. Congestion of a family of paths (the maximum over edges of the number of paths through the edge) and counts such as $\#\{i : x_i=b\}$ are load functions. Every load guarantee of the mission is about such an $f$.
--
--   **Formalization Note** Vectors are functions $\mathrm{Fin}\,n\to\mathcal U$, and $f$ is real-valued. Nonnegativity is not a separate condition: taking $x=y=z$ gives $f(x)\le 2f(x)$, so every load function in this sense is nonnegative, and the instances are those of the paper.
-- source:
--   Haeupler, Paramonov, Temporal Aggregation: Maintaining Randomness against Adaptive Adversaries, STOC 2027 submission (manuscript of 2026-11-03, sha256 42ebf866…), Definition 1.1, p.4

import Mathlib

namespace TemporalAgg

/-- **Load function** (Haeupler, Paramonov, *Temporal Aggregation: Maintaining Randomness against
Adaptive Adversaries*, STOC 2027 submission, manuscript of 2026-11-03, sha256 42ebf866…,
Definition 1.1, p.4).

A function `f : 𝒰ⁿ → ℝ≥0` is a load function if for all `x, y ∈ 𝒰ⁿ` and every `z` with
`zᵢ = xᵢ` or `zᵢ = yᵢ` for every `i`, `f z ≤ f x + f y`.

**Formalization Note** Vectors in `𝒰ⁿ` are functions `Fin n → U`. The codomain is `ℝ` rather
than `ℝ≥0`: nonnegativity is implied by the splice inequality (take `x = y = z`, so
`f x ≤ 2 f x`), hence the two definitions have the same instances. -/
def IsLoadFunction {U : Type*} {n : ℕ} (f : (Fin n → U) → ℝ) : Prop :=
  ∀ x y z : Fin n → U, (∀ i, z i = x i ∨ z i = y i) → f z ≤ f x + f y

end TemporalAgg


