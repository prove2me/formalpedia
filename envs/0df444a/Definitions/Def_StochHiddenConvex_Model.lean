-- Prove2me | Definitions.Def_StochHiddenConvex_Model
-- name    : StochHiddenConvex_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:50:18.799505+00:00
-- url     : https://prove2.me/theorems/d00305d9-d28e-4891-8f0b-7f2e375975d6
-- title:
--   The model of problem (1): box $\mathcal X$, law $\mathbb P(\xi)$, separable $\phi$, $f$, $g=\mathbb E\phi$ and $F$
-- statement:
--   The data of the stochastic problem
--   $$\min_{x\in\mathcal X}F(x):=\mathbb E_{\xi\sim\mathbb P(\xi)}\big[f(\phi(x,\xi))\big]\qquad(1)$$
--   are: a box $\mathcal X=[\underline X_1,\bar X_1]\times\dots\times[\underline X_d,\bar X_d]\subseteq\mathbb R^d$; the law $\mathbb P(\xi)$ of a random vector $\xi\in\mathbb R^d$; a **separable** random function $\phi(x,\xi)=(\phi_1(x_1,\xi_1),\dots,\phi_d(x_d,\xi_d))^\top$; and an outer function $f:\mathbb R^d\to\mathbb R$. From these the definition builds
--
--   1. the box $\mathcal X$;
--   2. the vector $\phi(x,\xi)$;
--   3. the **transformation** $g(x):=\mathbb E_\xi[\phi(x,\xi)]$, coordinate by coordinate $g_i(x_i)=\mathbb E[\phi_i(x_i,\xi_i)]$, defined at every $x\in\mathbb R^d$;
--   4. the objective $F(x)=\mathbb E_\xi[f(\phi(x,\xi))]$.
--
--   The change of variables $u=g(x)$ is what turns (1) into the convex problem (3).
--
--   **Formalization Note** Vectors live in `EuclideanSpace ℝ (Fin d)` (the $\ell_2$ norm of p.8); samples $\xi$ live in `Fin d → ℝ` with law `P`. Expectations are Bochner integrals; the assumptions under which they exist are separate predicates. No assumption is bundled into the structure.
-- source:
--   X. Chen, N. He, Y. Hu, Z. Ye, Efficient Algorithms for A Class of Stochastic Hidden Convex Optimization and Its Applications in Network Revenue Management, arXiv:2205.01774v3, Eq. (1), p.1; Eq. (3), p.8

import Mathlib

open MeasureTheory

namespace StochHiddenConvex

/-- The Euclidean space `ℝ^d` (with the `ℓ₂` norm of Chen, He, Hu & Ye, arXiv:2205.01774v3,
Preliminaries, p.8) in which the decision `x`, the transformed variable `u` and the value
`ϕ(x, ξ)` live. -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The data of problem (1) of Chen, He, Hu & Ye, arXiv:2205.01774v3, Eq. (1), p.1:
`min_{x∈𝒳} F(x) := 𝔼_{ξ∼ℙ(ξ)}[f(ϕ(x, ξ))]` with
`𝒳 = [X̲₁, X̄₁] × … × [X̲_d, X̄_d] ⊆ ℝ^d`, a random vector `ξ ∈ ℝ^d` with law `ℙ(ξ)`,
a separable random function `ϕ(x, ξ) = (ϕ₁(x₁, ξ₁), …, ϕ_d(x_d, ξ_d))ᵀ` and an outer function `f`.

* `lo i = X̲ᵢ`, `hi i = X̄ᵢ` (the box);
* `P = ℙ(ξ)`, the law of `ξ` on `ℝ^d` (here `Fin d → ℝ`);
* `phi i y t = ϕᵢ(y, t)`, the `i`-th component evaluated at `xᵢ = y` and `ξᵢ = t`;
* `f : ℝ^d → ℝ`.

**Formalization Note.** No assumption is bundled here: every assumption of the paper is a
separate predicate (`Def_StochHiddenConvex_Model_Assumptions`). -/
structure Model (d : ℕ) where
  /-- lower corner `X̲` of the box `𝒳` -/
  lo : Fin d → ℝ
  /-- upper corner `X̄` of the box `𝒳` -/
  hi : Fin d → ℝ
  /-- the law `ℙ(ξ)` of the random vector `ξ` -/
  P : Measure (Fin d → ℝ)
  /-- the components `ϕᵢ(xᵢ, ξᵢ)` of the random function `ϕ` -/
  phi : Fin d → ℝ → ℝ → ℝ
  /-- the outer function `f` -/
  f : Vec d → ℝ

namespace Model

variable {d : ℕ} (M : Model d)

/-- The box `𝒳 = [X̲₁, X̄₁] × … × [X̲_d, X̄_d]` (arXiv:2205.01774v3, p.1). -/
def box : Set (Vec d) := {x | ∀ i, M.lo i ≤ x i ∧ x i ≤ M.hi i}

/-- The separable random function `ϕ(x, ξ) = (ϕ₁(x₁, ξ₁), …, ϕ_d(x_d, ξ_d))ᵀ` (p.1). -/
def phiVec (x : Vec d) (s : Fin d → ℝ) : Vec d :=
  WithLp.toLp 2 (fun i => M.phi i (x i) (s i))

/-- The `i`-th coordinate of the transformation `g`, as a function of the scalar `y = xᵢ`:
`gᵢ(y) = 𝔼[ϕᵢ(y, ξᵢ)]` (arXiv:2205.01774v3, (3), p.8). -/
noncomputable def gc (i : Fin d) (y : ℝ) : ℝ := ∫ s, M.phi i y (s i) ∂M.P

/-- The transformation `g(x) := 𝔼_{ξ∼ℙ(ξ)}[ϕ(x, ξ)]` (arXiv:2205.01774v3, (3), p.8). It is
defined on all of `ℝ^d`; the paper uses it on `𝒳` and, in the proof of Theorem 3.2 (p.38),
at the points `x^t − γ v_F(x^t)`. -/
noncomputable def g (x : Vec d) : Vec d := WithLp.toLp 2 (fun i => M.gc i (x i))

/-- The objective `F(x) := 𝔼_{ξ∼ℙ(ξ)}[f(ϕ(x, ξ))]` of problem (1) (arXiv:2205.01774v3, p.1).

**Formalization Note.** A Bochner integral; it is the paper's expectation when
`f(ϕ(x, ·))` is integrable, which the assumption `IntegrableObjective` provides on `𝒳`. -/
noncomputable def F (x : Vec d) : ℝ := ∫ s, M.f (M.phiVec x s) ∂M.P

end Model

end StochHiddenConvex


