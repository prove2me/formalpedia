-- Prove2me | Definitions.Def_SubmodSparsify_lovasz
-- name    : SubmodSparsify_lovasz
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:21:36.753925+00:00
-- url     : https://prove2.me/theorems/ea546167-271e-4805-9479-cdc018c31ca4
-- title:
--   Lovász extension $\hat f$ (display (11))
-- statement:
--   Let $E$ be a finite ground set and $f : 2^E \to \mathbb R$ a set function with $f(\emptyset) = 0$. Its **Lovász extension** is the function on $\mathbb R^E_{\ge 0}$
--
--   $$\hat f(z) := \int_0^\infty f\bigl(\{v \in E : z(v) \ge \lambda\}\bigr)\, d\lambda .$$
--
--   For $z \ge 0$ the integrand is a step function of $\lambda$ that vanishes once $\lambda$ exceeds $\max_E z$, so the integral is a finite sum over the level sets of $z$ (the greedy formula (12)). The mission uses it to state $H(x^*) = \langle b_h, x^* \rangle$ (Lemma 4.2, Item 1) and $s_i = \hat h_i(x^*)$ (Lemma 4.2, Item 4).
--
--   **Formalization Note** Vectors of $\mathbb R^E$ are functions $\alpha \to \mathbb R$ of which only the coordinates in $E$ are read; the integral is the Bochner integral over $(0, \infty)$. If $f(\emptyset) \ne 0$ the integrand is not integrable and Lean returns $0$; the paper defines $\hat f$ only for $f(\emptyset) = 0$, and every use in the mission has $f(\emptyset) = 0$.
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6…), display (11), p.16 (PDF p.18); Conventions, p.8 (PDF p.10)

import Mathlib

namespace SubmodSparsify

/-- **Lovász extension** (display (11), p.16).

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held).

"The Lovász extension [Lov82] of a submodular function f with f(∅) = 0 is
f̂(z) := ∫₀^∞ f({i : z(i) ≥ λ}) dλ for z ∈ Rⁿ≥0."

`lovasz E f z` is `∫₀^∞ f({v ∈ E : z v ≥ λ}) dλ`, the Lovász extension of a set function `f` on
the ground set `E`, evaluated at the vector `z`.

**Formalization Note.**
* The ground set is a `Finset E` of an arbitrary type `α`; a vector of `ℝ^E` is a function
  `z : α → ℝ` of which only the coordinates in `E` are read.
* The integral is the Bochner integral over `(0, ∞)`. For `f ∅ = 0` (the paper's hypothesis)
  and `z ≥ 0` on `E` the integrand is a step function that vanishes for `λ > max_E z`, so the
  integral is the paper's. For `f ∅ ≠ 0` the integrand is not integrable and Lean returns the
  junk value `0`; the paper does not define `f̂` there, and the mission only uses `f` with
  `f ∅ = 0`. -/
noncomputable def lovasz {α : Type} [DecidableEq α] (E : Finset α) (f : Finset α → ℝ)
    (z : α → ℝ) : ℝ :=
  ∫ lam in Set.Ioi (0 : ℝ), f (E.filter (fun v => lam ≤ z v))

end SubmodSparsify


