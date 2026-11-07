-- Prove2me | Definitions.Def_ApproxDegComp_rho
-- name    : ApproxDegComp_rho
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:00.548209+00:00
-- url     : https://prove2.me/theorems/5d17c37e-cd59-45df-8932-a3f62bc191aa
-- title:
--   The family $\rho_\theta(x)=|(e^{i\theta A}v)_x|^2$
-- statement:
--   Let $\mathcal X\subseteq\{0,1\}^m$ be finite, $A$ a real matrix on $\mathbb R^{\mathcal X}$ and $v\in\mathbb C^{\mathcal X}$. For $\theta\in\mathbb R$ define
--
--   $$\rho_\theta(x)=\bigl|(e^{i\theta A}v)_x\bigr|^2\qquad(x\in\mathcal X).$$
--
--   For real symmetric $A$ the matrix $e^{i\theta A}$ is unitary, so for a unit vector $v$ every $\rho_\theta$ is a probability measure on $\mathcal X$ (Lemma 21).
--
--   **Formalization Note** $e^{i\theta A}$ is the matrix exponential of the complex matrix $i\theta A$. The paper defines $\rho_\theta$ on $\mathcal X$; here it is extended by $0$ to all of $\{0,1\}^m$, so that it is a weight vector on $\{0,1\}^m$ as Lemmas 9 and 22 use it.
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Lemma 21, p.22

import Mathlib

namespace ApproxDegComp

/-- **The family** `ρ_θ(x) = |(e^{iθA} v)_x|²` (Lemma 21, p.22).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Lemma 21, p.22: "Define v = (u₀ + iu₁)/√2 and for real θ, define ρ_θ : X → [0, 1] by
ρ_θ(x) = |(e^{iθA} v)_x|²."

For a real matrix `A` on `ℝ^X` and a complex vector `v`, `rho X A v θ x` is the squared
modulus of coordinate `x` of `e^{iθA} v` for `x ∈ X`, and `0` for `x ∉ X`.

**Formalization Note** `e^{iθA}` is `NormedSpace.exp` of the complex matrix `(iθ) · A`. The
paper defines `ρ_θ` on `X`; it is extended by `0` to `{0,1}^m` so that it is a weight vector
on `{0,1}^m`, as Lemma 9 and Lemma 22 use it. -/
noncomputable def rho {m : ℕ} (X : Finset (Fin m → Bool)) (A : Matrix X X ℝ) (v : X → ℂ)
    (θ : ℝ) : (Fin m → Bool) → ℝ :=
  fun x => if hx : x ∈ X then
    ‖Matrix.mulVec (NormedSpace.exp (((θ : ℂ) * Complex.I) • A.map (fun a : ℝ => (a : ℂ)))) v
      ⟨x, hx⟩‖ ^ 2
  else 0

end ApproxDegComp


