-- Prove2me | Definitions.Def_KallMayerSLP_NormalCC_IsPseudoConcaveOn
-- name    : KallMayerSLP_NormalCC_IsPseudoConcaveOn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:09:56.16799+00:00
-- url     : https://prove2.me/theorems/184cecf9-a8a9-4146-8342-0645518dceb9
-- title:
--   Pseudo-concave function on an open convex set (Definition 1.2)
-- statement:
--   Let $C\subseteq\mathbb R^n$ be an open convex set and $f$ a continuously differentiable function on $C$. Then $f$ is **pseudo-concave** on $C$ if
--   $$\nabla^{\mathsf T}f(x)(y-x)\le0\ \Longrightarrow\ f(y)\le f(x)\qquad\text{for all }x,y\in C .$$
--   $f$ is **pseudo-convex** on $C$ if $-f$ is pseudo-concave on $C$.
--
--   The predicate here bundles the standing requirements of the definition: $C$ open and convex, $f$ continuously differentiable on $C$, and the implication. Pseudo-concave objectives have only global local maxima and make the Kuhn–Tucker conditions sufficient; Proposition 2.1 establishes this property for the normal probability function on half-spaces.
--
--   **Formalization Note** $f$ is given on all of $\mathbb R^n$; only its values on $C$ matter. $\nabla^{\mathsf T}f(x)(y-x)$ is the Fréchet derivative of $f$ at $x$ applied to $y-x$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Definition 1.2, p.88 (PDF p.98)

import Mathlib

namespace KallMayerSLP.NormalCC

/-- **Pseudo-concave function** (Kall & Mayer 2005, Chapter 2, Definition 1.2, p.88, PDF p.98):
"Let `f : C → ℝ` be a continuously differentiable function defined over an open convex set `C`.
`f` is called pseudo-concave, if the following implication `∇ᵀf(x)(y − x) ≤ 0 ⟹ f(y) ≤ f(x)`
holds for all `x ∈ C` and `y ∈ C`. `f` is called pseudo-convex, if `−f` pseudo-concave."

`IsPseudoConcaveOn C f` asserts that `C ⊆ ℝⁿ` is open and convex, `f` is continuously
differentiable on `C`, and the implication holds on `C`. Pseudo-convexity of `f` on `C` is
`IsPseudoConcaveOn C (fun x => - f x)`, exactly as in the book.

**Formalization Note.** `f` is a function on all of `ℝⁿ = Fin n → ℝ`; only its values on `C`
matter. `∇ᵀf(x)(y − x)` is the Fréchet derivative `fderiv ℝ f x` applied to `y − x`; on the open
set `C` this is the directional derivative of the book. Continuous differentiability is
`ContDiffOn ℝ 1 f C` (independent of the norm chosen on `ℝⁿ`). -/
def IsPseudoConcaveOn {n : ℕ} (C : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  IsOpen C ∧ Convex ℝ C ∧ ContDiffOn ℝ 1 f C ∧
    ∀ x ∈ C, ∀ y ∈ C, fderiv ℝ f x (y - x) ≤ 0 → f y ≤ f x

end KallMayerSLP.NormalCC


