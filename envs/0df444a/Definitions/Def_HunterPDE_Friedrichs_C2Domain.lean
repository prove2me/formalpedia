-- Prove2me | Definitions.Def_HunterPDE_Friedrichs_C2Domain
-- name    : HunterPDE_Friedrichs_C2Domain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:54:58.387072+00:00
-- url     : https://prove2.me/theorems/f1a9ef17-37a4-49e5-befd-d4664fe787c0
-- title:
--   Bounded open sets with C²-boundary (via a C² defining function) and the outward unit normal ν
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n$. A **$C^2$ defining function** for $\Omega$ is a $C^2$ function $\rho : \mathbb{R}^n \to \mathbb{R}$ with
--   $$\Omega = \{x : \rho(x) < 0\}, \qquad \nabla\rho(x) \neq 0 \text{ whenever } \rho(x) = 0 .$$
--   Then $\Omega$ is open, $\partial\Omega = \{\rho = 0\}$ is a $C^2$ hypersurface, and $\Omega$ lies on one side of it. We say $\Omega$ is a **bounded open set with $C^2$-boundary** if $\Omega$ is bounded and has a $C^2$ defining function; for bounded open sets this is equivalent to the chart definition (Definition 1.35 of the notes with $k = 2$: near each boundary point, a $C^2$-diffeomorphism flattens $\partial\Omega$ onto a hyperplane with $\Omega$ on one side). The **outward unit normal** at $x \in \partial\Omega$ is
--   $$\nu(x) = \frac{\nabla \rho(x)}{|\nabla\rho(x)|},$$
--   which does not depend on the choice of the defining function $\rho$.
--
--   **Formalization Note.** `IsC2DefiningFunction Ω ρ` and `IsBoundedC2Domain Ω` are the two predicates above (`gradient` is the Euclidean gradient). `outwardNormal Ω x` uses a classically chosen defining function; when $\Omega$ has none it returns the junk value $0$, which never matters because every theorem using it assumes a $C^2$ domain.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 13, Definition 1.35 (k = 2), and p. 223, Definition 8.1 (1) and Eq. (8.2)

import Mathlib

namespace HunterPDE.Friedrichs

/-- `ρ : ℝⁿ → ℝ` is a global `C²` defining function for the open set `Ω ⊆ ℝⁿ`: `ρ` is `C²`,
`Ω = {x : ρ(x) < 0}`, and the gradient of `ρ` does not vanish on the level set `{ρ = 0}`.
Then `∂Ω = {ρ = 0}` is a `C²` hypersurface, `Ω` lies on one side of it, and `∇ρ` points out of
`Ω`. -/
def IsC2DefiningFunction {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ContDiff ℝ 2 ρ ∧ (∀ x, x ∈ Ω ↔ ρ x < 0) ∧ ∀ x, ρ x = 0 → gradient ρ x ≠ 0

/-- `Ω ⊆ ℝⁿ` is a bounded open set with `C²`-boundary (Hunter, Definition 1.35 with `k = 2`,
Definition 8.1 (1)), in the equivalent form: `Ω` is bounded and has a global `C²` defining
function. -/
def IsBoundedC2Domain {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  Bornology.IsBounded Ω ∧ ∃ ρ, IsC2DefiningFunction Ω ρ

/-- The outward unit normal `ν(x) = ∇ρ(x)/|∇ρ(x)|` to `∂Ω` at `x ∈ ∂Ω`, computed from a
(classically chosen) `C²` defining function `ρ` of `Ω`. On `∂Ω = {ρ = 0}` it does not depend on
the choice of `ρ`. It is `0` (a junk value) when `Ω` has no `C²` defining function. -/
noncomputable def outwardNormal {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  by
    classical
    exact if h : ∃ ρ, IsC2DefiningFunction Ω ρ then
      ‖gradient h.choose x‖⁻¹ • gradient h.choose x
    else 0

end HunterPDE.Friedrichs


