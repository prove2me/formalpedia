-- Prove2me | Definitions.Def_HunterPDE_Elliptic_H10
-- name    : HunterPDE_Elliptic_H10
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:37:39.86203+00:00
-- url     : https://prove2.me/theorems/e664f964-c924-441e-92bb-23273f4f2bf3
-- title:
--   The Sobolev space H¹₀(Ω) as the closure of C_c^∞(Ω) in the H¹ norm; domains bounded in some direction (p. 92, p. 98)
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n$ be open. A **test function** $\phi \in C_c^\infty(\Omega)$ is an infinitely differentiable function with compact support contained in $\Omega$. The **standard $H^1$ norm and inner product** are
--   $$\|u\|_1 = \Big(\int_\Omega \big(u^2 + |Du|^2\big)\,dx\Big)^{1/2}, \qquad (u,v)_1 = \int_\Omega (uv + Du\cdot Dv)\,dx .$$
--   The space $H^1_0(\Omega) = \overline{C_c^\infty(\Omega)}$ is the closure of the test functions in this norm; it is a Hilbert space. Each $u \in H^1_0(\Omega)$ has a function $u$ and a weak gradient $Du = (\partial_1 u, \dots, \partial_n u)$, both in $L^2(\Omega)$, and $(u, v)_{L^2} = \int_\Omega uv\,dx$ is the $L^2$ inner product.
--
--   An open set $\Omega$ is **bounded in some direction** if there are a unit vector $e \in \mathbb{R}^n$ and constants $a, b$ with $a < x \cdot e < b$ for all $x \in \Omega$.
--
--   **Formalization Note.** $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`. An element of $H^1_0(\Omega)$ is modelled by its **jet** $(u, Du)$: `H10 n Ω` is the closure, in the Hilbert space $L^2(\Omega;\mathbb{R}\times\mathbb{R}^n)$ with norm $\int_\Omega (u^2+|Du|^2)$, of the span of the jets $(\phi, \nabla\phi)$ of test functions. Its norm is therefore exactly the standard norm (4.13), and it is complete. `val u` and `grad u` are representatives of $u$ and $Du$; `pd u i` is $\partial_{i+1} u$ (coordinates are 0-based). `toL2 u` is the class of $u$ in $L^2(\Omega)$. $C^\infty$ is `ContDiff ℝ ∞` (smooth, not analytic).
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 92 (H¹₀(Ω) = closure of C_c^∞(Ω)), p. 99, Eq. (4.13), p. 98 (bounded in some direction)

import Mathlib

namespace HunterPDE.Elliptic

open MeasureTheory
open scoped ContDiff

/-- The value space of a first-order jet on `ℝⁿ`: a pair `(u(x), Du(x)) ∈ ℝ × ℝⁿ` with the
Euclidean (`L²`-product) norm `|(s, ξ)|² = s² + |ξ|²`. -/
abbrev Jet (n : ℕ) : Type := WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n))

/-- The Hilbert space `L²(Ω; ℝ × ℝⁿ)` in which `H¹₀(Ω)` sits: an element is (the a.e.-class of)
a pair `(u, Du)` with `u, ∂₁u, …, ∂ₙu ∈ L²(Ω)`, and its squared norm is
`∫_Ω (u² + |Du|²) dx`, the standard `H¹` norm (Hunter (4.13)). -/
abbrev JetL2 (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) : Type :=
  Lp (Jet n) 2 (volume.restrict Ω)

/-- The jets `(φ, ∇φ)` of the test functions `φ ∈ C_c^∞(Ω)`: smooth (`C^∞`, i.e. `ContDiff ℝ ∞`,
not the analytic `ω`), compactly supported, with support in `Ω`. An element of `JetL2 n Ω` is in
this set when it agrees a.e. on `Ω` with `x ↦ (φ x, ∇φ x)` for such a `φ`. -/
def testJets (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) : Set (JetL2 n Ω) :=
  {F | ∃ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
    tsupport φ ⊆ Ω ∧ (F : EuclideanSpace ℝ (Fin n) → Jet n) =ᵐ[volume.restrict Ω]
      fun x => WithLp.toLp 2 (φ x, gradient φ x)}

/-- The Sobolev space `H¹₀(Ω)` (Hunter, p. 92: `H¹₀(Ω) = \overline{C_c^∞(Ω)}`, the closure of
`C_c^∞(Ω)` in the `H¹` norm), realised as the closure of the jets `(φ, ∇φ)`, `φ ∈ C_c^∞(Ω)`,
in `L²(Ω; ℝ × ℝⁿ)`. An element `u` records both the function and its weak gradient; the induced
inner product is the standard one `(u, v)₁ = ∫_Ω (uv + Du · Dv) dx` of (4.13), and the subspace is
closed, hence a Hilbert space. -/
noncomputable def H10 (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    Submodule ℝ (JetL2 n Ω) :=
  (Submodule.span ℝ (testJets n Ω)).topologicalClosure

/-- The function `u : Ω → ℝ` underlying `u ∈ H¹₀(Ω)` (a representative of its a.e.-class). -/
noncomputable def val {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (u : H10 n Ω)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (WithLp.ofLp (((u : JetL2 n Ω) : EuclideanSpace ℝ (Fin n) → Jet n) x)).1

/-- The weak gradient `Du` of `u ∈ H¹₀(Ω)` (a representative of its a.e.-class). -/
noncomputable def grad {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (u : H10 n Ω)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (WithLp.ofLp (((u : JetL2 n Ω) : EuclideanSpace ℝ (Fin n) → Jet n) x)).2

/-- The weak partial derivative `∂ᵢu` of `u ∈ H¹₀(Ω)`, `i : Fin n` (0-based: Lean's `i`
is the book's `i + 1`). -/
noncomputable def pd {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (u : H10 n Ω) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  grad u x i

/-- The `L²(Ω)` inner product `(u, v)_{L²} = ∫_Ω u v dx` of `u, v ∈ H¹₀(Ω)`. -/
noncomputable def l2inner {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (u v : H10 n Ω) : ℝ :=
  ∫ x in Ω, val u x * val v x

/-- The inclusion `H¹₀(Ω) ↪ L²(Ω)`, `u ↦ u` (first component of the jet). -/
noncomputable def toL2 {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (u : H10 n Ω) :
    Lp ℝ 2 (volume.restrict Ω) :=
  (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).compLp (u : JetL2 n Ω)

/-- `Ω ⊆ ℝⁿ` is bounded in some direction (Hunter, p. 98): there are a unit vector `e ∈ ℝⁿ`
and constants `a, b` with `a < x · e < b` for all `x ∈ Ω`. -/
def BoundedInSomeDirection {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ e : EuclideanSpace ℝ (Fin n), ‖e‖ = 1 ∧ ∃ a b : ℝ, ∀ x ∈ Ω,
    a < inner ℝ x e ∧ inner ℝ x e < b

end HunterPDE.Elliptic


