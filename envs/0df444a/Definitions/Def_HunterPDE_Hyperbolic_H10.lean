-- Prove2me | Definitions.Def_HunterPDE_Hyperbolic_H10
-- name    : HunterPDE_Hyperbolic_H10
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:27:50.447213+00:00
-- url     : https://prove2.me/theorems/a82e3d80-d8c5-48bc-9b20-d1d389d30781
-- title:
--   The spaces H¹₀(Ω), L²(Ω) and H⁻¹(Ω) = H¹₀(Ω)′ with their embeddings (pp. 92, 179)
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n$ be open. A **test function** $\phi \in C_c^\infty(\Omega)$ is an infinitely differentiable function with compact support contained in $\Omega$. The **$H^1$ norm** of a function $u$ with weak gradient $Du$ is
--   $$\|u\|_{H^1_0} = \Big(\int_\Omega \big(u^2 + |Du|^2\big)\,dx\Big)^{1/2},$$
--   and the Sobolev space $H^1_0(\Omega)$ is the closure of $C_c^\infty(\Omega)$ in this norm; it is a Hilbert space. $L^2(\Omega)$ is the space of square-integrable real functions on $\Omega$ with inner product $(u,v)_{L^2} = \int_\Omega uv\,dx$, and $H^{-1}(\Omega) = H^1_0(\Omega)'$ is the space of bounded linear functionals on $H^1_0(\Omega)$, with the dual norm and the pairing $\langle f, v\rangle$. The embeddings $H^1_0(\Omega) \hookrightarrow L^2(\Omega) \hookrightarrow H^{-1}(\Omega)$ send $u$ to itself and $f \in L^2(\Omega)$ to the functional $v \mapsto (f, v)_{L^2}$.
--
--   These are the function spaces in which the weak solution of the hyperbolic initial-boundary value problem, its velocity and its acceleration live.
--
--   **Formalization Note.** $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`. An element of $H^1_0(\Omega)$ is modelled by its **jet** $(u, Du)$: `H10 n Ω` is the closure, in $L^2(\Omega;\mathbb{R}\times\mathbb{R}^n)$, of the span of the jets $(\phi, \nabla\phi)$ of test functions, so its norm is exactly the $H^1$ norm above. `val u`, `grad u` are representatives of $u$ and $Du$; `pd u i` is $\partial_{i+1}u$ (0-based coordinates). `toL2` is the embedding into `L2 n Ω` (= `Lp ℝ 2 (volume.restrict Ω)`), `Hm1 n Ω` is `StrongDual ℝ (H10 n Ω)`, and `l2ToHm1 f` is $v \mapsto (f, v)_{L^2}$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 92 (H¹₀(Ω) = closure of C_c^∞(Ω)), p. 179 (H⁻¹(Ω) = H¹₀(Ω)′ and the pairing ⟨·,·⟩)

import Mathlib

namespace HunterPDE.Hyperbolic

open MeasureTheory
open scoped ContDiff

/-- The value space of a first-order jet on `ℝⁿ`: a pair `(u(x), Du(x)) ∈ ℝ × ℝⁿ` with the
Euclidean norm `|(s, ξ)|² = s² + |ξ|²`. -/
abbrev Jet (n : ℕ) : Type := WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n))

/-- The Hilbert space `L²(Ω; ℝ × ℝⁿ)` in which `H¹₀(Ω)` sits: an element is (the a.e.-class of)
a pair `(u, Du)` with `u, ∂₁u, …, ∂ₙu ∈ L²(Ω)`; its squared norm is `∫_Ω (u² + |Du|²) dx`, the
`H¹` norm. -/
abbrev JetL2 (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) : Type :=
  Lp (Jet n) 2 (volume.restrict Ω)

/-- The jets `(φ, ∇φ)` of the test functions `φ ∈ C_c^∞(Ω)` (smooth, compactly supported, support
in `Ω`), as elements of `L²(Ω; ℝ × ℝⁿ)`. -/
def testJets (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) : Set (JetL2 n Ω) :=
  {F | ∃ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
    tsupport φ ⊆ Ω ∧ (F : EuclideanSpace ℝ (Fin n) → Jet n) =ᵐ[volume.restrict Ω]
      fun x => WithLp.toLp 2 (φ x, gradient φ x)}

/-- The Sobolev space `H¹₀(Ω)`: the closure of `C_c^∞(Ω)` in the `H¹` norm, realised as the closure
of the jets `(φ, ∇φ)`, `φ ∈ C_c^∞(Ω)`, in `L²(Ω; ℝ × ℝⁿ)`. An element records the function and its
weak gradient; its norm is `‖u‖_{H¹₀} = (∫_Ω (u² + |Du|²) dx)^{1/2}` and the subspace is closed,
hence a Hilbert space. -/
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

/-- The weak partial derivative `∂ᵢu` of `u ∈ H¹₀(Ω)`, `i : Fin n` (0-based: Lean's `i` is the
book's `i + 1`). -/
noncomputable def pd {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (u : H10 n Ω) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  grad u x i

/-- `L²(Ω)`, the real Lebesgue space of square-integrable functions on `Ω`. -/
abbrev L2 (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) : Type :=
  Lp ℝ 2 (volume.restrict Ω)

/-- The continuous embedding `H¹₀(Ω) ↪ L²(Ω)`, `u ↦ u` (first component of the jet). -/
noncomputable def toL2 (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) : H10 n Ω →L[ℝ] L2 n Ω :=
  (ContinuousLinearMap.compLpL 2 (volume.restrict Ω)
    (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n)))).comp (H10 n Ω).subtypeL

/-- `H⁻¹(Ω) = H¹₀(Ω)'`, the space of bounded linear functionals on `H¹₀(Ω)` with the dual (operator)
norm `‖f‖_{H⁻¹} = sup_{v ≠ 0} |⟨f, v⟩| / ‖v‖_{H¹₀}`. The duality pairing `⟨f, v⟩` is `f v`. -/
abbrev Hm1 (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) : Type :=
  StrongDual ℝ (H10 n Ω)

/-- The embedding `L²(Ω) ↪ H⁻¹(Ω)`: `f ∈ L²(Ω)` acts on `v ∈ H¹₀(Ω)` by
`⟨f, v⟩ = (f, v)_{L²} = ∫_Ω f v dx`. -/
noncomputable def l2ToHm1 {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (f : L2 n Ω) :
    Hm1 n Ω :=
  (innerSL ℝ f).comp (toL2 n Ω)

end HunterPDE.Hyperbolic


