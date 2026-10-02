-- Prove2me | Definitions.Def_HunterPDE_Parabolic_H10
-- name    : HunterPDE_Parabolic_H10
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:16:04.533749+00:00
-- url     : https://prove2.me/theorems/79ed6078-acbb-4df5-9b69-e853f93e161f
-- title:
--   The Sobolev space H¹₀(Ω), its dual H⁻¹(Ω), and the embedding H¹₀ ↪ L² ↪ H⁻¹ (pp. 92, 179, 207)
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n$ be open. A **test function** $\phi \in C_c^\infty(\Omega)$ is an infinitely differentiable function with compact support contained in $\Omega$. The **standard $H^1$ norm** is
--   $$\|u\|_{H^1_0} = \Big(\int_\Omega \big(u^2 + |Du|^2\big)\,dx\Big)^{1/2},$$
--   and $H^1_0(\Omega)$ is the closure of $C_c^\infty(\Omega)$ in this norm; it is a Hilbert space. Each $u \in H^1_0(\Omega)$ has a function $u \in L^2(\Omega)$ and a weak gradient $Du = (\partial_1 u, \dots, \partial_n u) \in L^2(\Omega)^n$, and $(u, v)_{L^2} = \int_\Omega uv\,dx$.
--
--   The space $H^{-1}(\Omega) = H^1_0(\Omega)'$ is the dual of $H^1_0(\Omega)$: the bounded linear functionals $f$ on $H^1_0(\Omega)$ with the dual norm, and $\langle f, v\rangle$ denotes the value of $f$ at $v$. Through $L^2(\Omega)$, every $u \in H^1_0(\Omega)$ defines the element $v \mapsto (u, v)_{L^2}$ of $H^{-1}(\Omega)$; this is the embedding $H^1_0(\Omega) \hookrightarrow L^2(\Omega) \hookrightarrow H^{-1}(\Omega)$ of the Hilbert triple on p. 207.
--
--   **Formalization Note.** $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`. An element of $H^1_0(\Omega)$ is modelled by its **jet** $(u, Du)$: `H10 n Ω` is the closure, in $L^2(\Omega;\mathbb{R}\times\mathbb{R}^n)$, of the span of the jets $(\phi, \nabla\phi)$ of test functions, so its norm is exactly the $H^1$ norm above. `val u`, `grad u` are representatives of $u$, $Du$; `pd u i` is $\partial_{i+1}u$ (0-based coordinates); `toL2 u` (and the continuous linear `toL2L`) is the class of $u$ in $L^2(\Omega)$. `Hm1 n Ω` is `StrongDual ℝ (H10 n Ω)` and `l2Embed n Ω u` is the functional $v \mapsto (u, v)_{L^2}$. This file repeats, under `HunterPDE.Parabolic`, the $H^1_0$ model of the elliptic mission of this series.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 92 (H¹₀(Ω) = closure of C_c^∞(Ω)), p. 179 (H⁻¹(Ω) = H¹₀(Ω)′), p. 207 (the triple H¹₀ ↪ L² ↪ H⁻¹)

import Mathlib

namespace HunterPDE.Parabolic

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

/-- `H¹₀(Ω)` is complete (a closed subspace of the Hilbert space `L²(Ω; ℝ × ℝⁿ)`), hence a
Hilbert space. -/
instance instCompleteSpaceH10 (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    CompleteSpace (H10 n Ω) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- The inclusion `H¹₀(Ω) ↪ L²(Ω)` as a continuous linear map (the same map as `toL2`). -/
noncomputable def toL2L (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    H10 n Ω →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  ((WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).compLpL 2 (volume.restrict Ω)).comp
    (H10 n Ω).subtypeL

/-- The space `H⁻¹(Ω) = H¹₀(Ω)'` (Hunter, p. 179): the (strong, i.e. norm-topology) dual of the
Hilbert space `H¹₀(Ω)`, with the dual norm `‖f‖_{H⁻¹} = sup_{‖v‖_{H¹₀} ≤ 1} |⟨f, v⟩|`. The duality
pairing `⟨f, v⟩` of `f ∈ H⁻¹(Ω)` and `v ∈ H¹₀(Ω)` is the application `f v`. -/
abbrev Hm1 (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) : Type :=
  StrongDual ℝ (H10 n Ω)

/-- The embedding `H¹₀(Ω) ↪ L²(Ω) ↪ H⁻¹(Ω)` of the Hilbert triple `H¹₀ ⊂ L² ⊂ H⁻¹` (Hunter,
p. 207): `u ∈ H¹₀(Ω)` acts on `v ∈ H¹₀(Ω)` by the `L²` inner product,
`⟨u, v⟩ = (u, v)_{L²} = ∫_Ω u v dx`. -/
noncomputable def l2Embed (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    H10 n Ω →L[ℝ] Hm1 n Ω :=
  (ContinuousLinearMap.precomp ℝ (toL2L n Ω) : _).comp
    ((innerSL ℝ (E := Lp ℝ 2 (volume.restrict Ω))).comp (toL2L n Ω))

end HunterPDE.Parabolic


