-- Prove2me | Definitions.Def_BCWCentralizer_Dynamics
-- name    : BCWCentralizer_Dynamics
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-30T20:54:01.539158+00:00
-- url     : https://prove2.me/theorems/9fc58400-3bd4-4dd5-a291-da5ef1b3c6dd
-- title:
--   Nonwandering set, Jacobians and the unbounded distortion property $(UD_{M\setminus\Omega})$
-- statement:
--   Dynamical notions used in Theorem A (Section 2.1–2.2 of the paper), for a smooth manifold $M$ modelled on $\mathbb R^d$ equipped with a Riemannian metric.
--
--   1. The *nonwandering set* $\Omega(f)$ of $f:M\to M$: the points $x$ such that every neighbourhood $U$ of $x$ satisfies $U\cap f^k(U)\neq\emptyset$ for some $k>0$. Its complement $M\setminus\Omega(f)$ is the wandering set.
--   2. The orbit of $x$ under $f\in\mathrm{Diff}^1(M)$: $\{f^n(x):n\in\mathbb Z\}$.
--   3. The Jacobian $|\det Dh(x)|$ of $h:M\to M$ at $x$, computed with orthonormal bases of $T_xM$ and $T_{h(x)}M$ for the Riemannian metric: $|\det Dh(x)|=\sqrt{\det\big(\langle Dh(x)e_i,Dh(x)e_j\rangle\big)_{i,j}}$ for an orthonormal basis $(e_i)$ of $T_xM$.
--   4. The *unbounded distortion property on the wandering set* $(UD_{M\setminus\Omega})$: there is a subset $\mathcal X\subset M\setminus\Omega(f)$, dense in $M\setminus\Omega(f)$, such that for any $K>0$, any $x\in\mathcal X$ and any $y\in M\setminus\Omega(f)$ not in the orbit of $x$, there exists $n\ge1$ with
--   $$\big|\log|\det Df^n(x)|-\log|\det Df^n(y)|\big|>K.$$
--
--   **Formalization Note** The Riemannian metric is a typeclass parameter; for a continuous metric on a compact manifold, property 4 does not depend on the metric, because changing the metric changes $\log|\det Df^n|$ by a bounded amount.
-- source:
--   Bonatti, Crovisier, Wilkinson, *The C^1 generic diffeomorphism has trivial centralizer*, arXiv:0804.1416v1 (2008), https://arxiv.org/abs/0804.1416, Sections 1.1, 2.1, 2.2, 2.5

import Mathlib
import Definitions.Def_BCWCentralizer_Basic

open scoped Manifold ContDiff Topology InnerProductSpace
open Bundle

namespace BCWCentralizer

noncomputable section

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin d)) M]
  [IsManifold (𝓡 d) ∞ M]

/-- The nonwandering set `Ω(f)`: the points `x` such that every neighbourhood `U` of `x` meets
some forward iterate `f^k(U)`, `k > 0`. -/
def nonwanderingSet (f : M → M) : Set M :=
  {x | ∀ U ∈ 𝓝 x, ∃ k : ℕ, 0 < k ∧ (U ∩ f^[k] '' U).Nonempty}

/-- The (full, two-sided) orbit `{f^n(x) : n ∈ ℤ}` of `x` under a diffeomorphism `f`. -/
def orbit (f : Diff1 d M) (x : M) : Set M :=
  Set.range fun n : ℤ => zpowPerm f n x

/-- Tangent spaces of `M` are finite dimensional (they are copies of `ℝ^d`). -/
scoped instance (x : M) : FiniteDimensional ℝ (TangentSpace (𝓡 d) x) :=
  inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin d)))

variable [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 d) x)]

/-- The Jacobian `|det Dh(x)|` of a map `h : M → M` at `x`, computed with respect to the
Riemannian inner products on `T_xM` and `T_{h x}M`: if `(e_i)` is an orthonormal basis of `T_xM`,
it is the square root of the Gram determinant `det (⟪Dh(x) e_i, Dh(x) e_j⟫)`. -/
def jacobianAbs (h : M → M) (x : M) : ℝ :=
  Real.sqrt (Matrix.det (Matrix.of fun i j =>
    ⟪mfderiv (𝓡 d) (𝓡 d) h x (stdOrthonormalBasis ℝ (TangentSpace (𝓡 d) x) i),
     mfderiv (𝓡 d) (𝓡 d) h x (stdOrthonormalBasis ℝ (TangentSpace (𝓡 d) x) j)⟫_ℝ))

/-- The unbounded distortion property on the wandering set, `(UD_{M∖Ω})`: there is a subset
`X` of the wandering set `M ∖ Ω(f)`, dense in `M ∖ Ω(f)`, such that for every `K`, every `x ∈ X`
and every `y ∈ M ∖ Ω(f)` not in the orbit of `x`, there is `n ≥ 1` with
`|log |det Df^n(x)| - log |det Df^n(y)|| > K`. -/
def HasUDWandering (f : Diff1 d M) : Prop :=
  ∃ X : Set M, X ⊆ (nonwanderingSet f)ᶜ ∧ (nonwanderingSet f)ᶜ ⊆ closure X ∧
    ∀ K : ℝ, ∀ x ∈ X, ∀ y ∈ (nonwanderingSet f)ᶜ, y ∉ orbit f x →
      ∃ n : ℕ, 1 ≤ n ∧
        K < |Real.log (jacobianAbs (d := d) (⇑f)^[n] x) -
          Real.log (jacobianAbs (d := d) (⇑f)^[n] y)|

end

end BCWCentralizer


