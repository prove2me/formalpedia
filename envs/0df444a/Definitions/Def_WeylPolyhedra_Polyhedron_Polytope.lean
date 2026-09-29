-- Prove2me | Definitions.Def_WeylPolyhedra_Polyhedron_Polytope
-- name    : WeylPolyhedra_Polyhedron_Polytope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:02:38.333168+00:00
-- url     : https://prove2.me/theorems/31c115ae-3015-4440-9cdf-5f29b4c09ac5
-- title:
--   Convex polyhedra, affine extreme supports, and regions cut out by finitely many inequalities (§4)
-- statement:
--   Weyl's inhomogeneous space $\bar R_{n-1}$ is the hyperplane $x_n = -1$ of $\mathbb{R}^n$. Here it is $\mathbb{R}^m$ with $m = n-1$, a point $x \in \mathbb{R}^m$ standing for $(x, -1) \in \mathbb{R}^n$. A homogeneous half-space $(\alpha x) \ge 0$ with $\alpha = (a, a_0) \ne 0$ then reads $a \cdot x - a_0 \ge 0$.
--
--   1. For a finite set $S \subseteq \mathbb{R}^m$, a pair $(a, a_0) \in \mathbb{R}^m \times \mathbb{R}$, not both zero, is an **extreme support** of $S$ when $a\cdot s - a_0 \ge 0$ for every $s \in S$ and equality $a\cdot t - a_0 = 0$ holds at $m$ affinely independent points $t$ of $S$.
--   2. A set $H \subseteq \mathbb{R}^m$ is a **convex polyhedron** when it is the convex hull of a finite non-degenerate point system:
--   $$H = \operatorname{conv} S, \qquad S \text{ finite}, \quad \operatorname{aff} S = \mathbb{R}^m .$$
--   3. For a finite index set $J$, normals $A_j \in \mathbb{R}^m$ and constants $b_j \in \mathbb{R}$, the **region cut out by the inequalities** is
--   $$H(A, b) = \{x \in \mathbb{R}^m : A_j \cdot x - b_j \ge 0 \text{ for all } j \in J\}.$$
--   In Weyl's notation, row $j$ is $(\alpha x) \equiv \alpha_1 x_1 + \dots + \alpha_{n-1}x_{n-1} - \alpha_n \ge 0$ with $A_j = (\alpha_1, \dots, \alpha_{n-1})$ and $b_j = \alpha_n$.
--
--   These are the two descriptions of a convex polytope that §4 of Weyl's paper shows to coincide.
--
--   **Formalization Note** The homogeneous notions of §1 translate as follows: $n-1$ linearly independent homogenized points $(t,-1)$ are exactly $m$ affinely independent points $t$, and non-degeneracy of the homogenized system is $\operatorname{aff} S = \mathbb{R}^m$. "Convex polyhedron" thus includes full-dimensionality, as in Weyl (p. 301), where it is the hull of a non-degenerate system.
-- source:
--   Weyl, Elementare Theorie der konvexen Polyeder, Comment. Math. Helv. (1935), p. 301, §4 I (konvexes Polyeder); p. 302, §4 I (13) and §4 II (inequalities)

import Mathlib

namespace WeylPolyhedra.Polyhedron

/-- Weyl (1935), §4 I, pp. 301–302, in affine form. Weyl's inhomogeneous space `R̄_{n-1}` is the
hyperplane `x_n = -1` of `ℝⁿ`; here it is `ℝᵐ` with `m = n - 1`, a point `x` standing for
`(x, -1)`. A homogeneous half-space `(α x) ≥ 0` with `α = (a, a₀) ≠ 0` then reads
`a ⬝ᵥ x - a₀ ≥ 0`. It is an *extreme support* of the finite point system `S ⊆ ℝᵐ` when every
point of `S` satisfies it and equality holds at `n - 1 = m` points of `S` whose homogenized
points `(t, -1)` are linearly independent, i.e. at `m` affinely independent points of `S`. -/
def IsExtremeAffineSupport {m : ℕ} (S : Finset (Fin m → ℝ)) (a : Fin m → ℝ) (a₀ : ℝ) : Prop :=
  (a ≠ 0 ∨ a₀ ≠ 0) ∧ (∀ s ∈ S, 0 ≤ a ⬝ᵥ s - a₀) ∧
    ∃ T : Finset (Fin m → ℝ), T ⊆ S ∧ T.card = m ∧
      AffineIndependent ℝ (fun t : T => (t : Fin m → ℝ)) ∧ ∀ t ∈ T, a ⬝ᵥ t - a₀ = 0

/-- Weyl (1935), §4 I, p. 301: a *konvexes Polyeder* in `R̄_{n-1} = ℝᵐ` is the convex hull `H`
of a finite **non-degenerate** point system `S`. For points of the hyperplane `x_n = -1`,
non-degeneracy of the homogenized system is the statement that the affine span of `S` is the
whole space. -/
def IsConvexPolyhedron {m : ℕ} (H : Set (Fin m → ℝ)) : Prop :=
  ∃ S : Finset (Fin m → ℝ), affineSpan ℝ (S : Set (Fin m → ℝ)) = ⊤ ∧
    H = convexHull ℝ (S : Set (Fin m → ℝ))

/-- Weyl (1935), §4 II, p. 302: the region `H ⊆ R̄_{n-1} = ℝᵐ` cut out by finitely many
inequalities `(α x) ≡ α₁x₁ + ⋯ + α_{n-1}x_{n-1} - α_n ≥ 0`, one for each index `j`, with
`A j = (α₁, …, α_{n-1})` and `b j = α_n`. -/
def inequalityRegion {m : ℕ} {J : Type*} (A : J → Fin m → ℝ) (b : J → ℝ) :
    Set (Fin m → ℝ) :=
  {x | ∀ j, 0 ≤ A j ⬝ᵥ x - b j}

end WeylPolyhedra.Polyhedron


