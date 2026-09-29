-- Prove2me | Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems
-- name    : MurtyKabadi_Reduction_QuadraticProblems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:12:21.275382+00:00
-- url     : https://prove2.me/theorems/7d76ec93-6219-41bd-ac7a-641021f30663
-- title:
--   The quadratic form $x^{\mathsf T}Dx$, copositivity, and Problems 1–4, 11, 12 (pp. 121–126)
-- statement:
--   Let $\iota$ be a finite index set and $D$ a real square matrix indexed by $\iota$. Write
--   $$Q(x) = x^{\mathsf T} D x, \qquad x \in \mathbb R^{\iota},$$
--   for its quadratic form, and $x \ge 0$ for coordinatewise nonnegativity. The matrix $D$ is **copositive** if $Q(x) \ge 0$ for every $x \ge 0$.
--
--   The decision problems of Murty and Kabadi about $D$ are recorded as propositions, each being the "yes" answer:
--
--   1. **Problem 1**: $x = 0$ is *not* a local minimum of $Q$ on the orthant $\{x \ge 0\}$ (the QP (7): minimize $Q(x)$ subject to $x \ge 0$).
--   2. **Problem 2**: $Q$ is *not* bounded below on $\{x \ge 0\}$.
--   3. **Problem 3**: there is an $x \ge 0$ with $Q(x) < 0$.
--   4. **Problem 4** (with a parameter $a_0$): there is an $x \ge 0$ with $e^{\mathsf T}x = \sum_i x_i = a_0$ and $Q(x) < 0$.
--   5. With $h(u) = (u_1^2, \dots, u_n^2)\, D\, (u_1^2, \dots, u_n^2)^{\mathsf T}$, the objective of the unconstrained QP (15): **Problem 11**: $u = 0$ is *not* a local minimum of $h$ on $\mathbb R^{\iota}$; **Problem 12**: $h$ is *not* bounded below on $\mathbb R^{\iota}$.
--
--   These are the questions whose hardness the paper establishes; the mission states the equivalences between them.
--
--   **Formalization Note** The topology on $\mathbb R^{\iota}$ is the product topology, which is the Euclidean one. Problem 1 is local minimality *relative to the orthant* (`IsLocalMinOn`), Problem 11 is unconstrained local minimality (`IsLocalMin`). $D$ is an arbitrary real matrix here; the paper's integrality and symmetry of $D$ are imposed where they are used.
-- source:
--   Murty and Kabadi, Some NP-complete problems in quadratic and nonlinear programming, Math. Programming 39 (1987), p. 121 (copositivity, QP (7)), p. 122 (Problems 1, 2), p. 123 (Problems 3, 4), p. 126 (QP (15), Problems 11, 12)

import Mathlib

namespace MurtyKabadi.Reduction

open Matrix

/-- The quadratic form `Q(x) = xᵀDx` of a square real matrix `D`
(Murty–Kabadi 1987, p. 121, QP (7)). -/
def Q {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  x ⬝ᵥ (D *ᵥ x)

/-- `D` is copositive: `xᵀDx ≥ 0` for all `x ≥ 0` (p. 121). -/
def Copositive {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) : Prop :=
  ∀ x : ι → ℝ, 0 ≤ x → 0 ≤ Q D x

/-- Problem 1 (p. 122): is `x = 0` not a local minimum of `Q` on `{x ≥ 0}` (QP (7))? -/
def Problem1 {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) : Prop :=
  ¬ IsLocalMinOn (Q D) {x : ι → ℝ | 0 ≤ x} 0

/-- Problem 2 (p. 122): is `Q` not bounded below on the feasible set `{x ≥ 0}` of (7)? -/
def Problem2 {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) : Prop :=
  ¬ BddBelow (Q D '' {x : ι → ℝ | 0 ≤ x})

/-- Problem 3 (p. 123): is there an `x ≥ 0` with `Q(x) < 0`? -/
def Problem3 {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) : Prop :=
  ∃ x : ι → ℝ, 0 ≤ x ∧ Q D x < 0

/-- Problem 4 (p. 123): given `a₀`, is there an `x` with `eᵀx = a₀`, `x ≥ 0` and `Q(x) < 0`? -/
def Problem4 {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) (a0 : ℝ) : Prop :=
  ∃ x : ι → ℝ, ∑ i, x i = a0 ∧ 0 ≤ x ∧ Q D x < 0

/-- The objective of the unconstrained QP (15) (p. 126):
`h(u) = (u₁², …, u_n²) D (u₁², …, u_n²)ᵀ`. -/
def h {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) (u : ι → ℝ) : ℝ :=
  Q D (fun i => u i ^ 2)

/-- Problem 11 (p. 126): is `u = 0` not a local minimum of (15)? -/
def Problem11 {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) : Prop :=
  ¬ IsLocalMin (h D) 0

/-- Problem 12 (p. 126): is `h` not bounded below? -/
def Problem12 {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) : Prop :=
  ¬ BddBelow (Set.range (h D))

end MurtyKabadi.Reduction


