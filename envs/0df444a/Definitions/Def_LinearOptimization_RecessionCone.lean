-- Prove2me | Definitions.Def_LinearOptimization_RecessionCone
-- name    : LinearOptimization_RecessionCone
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-05T20:47:38.822489+00:00
-- url     : https://prove2.me/theorems/9e1bc7d2-94e0-4a1a-bedd-5afcd8a46dde
-- title:
--   Polyhedral cone, recession cone, and extreme rays
-- statement:
--   **(Definition 4.1, p. 174; recession cone, p. 175; Definition 4.2, p. 176)**
--
--   Definition 4.1: a set $C \subset \mathbb{R}^n$ is a *cone* if $\lambda x \in C$ for all $\lambda \ge 0$ and all $x \in C$. A polyhedron of the form $P = \{x \in \mathbb{R}^n \mid Ax \ge 0\}$ is a nonempty cone, called a *polyhedral cone*; its only possible extreme point is the zero vector, and if $0$ is indeed an extreme point the cone is called *pointed*.
--
--   For a nonempty polyhedron $P = \{x \in \mathbb{R}^n \mid Ax \ge b\}$ and $y \in P$, the *recession cone* at $y$ is the set of all directions $d$ along which one can move indefinitely from $y$ without leaving $P$,
--
--   $$\{d \in \mathbb{R}^n \mid A(y + \lambda d) \ge b \text{ for all } \lambda \ge 0\};$$
--
--   it equals $\{d \in \mathbb{R}^n \mid Ad \ge 0\}$, hence is a polyhedral cone independent of $y$. Its nonzero elements are the *rays* of $P$. (For a standard form polyhedron $\{x \mid Ax = b, x \ge 0\}$ the recession cone is $\{d \mid Ad = 0, d \ge 0\}$.)
--
--   Definition 4.2:
--
--   - **(a)** a nonzero element $x$ of a polyhedral cone $C \subset \mathbb{R}^n$ is called an *extreme ray* if there are $n-1$ linearly independent constraints that are active at $x$;
--   - **(b)** an extreme ray of the recession cone associated with a nonempty polyhedron $P$ is also called an extreme ray of $P$.
--
--   Two extreme rays are *equivalent* if one is a positive multiple of the other (they then correspond to the same $n-1$ linearly independent active constraints); a *complete set of extreme rays* contains exactly one representative from each equivalence class, and is finite (p. 176).
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Definition 4.1, p. 174; recession cone (unnumbered), p. 175; Definition 4.2 and complete sets of extreme rays, p. 176

import Mathlib.Analysis.Convex.Extreme
import Definitions.Def_Polyhedron

/-!
Cones, pointedness, recession cones, rays, and extreme rays.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997, §4.8:

- **Definition 4.1 (p. 174).** "A set `C ⊆ ℝⁿ` is a *cone* if `λx ∈ C`
  for all `λ ≥ 0` and all `x ∈ C`." (A nonempty cone contains `0`.) A
  polyhedron of the form `P = {x ∈ ℝⁿ | Ax ≥ 0}` is a nonempty cone,
  called a *polyhedral cone* (here: `polyhedron A 0 = recessionCone A`).
  Its only possible extreme point is the zero vector; if `0` is indeed an
  extreme point, the cone is called *pointed* (p. 175).
- **Rays and recession cones (p. 175, unnumbered).** For a nonempty
  polyhedron `P = {x ∈ ℝⁿ | Ax ≥ b}` and `y ∈ P`, the recession cone at
  `y` is `{d | A(y + λd) ≥ b for all λ ≥ 0}`; it is easily seen to equal
  `{d ∈ ℝⁿ | Ad ≥ 0}`, a polyhedral cone independent of the starting
  point `y` — the form taken as the definition here. The nonzero elements
  of the recession cone are the *rays* of `P`. For a standard-form
  polyhedron `{x | Ax = b, x ≥ 0}` the recession cone is
  `{d | Ad = 0, d ≥ 0}`.
- **Definition 4.2 (p. 176).** "(a) A nonzero element `x` of a polyhedral
  cone `C ⊆ ℝⁿ` is called an *extreme ray* if there are `n − 1` linearly
  independent constraints that are active at `x`. (b) An extreme ray of
  the recession cone associated with a nonempty polyhedron `P` is also
  called an extreme ray of `P`." Two extreme rays are *equivalent* if one
  is a positive multiple of the other (they then correspond to the same
  `n − 1` linearly independent active constraints); the number of
  nonequivalent extreme rays is finite, and a finite collection of extreme
  rays is a *complete set of extreme rays* if it contains exactly one
  representative from each equivalence class (p. 176).

Design: extreme points are Mathlib's `Set.extremePoints` (not re-minted);
extreme rays are presentation-DEPENDENT (they count active constraints),
so — exactly like `IsBasicSolution` — the constraint matrix `A`, not the
solution set, is the argument. Since the recession cone of
`polyhedron A b` is presented by the same matrix `A` (with right-hand
side `0`), one predicate `IsExtremeRay A` covers both parts (a) and (b)
of Definition 4.2.
-/

open Matrix

namespace LinearOptimization

/-- **Bertsimas & Tsitsiklis, Definition 4.1 (p. 174).** `C` is a cone: `λ • x ∈ C` for every
`λ ≥ 0` and every `x ∈ C`. -/
def IsCone {n : ℕ} (C : Set (Fin n → ℝ)) : Prop :=
  ∀ lam : ℝ, 0 ≤ lam → ∀ x ∈ C, lam • x ∈ C

/-- **Bertsimas & Tsitsiklis, p. 175.** A cone is *pointed* if the zero vector is an extreme
point of it (the only candidate, since any nonzero `x` is the average of
`x/2` and `3x/2`). -/
def IsPointedCone {n : ℕ} (C : Set (Fin n → ℝ)) : Prop :=
  (0 : Fin n → ℝ) ∈ Set.extremePoints ℝ C

/-- **Bertsimas & Tsitsiklis, p. 175.** The recession cone of the polyhedron `{x | Ax ≥ b}`,
in the presentation-independent form `{d | Ad ≥ 0}` (equal, for every
`y ∈ P`, to the book's primary at-`y` form
`{d | A(y + λd) ≥ b for all λ ≥ 0}`; also equal to the polyhedral cone
`polyhedron A 0`). Its nonzero elements are the rays of `P`. -/
def recessionCone {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Set (Fin n → ℝ) :=
  {d | 0 ≤ A.mulVec d}

/-- The recession cone is the polyhedral cone `{x | Ax ≥ 0}`
(Bertsimas & Tsitsiklis, p. 175). -/
theorem recessionCone_eq_polyhedron {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    recessionCone A = polyhedron A 0 :=
  rfl

/-- **Bertsimas & Tsitsiklis, Definition 4.2 (p. 176).** `x` is an extreme ray of the
polyhedral cone `{d | Ad ≥ 0}` presented by `A`: `x` is a nonzero element
of the cone and `n − 1` linearly independent constraints (rows `aᵢ` of
`A`, constraints `aᵢ'x ≥ 0`) are active at `x`. Part (b): an extreme ray
of the polyhedron `{x | Ax ≥ b}` is an extreme ray of its recession cone,
which is presented by the same matrix `A` — so this predicate covers both
parts. -/
def IsExtremeRay {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) : Prop :=
  x ∈ recessionCone A ∧ x ≠ 0 ∧
  ∃ s : Finset (Fin m), s.card = n - 1 ∧ (∀ i ∈ s, A i ⬝ᵥ x = 0) ∧
    LinearIndependent ℝ (fun i : s => A i.1)

/-- **Bertsimas & Tsitsiklis, p. 176.** `w` is a complete set of extreme rays of the (recession)
cone presented by `A`: every `w j` is an extreme ray, and every extreme ray
is a positive multiple of exactly one `w j` (one representative per
equivalence class, equivalence being "positive multiple of"). -/
def IsCompleteExtremeRaySet {m n r : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (w : Fin r → (Fin n → ℝ)) : Prop :=
  (∀ j, IsExtremeRay A (w j)) ∧
  ∀ d, IsExtremeRay A d → ∃! j, ∃ t : ℝ, 0 < t ∧ d = t • w j

end LinearOptimization


