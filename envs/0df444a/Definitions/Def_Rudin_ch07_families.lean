-- Prove2me | Definitions.Def_Rudin_ch07_families
-- name    : Rudin_ch07_families
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-12T20:04:29.046657+00:00
-- url     : https://prove2.me/theorems/4313aa95-fd3f-486b-8fbd-9f5d307d6fe1
-- title:
--   Algebras of functions, equicontinuity, uniform closure
-- statement:
--   The vocabulary of Rudin's Chapter 7 that is not already in Mathlib in his form. A set $\mathcal{A}$ of real functions is an **algebra** if it is closed under sums, products and real scalar multiples (Definition 7.28); it **separates points** on $K$ and **vanishes at no point** of $K$ in the sense of Definition 7.30; its **uniform closure** on $K$ is the set of uniform limits on $K$ of sequences drawn from it (Section 7.13, Definition 7.29). A sequence of functions is **pointwise bounded** or **uniformly bounded** on $E$ as in Definition 7.19, and **equicontinuous** on $E$ when a single $\delta$ serves every member of the family (Definition 7.22). Uniform convergence itself is Mathlib's `TendstoUniformlyOn`.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 7, pp. 150-162, Definitions 7.19, 7.22, 7.28, 7.30 and Section 7.13

import Mathlib

/-!
# Rudin, Chapter 7 — families of functions

Definitions transcribed from Walter Rudin, *Principles of Mathematical Analysis*, 3rd edition,
Chapter 7 (Definitions 7.7, 7.19, 7.22, 7.28, 7.30 and Section 7.13).

Uniform convergence itself is Mathlib's `TendstoUniformlyOn` and is reused.  What is added here
is the vocabulary of the Stone–Weierstrass section — algebras of functions, separation of
points, vanishing at no point, uniform closure — together with Rudin's boundedness and
equicontinuity conditions for families of functions, all stated for plain function sets rather
than for bundled subalgebras, so that they match the book.
-/

namespace Rudin

variable {X : Type*}

/-- Rudin, Definition 7.28: a set `A` of real functions is an **algebra** if it is closed under
addition, multiplication and scalar multiplication. -/
def IsFunctionAlgebra (A : Set (X → ℝ)) : Prop :=
  (∀ f ∈ A, ∀ g ∈ A, f + g ∈ A) ∧ (∀ f ∈ A, ∀ g ∈ A, f * g ∈ A) ∧
    (∀ c : ℝ, ∀ f ∈ A, (fun x => c * f x) ∈ A)

/-- Rudin, Definition 7.30: `A` **separates points** on `K` if for any two distinct points of
`K` some member of `A` takes different values at them. -/
def SeparatesPointsOn (A : Set (X → ℝ)) (K : Set X) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, x ≠ y → ∃ f ∈ A, f x ≠ f y

/-- Rudin, Definition 7.30: `A` **vanishes at no point** of `K` if for each `x ∈ K` some member
of `A` is nonzero at `x`. -/
def VanishesAtNoPointOn (A : Set (X → ℝ)) (K : Set X) : Prop :=
  ∀ x ∈ K, ∃ f ∈ A, f x ≠ 0

/-- Rudin, Section 7.13 and Definition 7.29: the **uniform closure** of `A` on `K` is the set of
functions that are uniform limits on `K` of sequences from `A`. -/
def UniformClosureOn [PseudoMetricSpace X] (A : Set (X → ℝ)) (K : Set X) : Set (X → ℝ) :=
  {g | ∃ f : ℕ → X → ℝ, (∀ n, f n ∈ A) ∧ TendstoUniformlyOn f g Filter.atTop K}

/-- Rudin, Definition 7.19: the sequence `F` is **pointwise bounded** on `E`. -/
def PointwiseBoundedOn (F : ℕ → X → ℂ) (E : Set X) : Prop :=
  ∀ x ∈ E, ∃ M : ℝ, ∀ n, ‖F n x‖ ≤ M

/-- Rudin, Definition 7.19: the sequence `F` is **uniformly bounded** on `E`. -/
def UniformlyBoundedOn (F : ℕ → X → ℂ) (E : Set X) : Prop :=
  ∃ M : ℝ, ∀ n, ∀ x ∈ E, ‖F n x‖ ≤ M

/-- Rudin, Definition 7.22: the family `F` is **equicontinuous** on `E`: one `δ` works for every
member of the family and every pair of points of `E`. -/
def EquicontinuousOn [PseudoMetricSpace X] (F : ℕ → X → ℂ) (E : Set X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ n, ∀ x ∈ E, ∀ y ∈ E, dist x y < δ → ‖F n x - F n y‖ < ε

end Rudin


