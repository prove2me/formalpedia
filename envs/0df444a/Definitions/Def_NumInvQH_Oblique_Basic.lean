-- Prove2me | Definitions.Def_NumInvQH_Oblique_Basic
-- name    : NumInvQH_Oblique_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:56.608988+00:00
-- url     : https://prove2.me/theorems/69cd4aaa-d996-4d97-8715-626bd5d4b333
-- title:
--   Quadratic form $x^{\mathsf T}Cx-2x^{\mathsf T}F$, argmin sets on an affine subspace and on a hyperplane, minimum-norm element, squared residual (Appendix A; (4.3), (4.7))
-- statement:
--   This module fixes the finite-dimensional objects shared by every statement of the mission. Vectors are elements of $\mathbb R^n$ and $x^{\mathsf T}y$ is the standard dot product.
--
--   1. **Quadratic form.** For $C\in\mathbb R^{n\times n}$ and $F\in\mathbb R^n$,
--
--   $$q_{C,F}(x)=x^{\mathsf T}Cx-2x^{\mathsf T}F.$$
--
--   2. **Argmin on an affine subspace.** For $A\in\mathbb R^{k\times n}$, $b\in\mathbb R^k$ and $f:\mathbb R^n\to\mathbb R$, the set of all global minimizers of $f$ on $\{x: Ax=b\}$,
--
--   $$\operatorname*{arg\,min}_{Ax=b} f=\{x: Ax=b,\ f(x)\le f(y)\text{ for every }y\text{ with }Ay=b\}.$$
--
--   3. **Argmin on a hyperplane.** For $s\in\mathbb R^n$ and $c\in\mathbb R$, the set of all global minimizers of $q_{C,F}$ over $\{x: x^{\mathsf T}s=c\}$; with $C=\tilde c^{S\star}$, $s=S_-$ this is $\Xi_a$ of (4.3) (for $F=b^{S\star}$, $c=-1$) and $\Xi_\xi$ of (4.7) (for $F=\tilde c^{SV\star}$, $c=V_-$).
--
--   4. **Minimum-norm element.** $x$ is a minimum-norm element of a set $X$ if $x\in X$ and $x^{\mathsf T}x\le y^{\mathsf T}y$ for every $y\in X$.
--
--   5. **Squared residual.** $\|Ax-b\|^2=(Ax-b)^{\mathsf T}(Ax-b)$, the objective of Proposition A.3.
--
--   An argmin set may be empty; nothing is assumed about existence of minimizers, which is what Theorem A.4 and Theorem 4.3 decide.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` and the dot product is `⬝ᵥ`. A row vector times a matrix is written `x ᵥ* M` and a matrix times a column vector `M *ᵥ x`. The minimum-norm property compares squared Euclidean norms, which is equivalent to comparing norms.
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, pp. 14–15, 24–26, (4.3), (4.7), Proposition A.3, Theorem A.4

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS

open Matrix

namespace NumInvQH.Oblique

/-- The quadratic form in Theorem A.4 and the pointwise problems (4.3), (4.7). -/
def quadraticForm {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (F x : Fin n → ℝ) : ℝ := x ⬝ᵥ (C *ᵥ x) - 2 * (x ⬝ᵥ F)

/-- All global minimizers of a function over the affine fibre `Ax=b`. -/
def affineArgmin {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (b : Fin k → ℝ) (f : (Fin n → ℝ) → ℝ) : Set (Fin n → ℝ) :=
  {x | A *ᵥ x = b ∧ ∀ y, A *ᵥ y = b → f x ≤ f y}

/-- All global minimizers of the quadratic form on `x·s=c`. -/
def hyperArgmin {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (F s : Fin n → ℝ) (c : ℝ) : Set (Fin n → ℝ) :=
  {x | x ⬝ᵥ s = c ∧ ∀ y, y ⬝ᵥ s = c → quadraticForm C F x ≤ quadraticForm C F y}

/-- The source's minimum-Euclidean-norm property over a whole solution set. -/
def IsMinNorm {n : ℕ} (X : Set (Fin n → ℝ)) (x : Fin n → ℝ) : Prop :=
  x ∈ X ∧ ∀ y ∈ X, x ⬝ᵥ x ≤ y ⬝ᵥ y

/-- Squared Euclidean residual for Proposition A.3. -/
def squaredResidual {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) : ℝ :=
  (A *ᵥ x - b) ⬝ᵥ (A *ᵥ x - b)

end NumInvQH.Oblique


