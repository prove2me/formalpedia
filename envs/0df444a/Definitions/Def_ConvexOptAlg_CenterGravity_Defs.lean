-- Prove2me | Definitions.Def_ConvexOptAlg_CenterGravity_Defs
-- name    : ConvexOptAlg_CenterGravity_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T16:02:06.873146+00:00
-- url     : https://prove2.me/theorems/d142c4ba-9e61-48f9-bc1a-61597f1e40a4
-- title:
--   Ch. 2 preamble and §2.1, pp. 244–245 — convex bodies, subgradients relative to X, the center of gravity (2.1) and runs of the center of gravity method
-- statement:
--   This file fixes the objects of Chapter 2 and §2.1 of Bubeck, *Convex Optimization: Algorithms and Complexity*. Throughout, $\mathbb R^n$ is Euclidean space with inner product $x^\top y$ and Lebesgue measure $\mathrm{vol}$.
--
--   1. **Convex body** (Ch. 2 preamble, p. 244). A set $\mathcal X\subset\mathbb R^n$ is a convex body if it is compact, convex and has non-empty interior.
--   2. **Subgradient relative to $\mathcal X$** (Definition 1.2, p. 235). For $f:\mathbb R^n\to\mathbb R$ and $x\in\mathcal X$, a vector $w$ is a subgradient of $f$ at $x$ (relative to $\mathcal X$) if
--   $$f(x)-f(y)\le w^\top(x-y)\qquad\text{for every } y\in\mathcal X .$$
--   3. **Center of gravity** (Eq. (2.1), p. 245). For a set $\mathcal S\subset\mathbb R^n$,
--   $$c(\mathcal S)=\frac{1}{\mathrm{vol}(\mathcal S)}\int_{x\in\mathcal S}x\,dx .$$
--   4. **Run of the center of gravity method** (§2.1, p. 245). Sequences $(\mathcal S_t)_{t\ge1}$, $(c_t)_{t\ge1}$, $(w_t)_{t\ge1}$ form a run on $\mathcal X$ for $f$ if $\mathcal S_1=\mathcal X$ and, for every $t\ge1$, $c_t=c(\mathcal S_t)$, $w_t$ is a subgradient of $f$ at $c_t$ (any one the first order oracle returns), and
--   $$\mathcal S_{t+1}=\mathcal S_t\cap\{x\in\mathbb R^n:(x-c_t)^\top w_t\le 0\}.$$
--
--   These are the objects every statement of the mission is about: the method cuts the current set through its center of gravity with the half-space on which $f$ cannot decrease, and Theorem 2.1 bounds the best value queried so far.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` with its Lebesgue measure `volume`. In the center of gravity the volume is converted to a real number, so the formula is the book's whenever $0<\mathrm{vol}(\mathcal S)<\infty$; in a run every $\mathcal S_t$ has finite positive volume, so the run predicate does not need a separate positivity clause. The oracle's choice of $w_t$ is left free (any subgradient). Sequences are indexed from $1$ as in the book; index $0$ is unused.
-- source:
--   Bubeck, arXiv:1405.4980v2, Ch. 2 preamble, p. 244; §2.1 and Eq. (2.1), p. 245; Definition 1.2, p. 235

import Mathlib

open MeasureTheory
open scoped InnerProductSpace

namespace ConvexOptAlg.CenterGravity

/-- Bubeck, arXiv:1405.4980v2, Ch. 2 preamble, p. 244: a **convex body** is a compact convex set with
non-empty interior. -/
def IsConvexBody {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsCompact X ∧ Convex ℝ X ∧ (interior X).Nonempty

/-- Bubeck, Definition 1.2, p. 235, relative to the constraint set `X`: `w` is a **subgradient** of `f`
at `x ∈ X` if `f x - f y ≤ wᵀ(x - y)` for every `y ∈ X`. -/
def IsSubgradientOn {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x w : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ X ∧ ∀ y ∈ X, f x - f y ≤ ⟪w, x - y⟫_ℝ

/-- Bubeck, Eq. (2.1), p. 245: the **center of gravity** `c = (1 / vol S) ∫_{x ∈ S} x dx` of a set `S`
for the Lebesgue measure `volume` of `ℝⁿ = EuclideanSpace ℝ (Fin n)`. (The volume is converted to a real
number; the expression is meaningful when `0 < vol S < ∞`, which holds for every set occurring in a run of
the center of gravity method.) -/
noncomputable def centroid {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) :=
  (volume S).toReal⁻¹ • ∫ x in S, x

/-- Bubeck, §2.1, p. 245: `(S, c, w)` is a **run of the center of gravity method** on `X` for `f`:
`S₁ = X`, and for every `t ≥ 1`, `c_t` is the center of gravity (2.1) of `S_t`, `w_t` is any subgradient
of `f` at `c_t` returned by the first order oracle, and
`S_{t+1} = S_t ∩ {x ∈ ℝⁿ : (x - c_t)ᵀ w_t ≤ 0}`. Index `0` is unused. -/
structure IsCenterOfGravityRun {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (S : ℕ → Set (EuclideanSpace ℝ (Fin n)))
    (c w : ℕ → EuclideanSpace ℝ (Fin n)) : Prop where
  init : S 1 = X
  center : ∀ t : ℕ, 1 ≤ t → c t = centroid (S t)
  oracle : ∀ t : ℕ, 1 ≤ t → IsSubgradientOn X f (c t) (w t)
  cut : ∀ t : ℕ, 1 ≤ t → S (t + 1) = S t ∩ {x | ⟪x - c t, w t⟫_ℝ ≤ 0}

end ConvexOptAlg.CenterGravity


