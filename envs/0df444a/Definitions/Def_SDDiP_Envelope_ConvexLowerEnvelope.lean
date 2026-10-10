-- Prove2me | Definitions.Def_SDDiP_Envelope_ConvexLowerEnvelope
-- name    : SDDiP_Envelope_ConvexLowerEnvelope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-10T03:44:16.804632+00:00
-- url     : https://prove2.me/theorems/dbab3b8c-35ba-4ef2-986c-16be50204aca
-- title:
--   Definition 3 — convex underestimators and the convex lower envelope of $f : X \to \mathbb R$; binary points, the cube $[0,1]^n$, max-of-affine functions
-- statement:
--   Let $E$ be a real vector space, $X \subseteq E$ and $f : X \to \mathbb R$.
--
--   1. A **convex underestimator** of $f$ is a function $h$ that is convex on the convex hull $\operatorname{conv}(X)$ and majorized by $f$ on $X$:
--   $$h \text{ convex on } \operatorname{conv}(X), \qquad h(x) \le f(x) \quad \text{for all } x \in X.$$
--   2. A function $e$ is **the convex lower envelope** of $f$ if it is the largest convex underestimator of $f$ on $\operatorname{conv}(X)$: $e$ is a convex underestimator of $f$, and $h(x) \le e(x)$ for every convex underestimator $h$ of $f$ and every $x \in \operatorname{conv}(X)$. Two convex lower envelopes of $f$ agree on $\operatorname{conv}(X)$.
--
--   For the setting of Theorem 1 the file also fixes three objects in $\mathbb R^n$:
--
--   - the **binary points** $\{0,1\}^n = \{x \in \mathbb R^n : x_i \in \{0,1\} \text{ for every } i\}$;
--   - the **unit cube** $C_n = [0,1]^n = \{x \in \mathbb R^n : 0 \le x_i \le 1 \text{ for every } i\}$;
--   - a function $e$ is a **convex piecewise linear function with finitely many linear pieces** on a set $S \subseteq \mathbb R^n$ if there are finitely many affine functions $x \mapsto \alpha_k^\top x + \beta_k$, $k = 1, \dots, K$, with
--   $$e(x) = \max_{k} \big(\alpha_k^\top x + \beta_k\big) \qquad \text{for all } x \in S.$$
--
--   These are the objects of Definition 3 and Theorem 1 of Zou, Ahmed and Sun: Theorem 1 says that for $X = \{0,1\}^n$ the convex lower envelope of any real function is of the last kind on $[0,1]^n$ and equals the function at every binary point.
--
--   **Formalization Note** $f$ and $h$ are total functions on $E$; only the values of $f$ on $X$ and of $h$ on $\operatorname{conv}(X)$ enter the definitions, so values elsewhere are irrelevant. The convex lower envelope is a predicate on $e$ (no supremum is taken, so no default value of a real supremum is involved); its existence is part of Theorem 1. Points of $\mathbb R^n$ are `Fin n → ℝ` with the componentwise order, and $\alpha^\top x$ is the dot product `α ⬝ᵥ x`. "Maximum of the affine functions at $x$" is written as: every one of them is $\le e(x)$ and one of them equals $e(x)$.
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), p. 496, Appendix, Definition 3; p. 467, Theorem 1; p. 496, proof of Theorem 1 (C_n := [0,1]^n, 'convex piecewise linear function with a finite number of linear pieces')

import Mathlib

namespace SDDiP.Envelope

/-- A **convex underestimator** of `f : X → ℝ` (Zou, Ahmed, Sun, *Stochastic dual dynamic integer
programming*, Math. Program. 175 (2019), Appendix, Definition 3, p. 496): a function `h` that is convex
on `conv(X)` and majorized by `f` on `X`. Only the values of `f` on `X` and of `h` on `conv(X)` matter. -/
def IsConvexUnderestimator {E : Type*} [AddCommGroup E] [Module ℝ E]
    (X : Set E) (f : E → ℝ) (h : E → ℝ) : Prop :=
  ConvexOn ℝ (convexHull ℝ X) h ∧ ∀ x ∈ X, h x ≤ f x

/-- `e` is **the convex lower envelope** of `f : X → ℝ` (Definition 3, p. 496): `e` is a convex
underestimator of `f` and it is the largest one on `conv(X)`, i.e. `h ≤ e` on `conv(X)` for every
convex underestimator `h`. Two such functions agree on `conv(X)`. -/
def IsConvexLowerEnvelope {E : Type*} [AddCommGroup E] [Module ℝ E]
    (X : Set E) (f : E → ℝ) (e : E → ℝ) : Prop :=
  IsConvexUnderestimator X f e ∧
    ∀ h : E → ℝ, IsConvexUnderestimator X f h → ∀ x ∈ convexHull ℝ X, h x ≤ e x

/-- The binary points `{0,1}ⁿ ⊆ ℝⁿ`: vectors whose every coordinate is `0` or `1`. -/
def binaryPoints (n : ℕ) : Set (Fin n → ℝ) := {x | ∀ i, x i = 0 ∨ x i = 1}

/-- The unit cube `Cₙ = [0,1]ⁿ ⊆ ℝⁿ` (componentwise order). -/
def cube (n : ℕ) : Set (Fin n → ℝ) := Set.Icc 0 1

/-- `e` is a **convex piecewise linear function with finitely many linear pieces** on `S`: there are
finitely many affine functions `x ↦ ⟪αₖ, x⟫ + βₖ`, `k < K`, such that at every `x ∈ S` the value `e x`
is the largest of them (each is `≤ e x`, and one equals `e x`), i.e. `e = maxₖ (⟪αₖ, ·⟫ + βₖ)` on `S`. -/
def IsMaxOfAffineOn {n : ℕ} (S : Set (Fin n → ℝ)) (e : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (K : ℕ) (α : Fin K → Fin n → ℝ) (β : Fin K → ℝ),
    ∀ x ∈ S, (∀ k, α k ⬝ᵥ x + β k ≤ e x) ∧ ∃ k, e x = α k ⬝ᵥ x + β k

end SDDiP.Envelope


