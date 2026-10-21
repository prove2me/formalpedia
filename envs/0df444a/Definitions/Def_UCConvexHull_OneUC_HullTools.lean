-- Prove2me | Definitions.Def_UCConvexHull_OneUC_HullTools
-- name    : UCConvexHull_OneUC_HullTools
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:14:14.351243+00:00
-- url     : https://prove2.me/theorems/862641b3-6252-4320-b406-4af7a08c9f2e
-- title:
--   §5, pp. 16–17 — NLP set C = {f ≤ 0}, its mixed-integer restriction S, σ_S(c), the Lagrangian dual D(c) of (22)–(23), and the 1-sum S¹ ⊕ S² (Definition 1)
-- statement:
--   This file fixes the general convex-analysis objects of §5 that are not specific to unit commitment.
--
--   **The NLP set and its mixed-integer restriction (Proposition 1, p. 16).** For a constraint map $f:\mathbb R^n\to\mathbb R^m$, the NLP set is
--
--   $$C=\{\,z\in\mathbb R^n : f(z)\le 0\,\},$$
--
--   with $f(z)\le 0$ read componentwise. For an index set $K\subseteq\{1,\dots,n\}$, its mixed-integer restriction is $S=\{\,z\in C : z_k\in\mathbb Z,\ k\in K\,\}$.
--
--   **Support function and Lagrangian dual ((22)–(23), pp. 16–17).** For $c\in\mathbb R^n$ and a set $S\subseteq\mathbb R^n$, the minimization of $cz$ over $S$ is $\sigma_S(c)=\inf\{\,cz : z\in S\,\}$, an extended real number ($+\infty$ when $S=\emptyset$, possibly $-\infty$). The Lagrangian function is $L(\lambda;c)=\inf_{z\in\mathbb R^n}\{\,cz+\lambda f(z)\,\}$, the infimum over all of $\mathbb R^n$, and the Lagrangian dual is
--
--   $$D(c)=\sup_{\lambda\ge 0} L(\lambda;c).$$
--
--   **1-sum composition (Definition 1, p. 17).** For $S^1\subseteq\mathbb R^{n_1}\times\mathbb R$ and $S^2\subseteq\mathbb R^{n_2}\times\mathbb R$,
--
--   $$S^1\oplus S^2=\{\,(x^1,x^2,y) : (x^h,y)\in S^h,\ h=1,2\,\}:$$
--
--   the two sets are glued along their shared last coordinate $y$.
--
--   These objects state Proposition 1, Lemma 1 and the remark that 1-sums preserve convexity and closedness.
--
--   **Formalization Note.** Points of $\mathbb R^n$ are functions `Fin n → ℝ`, and $cz$ is the dot product. $\sigma_S$ and $D$ take values in `EReal`; only infima and suprema act on `EReal`, and no `EReal` addition occurs. The multiplier $\lambda$ ranges over the nonnegative orthant. The 1-sum lives in $\mathbb R^{n_1}\times\mathbb R^{n_2}\times\mathbb R$, written as a product of types rather than $\mathbb R^{n_1+n_2+1}$.
-- source:
--   Bacci, Frangioni, Gentile, Tavlaridis-Gyparakis, New MINLP Formulations for the Unit Commitment Problems with Ramping Constraints, manuscript submitted to Operations Research (PDF sha256 eee1c5a4…e224), pp. 16–17, Proposition 1, (22), (23), Definition 1

import Mathlib

namespace UCConvexHull.OneUC

/-! # Closed convex hulls of mixed-integer convex sets: the objects of Proposition 1 and Definition 1

Bacci, Frangioni, Gentile, Tavlaridis-Gyparakis, *New MINLP Formulations for the Unit Commitment
Problems with Ramping Constraints* (manuscript submitted to Operations Research), §5, pp. 16–17.
Everything is real and finite-dimensional. -/

/-- The NLP set `C = { z ∈ ℝⁿ : f(z) ≤ 0 }` of a constraint map `f : ℝⁿ → ℝᵐ` (Proposition 1,
p. 16); `f(z) ≤ 0` is componentwise. -/
def conSet {n m : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ)) : Set (Fin n → ℝ) :=
  {z | ∀ i, f z i ≤ 0}

/-- The mixed-integer restriction `S = { z ∈ C : z_k ∈ ℤ, k ∈ K }` of `C` (Proposition 1, p. 16). -/
def miRestriction {n m : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ)) (K : Finset (Fin n)) :
    Set (Fin n → ℝ) :=
  {z | z ∈ conSet f ∧ ∀ k ∈ K, ∃ j : ℤ, z k = j}

/-- The minimization of `cz` over a set, `σ_S(c) = inf { cz : z ∈ S }` ((22)–(23), pp. 16–17), in
the extended reals: `+∞` on the empty set, and possibly `−∞`. -/
noncomputable def supportInf {n : ℕ} (S : Set (Fin n → ℝ)) (c : Fin n → ℝ) : EReal :=
  ⨅ z ∈ S, ((c ⬝ᵥ z : ℝ) : EReal)

/-- The Lagrangian dual `D(c) = sup_{λ ≥ 0} L(λ; c)`, where `L(λ; c) = inf { cz + λ f(z) }` with the
infimum over all `z ∈ ℝⁿ` ((22), p. 16), in the extended reals. -/
noncomputable def lagDual {n m : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ)) (c : Fin n → ℝ) : EReal :=
  ⨆ (μ : Fin m → ℝ) (_ : 0 ≤ μ), ⨅ z : Fin n → ℝ, ((c ⬝ᵥ z + μ ⬝ᵥ f z : ℝ) : EReal)

/-- Definition 1 (p. 17): the 1-sum composition of `S¹ ⊆ ℝ^{n₁} × ℝ` and `S² ⊆ ℝ^{n₂} × ℝ`,
`S¹ ⊕ S² = { (x¹, x², y) : (xʰ, y) ∈ Sʰ, h = 1, 2 }`. -/
def oneSum {n₁ n₂ : ℕ} (S₁ : Set ((Fin n₁ → ℝ) × ℝ)) (S₂ : Set ((Fin n₂ → ℝ) × ℝ)) :
    Set ((Fin n₁ → ℝ) × (Fin n₂ → ℝ) × ℝ) :=
  {q | (q.1, q.2.2) ∈ S₁ ∧ (q.2.1, q.2.2) ∈ S₂}

end UCConvexHull.OneUC


