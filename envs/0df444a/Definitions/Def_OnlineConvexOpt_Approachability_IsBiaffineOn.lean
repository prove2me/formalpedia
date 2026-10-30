-- Prove2me | Definitions.Def_OnlineConvexOpt_Approachability_IsBiaffineOn
-- name    : OnlineConvexOpt_Approachability_IsBiaffineOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:39:58.974847+00:00
-- url     : https://prove2.me/theorems/ca7de0d1-c56c-4d36-9ea5-7a79ef5f8fb6
-- title:
--   Bi-affine payoff $u$ on $\mathcal K_1\times\mathcal K_2$
-- statement:
--   Let $\mathcal K_1\subseteq\mathbb R^n$, $\mathcal K_2\subseteq\mathbb R^m$ and $u:\mathbb R^n\times\mathbb R^m\to\mathbb R^d$. The payoff $u$ is **bi-affine on $\mathcal K_1\times\mathcal K_2$** if
--
--   1. for every $y\in\mathcal K_2$, all $x_1,x_2\in\mathcal K_1$ and all $a,b\ge 0$ with $a+b=1$: $\;u(ax_1+bx_2,y)=a\,u(x_1,y)+b\,u(x_2,y)$;
--   2. for every $x\in\mathcal K_1$, all $y_1,y_2\in\mathcal K_2$ and all $a,b\ge 0$ with $a+b=1$: $\;u(x,ay_1+by_2)=a\,u(x,y_1)+b\,u(x,y_2)$.
--
--   This is the condition on the reward vector of a generalized vector game under which Blackwell's approachability theorem holds. Definition 13.2 of the book states no condition on $u$, and without one Theorem 13.4 and Lemma 13.6 are false; the chapter's source (Abernethy, Bartlett and Hazan, 2011) assumes a bi-affine utility, and the mixed extension $u(x,y)=\mathbb E_{i\sim x,\,j\sim y}[u(i,j)]$ of Definition 13.1 is bilinear on $\Delta_n\times\Delta_m$.
--
--   **Formalization Note** The condition constrains $u$ only on $\mathcal K_1\times\mathcal K_2$; $u$ is a total function and its other values are irrelevant. Neither global bilinearity nor continuity is required.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, Definition 13.2, p. 208 (PDF p. 230), corrected; Abernethy, Bartlett and Hazan, Blackwell Approachability and No-Regret Learning are Equivalent, COLT 2011, §2.2

import Mathlib

namespace OnlineConvexOpt.Approachability

/-- **Bi-affinity of the payoff on `K₁ × K₂`** (the correction to Definition 13.2).
Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3,
Definition 13.2, p. 208: "A generalized two-player vector game is given by a set of vectors
{u ∈ ℝ^d}, and two bounded convex and closed decision sets K1, K2. The reward vector for the row
player playing strategy x ∈ K1, and column player playing strategy y ∈ K2, is given by the vector
u(x, y) ∈ ℝ^d."

`IsBiaffineOn K₁ K₂ u` says: for every `y ∈ K₂`, the map `x ↦ u x y` preserves convex
combinations of two points of `K₁`; and for every `x ∈ K₁`, the map `y ↦ u x y` preserves
convex combinations of two points of `K₂`.

**Formalization Note.** Definition 13.2 imposes no condition on `u`, and with an arbitrary
(even continuous) `u` Theorem 13.4 and Lemma 13.6 are false (see their docstrings). This is the
hypothesis of the source the chapter follows (Abernethy, Bartlett and Hazan 2011, §2.2: "a
biaffine utility function"), it holds for the mixed extension
`u(x, y) = E_{i∼x, j∼y}[u(i, j)]` of Definition 13.1, and it is what the chapter's appeal to
Sion's minimax theorem needs. The condition is imposed on `K₁ × K₂` only: `u` is a total
function and its values outside `K₁ × K₂` are irrelevant. No global (bi)linearity and no
continuity is required (continuity on `K₁ × K₂` follows in finite dimension). -/
def IsBiaffineOn {n m d : ℕ} (K₁ : Set (EuclideanSpace ℝ (Fin n)))
    (K₂ : Set (EuclideanSpace ℝ (Fin m)))
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d)) :
    Prop :=
  (∀ y ∈ K₂, ∀ x₁ ∈ K₁, ∀ x₂ ∈ K₁, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      u (a • x₁ + b • x₂) y = a • u x₁ y + b • u x₂ y) ∧
  (∀ x ∈ K₁, ∀ y₁ ∈ K₂, ∀ y₂ ∈ K₂, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      u x (a • y₁ + b • y₂) = a • u x y₁ + b • u x y₂)

end OnlineConvexOpt.Approachability


