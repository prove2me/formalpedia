-- Prove2me | Definitions.Def_SubexpPermanent_Main_Subgradient
-- name    : SubexpPermanent_Main_Subgradient
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:00:09.098233+00:00
-- url     : https://prove2.me/theorems/57e29bbe-90de-4401-b918-4a7e390f12e6
-- title:
--   Subgradients, subdifferentials (also jointly in $(x,a)$) and the Euclidean projection $\Pi_K$
-- statement:
--   Let $f:\mathbb R^m\to\mathbb R$. A vector $g$ is a **subgradient** of $f$ at $x$ if $f(z)\ge f(x)+\langle g,z-x\rangle$ for every $z\in\mathbb R^m$; the **subdifferential** $\partial f(x)$ is the set of subgradients. For a function $f(x,a)$ of $(x,a)\in\mathbb R^m\times\mathbb R$, $\partial f(x,a)$ is the set of pairs $(g,g_0)$ with $f(z,b)\ge f(x,a)+\langle g,z-x\rangle+g_0(b-a)$ for all $(z,b)$. For $K\subseteq\mathbb R^m$, $\Pi_K(y)$ is the point of $K$ closest to $y$ in Euclidean distance; the predicate `IsEuclidProj K y p` says that $p\in K$ and $\|y-p\|_2\le\|y-q\|_2$ for every $q\in K$.
--
--   **Formalization Note.** $\langle g,z-x\rangle$ is `dotProduct`. For a nonempty compact convex $K$ there is exactly one closest point, so `IsEuclidProj K y p` is equivalent to $p=\Pi_K(y)$.
-- source:
--   Kudria, Luo, Majid, Subexponential Approximation of the Permanent in Deterministic Polynomial Time, arXiv:2609.10516 (held PDF, sha256 e752b6f0…), p. 15 (§4.2), p. 17 (Fact 4.11)

import Mathlib

namespace SubexpPermanent.Main

/-! # Subgradients, subdifferentials and Euclidean projection (Kudria–Luo–Majid, §4.2, pp. 15, 17) -/

variable {ι : Type*} [Fintype ι]

/-- `∂f(x)`: the vectors `g` with `f(z) ≥ f(x) + ⟨g, z − x⟩` for every `z`. -/
def subdiff (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : Set (ι → ℝ) :=
  {g | ∀ z : ι → ℝ, f x + dotProduct g (z - x) ≤ f z}

/-- The subdifferential of a function of `(x, a) ∈ ℝ^ι × ℝ`: the pairs `(g, g₀)` with
`f(z, b) ≥ f(x, a) + ⟨g, z − x⟩ + g₀ (b − a)` for every `(z, b)`. -/
def subdiffJoint (f : (ι → ℝ) → ℝ → ℝ) (x : ι → ℝ) (a : ℝ) : Set ((ι → ℝ) × ℝ) :=
  {g | ∀ (z : ι → ℝ) (b : ℝ), f x a + dotProduct g.1 (z - x) + g.2 * (b - a) ≤ f z b}

/-- `p = Π_K(y)`: `p` is a point of `K` closest to `y` in Euclidean distance (for a nonempty
compact convex `K` there is exactly one). -/
def IsEuclidProj {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) (y p : EuclideanSpace ℝ (Fin m)) :
    Prop :=
  p ∈ K ∧ ∀ q ∈ K, dist y p ≤ dist y q

end SubexpPermanent.Main


