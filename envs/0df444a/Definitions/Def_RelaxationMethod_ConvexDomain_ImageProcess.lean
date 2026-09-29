-- Prove2me | Definitions.Def_RelaxationMethod_ConvexDomain_ImageProcess
-- name    : RelaxationMethod_ConvexDomain_ImageProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:45:30.157661+00:00
-- url     : https://prove2.me/theorems/86591c20-4284-44d4-b7a0-0dabcdad8978
-- title:
--   The image of a point with respect to a convex set, and the reflexion process (3.1)–(3.2) of §9
-- statement:
--   Let $E_n$ denote $n$-dimensional Euclidean space and let $A \subseteq E_n$ be a set.
--
--   1. A point $q$ is a **nearest point of $A$ to $p$** if $q \in A$ and $|p - q| \le |p - a|$ for every $a \in A$.
--   2. A point $p_1$ is an **image of $p$ with respect to $A$** if there is a nearest point $q$ of $A$ to $p$ with
--   $$p_1 = p + 2(q - p) = F(p),$$
--   that is, $p_1$ is the reflexion of $p$ through $q$ (Motzkin–Schoenberg, §9, (3.1)).
--   3. A sequence $p_0, p_1, p_2, \dots$ is a **run of the reflexion process** with respect to $A$ if $p_{\nu+1}$ is an image of $p_\nu$ whenever $p_\nu \notin A$ (§9, (3.2)). "The process terminates" means some $p_N \in A$; "the process produces an infinite sequence" means $p_\nu \notin A$ for all $\nu$.
--
--   When $A$ is nonempty, closed and convex, the nearest point exists and is unique, so the image is a genuine function $F(p)$; the relational form avoids choosing it.
--
--   **Formalization Note** Once a run enters $A$ the process has terminated and the later terms are unconstrained. The factor $2$ is fixed (the paper's reflexion process, $\lambda = 2$).
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), p. 402, §9, (3.1), (3.2)

import Mathlib

namespace RelaxationMethod.ConvexDomain

/-- `q` is a point of `A` nearest to `p`: `q ∈ A` and `|p - q| ≤ |p - a|` for every `a ∈ A`
(Motzkin–Schoenberg 1954, §9, p. 402). -/
def IsNearestPoint {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (p q : EuclideanSpace ℝ (Fin n)) : Prop :=
  q ∈ A ∧ ∀ a ∈ A, dist p q ≤ dist p a

/-- §9, (3.1), p. 402: `p₁` is the image of `p` with respect to `A`, i.e.
`p₁ = p + 2(q - p)` where `q` is the point of `A` nearest to `p` (reflexion of `p` through `q`). -/
def IsImage {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (p p₁ : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ q, IsNearestPoint A p q ∧ p₁ = p + (2 : ℝ) • (q - p)

/-- §9, (3.2), p. 402: `p₀, p₁, p₂, …` is a run of the reflexion process with respect to `A`:
whenever `p_ν ∉ A`, the next point is the image `p_{ν+1} = F(p_ν)`. Once a point lies in `A`
the process has terminated and later terms are unconstrained. -/
def IsImageRun {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (p : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ ν : ℕ, p ν ∉ A → IsImage A (p ν) (p (ν + 1))

end RelaxationMethod.ConvexDomain


