-- Prove2me | Definitions.Def_NecoaraNG_GMIff_Setting
-- name    : NecoaraNG_GMIff_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:45:51.946213+00:00
-- url     : https://prove2.me/theorems/b0252472-8b8d-4ecc-82a6-9083d445f113
-- title:
--   Algorithm (GM), p. 19 — runs of the projected gradient method with step sizes α_k
-- statement:
--   This file adds the projected gradient method of Necoara, Nesterov and Glineur to the shared setting of the paper (the space $\mathbb R^n$ and the nearest-point relation $p=[u]_S$ of the imported module `NecoaraNG.Chain.Setting`).
--
--   Work in $\mathbb R^n$ with the Euclidean inner product and norm. Let $X\subseteq\mathbb R^n$, let $f$ be a function with gradient $\nabla f$, and let $(\alpha_k)_{k\ge0}$ be real step sizes. A sequence $(x^k)_{k\ge0}$ is a **run of the projected gradient method (GM)** with step sizes $(\alpha_k)$ if $x^0\in X$ and, for every $k\ge0$,
--   $$x^{k+1}=\bigl[x^k-\alpha_k\nabla f(x^k)\bigr]_X ,$$
--   that is, $x^{k+1}$ is a nearest point of $X$ to $x^k-\alpha_k\nabla f(x^k)$.
--
--   This is the algorithm whose linear convergence is proved in §5.1 (Theorems 11 and 12, with $\alpha_k=1/L_f$) and characterised in Theorem 13.
--
--   **Formalization Note** The projection is a predicate, not a chosen point; on a nonempty closed convex $X$ the nearest point exists and is unique, so a run is determined by $x^0$ and the step sizes. The page's step-size window $\alpha_k\in[\bar L_f^{-1},L_f^{-1}]$ is not part of a run; each theorem states the step sizes it uses. The page writes "Given $x^0\in X$ for $k\ge1$ do"; the iteration is indexed from $k=0$, as Theorems 11 and 12 use it (they bound $x^k$ in terms of $x^0$).
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 19, Algorithm (GM)

import Mathlib
import Definitions.Def_NecoaraNG_Chain_Setting
import Definitions.Def_NecoaraNG_ErrBound_Setting

namespace NecoaraNG.GMIff

open scoped InnerProductSpace

/-- A run of the projected gradient method (GM) with step sizes `α k` (p. 19):
`x⁰ ∈ X` and `x^{k+1} = [x^k - α_k ∇f(x^k)]_X` for every `k ≥ 0`. -/
def IsGMRun {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (f : NecoaraNG.Chain.E n → ℝ) (α : ℕ → ℝ) (x : ℕ → NecoaraNG.Chain.E n) : Prop :=
  x 0 ∈ X ∧ ∀ k, NecoaraNG.Chain.IsNearest X (x k - α k • gradient f (x k)) (x (k + 1))

end NecoaraNG.GMIff


