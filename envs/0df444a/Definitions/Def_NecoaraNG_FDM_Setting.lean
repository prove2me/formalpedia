-- Prove2me | Definitions.Def_NecoaraNG_FDM_Setting
-- name    : NecoaraNG_FDM_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:45:29.368909+00:00
-- url     : https://prove2.me/theorems/7a67169d-86e1-4bfa-b1d1-d472b752670d
-- title:
--   (P), (1), (22), (FDM), pp. 3, 8, 29 — optimal set, nearest points, quadratic functional growth and runs of the feasible descent method
-- statement:
--   This module fixes the objects of §5.3 of Necoara, Nesterov and Glineur. Throughout, $\mathbb R^n$ carries the Euclidean inner product $\langle u,v\rangle=u^\top v$ and the Euclidean norm.
--
--   1. **Optimal set** (p. 3). For a set $X\subseteq\mathbb R^n$ and $f:\mathbb R^n\to\mathbb R$, the optimal set of problem $(\mathrm P)$: $f^*=\min_{x\in X}f(x)$ is
--   $$
--   X^*=\{x\in X:\ f(x)\le f(y)\ \text{for all } y\in X\}.
--   $$
--   2. **Nearest points** (pp. 2–3). A point $p$ is a nearest point of $S$ to $u$, written $p=[u]_S$, when $p\in S$ and $\|u-p\|\le\|u-z\|$ for every $z\in S$.
--   3. **Quadratic functional growth** (Definition 4, (22), p. 8) with constant $\kappa$: for every $x\in X$ and every nearest point $\bar x=[x]_{X^*}$,
--   $$
--   f(x)-f^*\ \ge\ \frac{\kappa}{2}\,\|x-\bar x\|^2 ,
--   $$
--   where $f^*=f(\bar x)$.
--   4. **Runs of the feasible descent method (FDM)** (p. 29). Given constants $\beta$, $L$, $\bar L_f$, stepsizes $(\alpha_k)_{k\ge0}$, errors $(e^k)_{k\ge0}$ and iterates $(x^k)_{k\ge0}$, the triple is a run of (FDM) when $x^0\in X$ and, for every $k\ge0$,
--   $$
--   x^{k+1}=\big[x^k-\alpha_k\nabla f(x^k)+e^k\big]_X,\qquad \|e^k\|\le\beta\|x^{k+1}-x^k\|,\qquad f(x^{k+1})\le f(x^k)-\frac L2\|x^{k+1}-x^k\|^2,\qquad \alpha_k\ge\bar L_f^{-1}.
--   $$
--
--   The errors $e^k$ are any vectors satisfying the two conditions, so (FDM) is a family of methods; the paper notes (p. 29) that proximal point minimization, coordinate descent, extragradient descent and matrix splitting methods are feasible descent methods.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. The projection $[u]_S$ is the predicate `IsNearest S u p`, never a choice function; for closed convex nonempty $S$ the nearest point exists and is unique. $\nabla f$ is Mathlib's `gradient`, and $f^*$ is the value of $f$ at a point of $X^*$ rather than an infimum. Positivity of $\beta$, $L$, $\bar L_f$ ("$\beta,L>0$", "$\bar L_f^{-1}>0$") is not part of the run predicate; it is a hypothesis of each theorem that needs it.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, pp. 3, 8, 29, (P), (1), Definition 4 (22), Algorithm (FDM)

import Mathlib
import Definitions.Def_NecoaraNG_Chain_Setting
import Definitions.Def_NecoaraNG_ErrBound_Setting

namespace NecoaraNG.FDM

open scoped InnerProductSpace

/-- A run of the feasible descent method (FDM), p. 29: iterates `x`, errors `e` and stepsizes
`α` such that `x⁰ ∈ X` and, for every `k ≥ 0`,
`x^{k+1} = [x^k - α_k ∇f(x^k) + e^k]_X`, `‖e^k‖ ≤ β ‖x^{k+1} - x^k‖`,
`f(x^{k+1}) ≤ f(x^k) - L/2 ‖x^{k+1} - x^k‖²` and `α_k ≥ L̄_f⁻¹`. -/
def IsFDMRun {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (f : NecoaraNG.Chain.E n → ℝ) (β L Lbar : ℝ) (α : ℕ → ℝ)
    (e x : ℕ → NecoaraNG.Chain.E n) : Prop :=
  x 0 ∈ X ∧ ∀ k : ℕ,
    NecoaraNG.Chain.IsNearest X (x k - α k • gradient f (x k) + e k) (x (k + 1)) ∧
      ‖e k‖ ≤ β * ‖x (k + 1) - x k‖ ∧
      f (x (k + 1)) ≤ f (x k) - L / 2 * ‖x (k + 1) - x k‖ ^ 2 ∧
      1 / Lbar ≤ α k

end NecoaraNG.FDM


