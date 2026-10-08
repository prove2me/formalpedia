-- Prove2me | Definitions.Def_ErrBoundCplx_Cplx_DescentSeq
-- name    : ErrBoundCplx_Cplx_DescentSeq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:10.735628+00:00
-- url     : https://prove2.me/theorems/85cabf4b-e91d-43ba-81f4-e51edde6c3fb
-- title:
--   §2, §4.1: min f = 0, the KL inequality on the band [0 < f < r̄], and subgradient descent sequences (H1)–(H2)
-- statement:
--   Let $H$ be a real Hilbert space and $f : H \to (-\infty, +\infty]$. The convex subdifferential of $f$ at $x$ is $\partial f(x) = \{u \in H : f(y) \ge f(x) + \langle u, y - x\rangle \text{ for all } y \in H\}$ (empty when $f(x) = +\infty$). This module fixes three notions used throughout §4 of Bolte–Nguyen–Peypouquet–Suter.
--
--   1. **Normalization.** $f$ satisfies $\min f = 0$ with $\operatorname{argmin} f \neq \emptyset$: $f(y) \ge 0$ for every $y$, and $f(x) = 0$ for some $x$. The set of minimizers is then $S = \{x : f(x) = 0\}$.
--
--   2. **KL property on a band.** Given $\bar r > 0$ and a function $\varphi$, $f$ has the KL property on $[0 < f < \bar r]$ with desingularizing function $\varphi$ when
--   $$\varphi'(f(x))\,\|\partial^0 f(x)\| \ge 1 \qquad \text{for every } x \text{ with } 0 < f(x) < \bar r,$$
--   where $\partial^0 f(x)$ is the least-norm element of $\partial f(x)$ and $\|\partial^0 f(x)\| = +\infty$ when $\partial f(x) = \emptyset$. Equivalently, $\varphi'(f(x))\,\|v\| \ge 1$ for every $v \in \partial f(x)$.
--
--   3. **Subgradient descent sequences.** A sequence $(x_k)_{k \in \mathbb N}$ in $H$ is a subgradient descent sequence for $f$ with constants $a, b$ if $x_0 \in \operatorname{dom} f$ and
--      - (H1) (sufficient decrease) for each $k \ge 1$, $f(x_k) + a\|x_k - x_{k-1}\|^2 \le f(x_{k-1})$;
--      - (H2) (relative error) for each $k \ge 1$ there is $\omega_k \in \partial f(x_k)$ with $\|\omega_k\| \le b\,\|x_k - x_{k-1}\|$.
--
--   Subgradient descent sequences are produced by many first-order methods (forward–backward splitting, alternating and majorization–minimization schemes); the KL inequality on a band is the geometric assumption under which their complexity is analysed.
--
--   **Formalization Note** $f$ takes values in `EReal`; the subdifferential is the published `subgrad` of `MoreauProx.Characterization.GammaZero`. On the band $f(x)$ is a real number and enters $\varphi'$ through `toReal`; $\varphi'$ is `deriv φ`. The least-norm element is not constructed: the "for every $v$" form is used instead. The constants $a, b$ are parameters of the predicate; theorems that use it assume $a, b > 0$.
-- source:
--   arXiv:1510.08234v3 (Bolte, Nguyen, Peypouquet, Suter, From error bounds to the complexity of first-order descent methods for convex functions), §2, p. 4 (argmin f ≠ ∅, min f = 0, ∂f); §2.1, p. 5 (∂⁰f, ‖∂⁰f(x)‖ = +∞ off dom ∂f); §2.3, p. 6, (2); §4.1, p. 14, (H1), (H2); §4.2, p. 17 (KL on [0 < f < r̄])

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
open MoreauProx.Characterization

namespace ErrBoundCplx.Cplx

/-- §2, p. 4: the standing normalization of the paper, "argmin f is nonempty and min f = 0":
`f` takes only values `≥ 0` and attains the value `0`. Then `argmin f = {x | f x = 0}`. -/
def IsMinZero {H : Type*} (f : H → EReal) : Prop :=
  (∀ y, 0 ≤ f y) ∧ ∃ x, f x = 0

/-- §2.3 (p. 6) and §4.2 (p. 17): `f` has the KL property on the band `[0 < f < r̄]` with
desingularizing function `φ`:
`φ'(f(x)) ‖∂⁰f(x)‖ ≥ 1` for every `x` with `0 < f(x) < r̄`.
Here `∂⁰f(x)` is the least-norm element of the convex subdifferential `∂f(x)`, with
`‖∂⁰f(x)‖ = +∞` when `∂f(x) = ∅`. Since `‖∂⁰f(x)‖` is the minimum of `‖v‖` over `v ∈ ∂f(x)`,
the inequality at `∂⁰f(x)` is the inequality for every `v ∈ ∂f(x)`, which is how it is stated.
On the band `f x` is a real number in `(0, r̄)`, so `(f x).toReal` is that number. -/
def KLOnBand {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (rbar : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ x, 0 < f x → f x < (rbar : EReal) →
    ∀ v ∈ subgrad f x, 1 ≤ deriv φ (f x).toReal * ‖v‖

/-- §4.1, p. 14: `(x_k)_{k ∈ ℕ}` is a subgradient descent sequence for `f` with constants
`a, b` (the theorems using it assume `a, b > 0`) if `x₀ ∈ dom f` and
* (H1) (sufficient decrease) for each `k ≥ 1`, `f(x_k) + a ‖x_k − x_{k−1}‖² ≤ f(x_{k−1})`;
* (H2) (relative error) for each `k ≥ 1` there is `ω_k ∈ ∂f(x_k)` with
  `‖ω_k‖ ≤ b ‖x_k − x_{k−1}‖`.
Indices start at `0`, as on the page. -/
def IsSubgradDescentSeq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (a b : ℝ) (x : ℕ → H) : Prop :=
  f (x 0) ≠ ⊤ ∧
    (∀ k ≥ 1, f (x k) + ((a * ‖x k - x (k - 1)‖ ^ 2 : ℝ) : EReal) ≤ f (x (k - 1))) ∧
    (∀ k ≥ 1, ∃ ω ∈ subgrad f (x k), ‖ω‖ ≤ b * ‖x k - x (k - 1)‖)

end ErrBoundCplx.Cplx


