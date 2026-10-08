-- Prove2me | Definitions.Def_ErrBoundCplx_ISTA_DescentSeq
-- name    : ErrBoundCplx_ISTA_DescentSeq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:50.668975+00:00
-- url     : https://prove2.me/theorems/f5ad6a4d-2e92-44af-bebb-7f02c9a41f9a
-- title:
--   §2, §4.1, §4.2, Corollary 19: min f = 0, the KL inequality on X ∩ [0 < f < r̄], and subgradient descent sequences (H1)–(H2)
-- statement:
--   Let $H$ be a real Hilbert space and $f : H \to (-\infty, +\infty]$. The convex subdifferential of $f$ at $x$ is $\partial f(x) = \{u \in H : f(y) \ge f(x) + \langle u, y - x\rangle \text{ for all } y \in H\}$, empty when $f(x) = +\infty$. This module fixes the notions of §4 of Bolte–Nguyen–Peypouquet–Suter that the ISTA mission uses.
--
--   1. **Normalization.** $f$ satisfies $\min f = 0$ with $\operatorname{argmin} f \neq \emptyset$: $f(y) \ge 0$ for every $y$ and $f(x) = 0$ for some $x$. The set of minimizers is then $S = \{x : f(x) = 0\}$.
--
--   2. **KL property on a stable set.** Given $X \subseteq H$, $\bar r > 0$ and a function $\varphi$, $f$ has the KL property on $X \cap [0 < f < \bar r]$ with desingularizing function $\varphi$ when
--   $$\varphi'(f(x))\,\|\partial^0 f(x)\| \ge 1 \qquad \text{for every } x \in X \text{ with } 0 < f(x) < \bar r,$$
--   where $\partial^0 f(x)$ is the least-norm element of $\partial f(x)$ and $\|\partial^0 f(x)\| = +\infty$ when $\partial f(x) = \emptyset$. Equivalently, $\varphi'(f(x))\,\|v\| \ge 1$ for every $v \in \partial f(x)$. For $X = H$ this is the KL property on the band $[0 < f < \bar r]$ of §4.2; general $X$ is the relaxation of Corollary 19.
--
--   3. **Conditions (H1) and (H2).** For a sequence $(x_k)_{k \in \mathbb N}$ in $H$ and constants $a, b$:
--      - (H1) (sufficient decrease) for each $k \ge 1$, $f(x_k) + a\|x_k - x_{k-1}\|^2 \le f(x_{k-1})$;
--      - (H2) (relative error) for each $k \ge 1$ there is $\omega_k \in \partial f(x_k)$ with $\|\omega_k\| \le b\,\|x_k - x_{k-1}\|$.
--
--   4. **Subgradient descent sequences.** $(x_k)$ is a subgradient descent sequence for $f$ with constants $a, b$ if $x_0 \in \operatorname{dom} f$ and (H1), (H2) hold.
--
--   These are the hypotheses under which the paper turns a KL inequality into complexity bounds for first-order methods.
--
--   **Formalization Note** $f$ takes values in `EReal`; the subdifferential is the published `subgrad` of `MoreauProx.Characterization.GammaZero`. On the band, $f(x)$ is real and enters $\varphi'$ through `toReal`; $\varphi'$ is `deriv φ`. The least-norm element is not constructed: the "for every $v$" form is used. The constants $a, b$ are parameters; theorems using the predicate assume $a, b > 0$. (H1) and (H2) are separate predicates because Proposition 13 establishes them without assuming $x_0 \in \operatorname{dom} f$. These notions restate mission 01's (`ErrBoundCplx.Cplx`) locally, with the same clauses.
-- source:
--   arXiv:1510.08234v3, §2, p. 4 (argmin f ≠ ∅, min f = 0); §2.1, p. 5 (∂⁰f, ‖∂⁰f(x)‖ = +∞ off dom ∂f); §4.1, p. 14, (H1), (H2); §4.2, p. 17 (KL on [0 < f < r̄]); Corollary 19, p. 19 (stable set X ∩ [0 < f < r̄])

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_ErrBoundCplx_Cplx_DescentSeq
open MoreauProx.Characterization

namespace ErrBoundCplx.ISTA

/-- §4.2, p. 17, with the stable-set relaxation of Corollary 19, p. 19: `f` has the KL property
on `X ∩ [0 < f < r̄]` with desingularizing function `φ`:
`φ'(f(x)) ‖∂⁰f(x)‖ ≥ 1` for every `x ∈ X` with `0 < f(x) < r̄`.
`∂⁰f(x)` is the least-norm element of the convex subdifferential `∂f(x)`, with
`‖∂⁰f(x)‖ = +∞` when `∂f(x) = ∅`; since `‖∂⁰f(x)‖` is the minimum of `‖v‖` over `∂f(x)`, the
inequality at `∂⁰f(x)` is the inequality for every `v ∈ ∂f(x)`, which is how it is stated.
On the band `f x` is a real number, so `(f x).toReal` is that number. With `X = univ` this is
the KL property on `[0 < f < r̄]` (mission 01's `KLOnBand`). -/
def KLOnSet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (X : Set H) (rbar : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ x ∈ X, 0 < f x → f x < (rbar : EReal) →
    ∀ v ∈ subgrad f x, 1 ≤ deriv φ (f x).toReal * ‖v‖

/-- (H1), §4.1, p. 14 (sufficient decrease condition with constant `a`): for each `k ≥ 1`,
`f(x_k) + a ‖x_k − x_{k−1}‖² ≤ f(x_{k−1})`, computed in `EReal`. -/
def SatisfiesH1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (a : ℝ) (x : ℕ → H) : Prop :=
  ∀ k ≥ 1, f (x k) + ((a * ‖x k - x (k - 1)‖ ^ 2 : ℝ) : EReal) ≤ f (x (k - 1))

/-- (H2), §4.1, p. 14 (relative error condition with constant `b`): for each `k ≥ 1` there is
`ω_k ∈ ∂f(x_k)` with `‖ω_k‖ ≤ b ‖x_k − x_{k−1}‖`. -/
def SatisfiesH2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (b : ℝ) (x : ℕ → H) : Prop :=
  ∀ k ≥ 1, ∃ ω ∈ subgrad f (x k), ‖ω‖ ≤ b * ‖x k - x (k - 1)‖

/-- §4.1, p. 14: `(x_k)_{k ∈ ℕ}` is a subgradient descent sequence for `f` with constants
`a, b` (the theorems using it assume `a, b > 0`) if `x₀ ∈ dom f` and (H1), (H2) hold.
Indices start at `0`, as on the page. (Local copy of mission 01's
`ErrBoundCplx.Cplx.IsSubgradDescentSeq`, with the same three clauses.) -/
def IsSubgradDescentSeq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (a b : ℝ) (x : ℕ → H) : Prop :=
  f (x 0) ≠ ⊤ ∧ SatisfiesH1 f a x ∧ SatisfiesH2 f b x

end ErrBoundCplx.ISTA


