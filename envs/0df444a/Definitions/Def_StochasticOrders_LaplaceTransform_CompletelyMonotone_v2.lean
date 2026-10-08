-- Prove2me | Definitions.Def_StochasticOrders_LaplaceTransform_CompletelyMonotone_v2
-- name    : StochasticOrders_LaplaceTransform_CompletelyMonotone_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:18:37.912552+00:00
-- url     : https://prove2.me/theorems/eb0d75ba-a1cb-4be1-ab24-78973a142aca
-- title:
--   Completely monotone functions (corrected: smoothness on $(0,\infty)$ only)
-- statement:
--   A function $\varphi : [0,\infty) \to \mathbb{R}$ is **completely monotone** if all its derivatives $\varphi^{(n)}$ exist and
--
--   $$(-1)^n \varphi^{(n)}(x) \ge 0 \quad \text{for all } x > 0 \text{ and } n = 0, 1, 2, \dots$$
--
--   (Shaked & Shanthikumar, p. 234). Equivalently (Bernstein's theorem, which the book states but does not reprove), $\varphi$ is completely monotone if and only if there is a measure $\mu$ on $[0,\infty)$ with $\varphi(x) = \int_0^\infty e^{-xu}\,\mu(du)$. The function $\varphi(x) = e^{-sx}$ is completely monotone for every $s > 0$, which connects this notion to the Laplace transform order.
--
--   **Formalization Note** This is the corrected (`_v2`) form of `StochasticOrders_LaplaceTransform_CompletelyMonotone`. `CompletelyMonotone φ` bundles `ContDiffOn ℝ ⊤ φ (Set.Ioi 0)` (all derivatives of `φ` exist on the open half-line $(0,\infty)$; since `Set.Ioi 0` is open, `iteratedDeriv n φ x` at $x>0$ is then the honest $n$-th derivative, so the junk value `0` of a nonexistent derivative cannot arise) with the sign condition for every $n$ and every $x > 0$. The retired definition demanded `ContDiff ℝ ⊤ φ` on all of $\mathbb{R}$, i.e. smoothness on $(-\infty,0]$ as well, which the book's class of functions on $[0,\infty)$ does not require and which excluded, e.g., every function whose derivatives blow up at $0^+$. The value of `φ` on $(-\infty,0)$ is irrelevant and no condition is imposed at $x = 0$ itself; a theorem that needs continuity at $0$ (such as Theorem 5.A.7 for the function $g$ it transforms) states it separately.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 234

import Mathlib

namespace StochasticOrders.LaplaceTransform

/-- A function `φ` (the book's `φ : [0,∞) → ℝ`, here a function on `ℝ` whose values on `(-∞, 0)`
are irrelevant) is completely monotone (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007,
p. 234) if all its derivatives exist and `(-1)^n φ^(n)(x) ≥ 0` for every `x > 0` and every
`n = 0, 1, 2, …`. Existence of every derivative on the open half-line `(0, ∞)` is carried by
`ContDiffOn ℝ (⊤ : ℕ∞) φ (Set.Ioi 0)` (`φ` is `C^∞` on `(0, ∞)`), which guards against the junk
value `iteratedDeriv n φ x = 0` that a nonexistent derivative would otherwise silently supply;
since `Set.Ioi 0` is open, `iteratedDeriv n φ x` at `x > 0` is then the honest `n`-th derivative.

Corrected version (`_v2`): the previous definition demanded `ContDiff ℝ ⊤ φ` on all of `ℝ`, i.e.
smoothness on `(-∞, 0]` as well, which the book's class (functions on `[0,∞)`, derivatives and
sign conditions for `x > 0`) does not require; that excluded, e.g., every function whose
derivatives blow up at `0⁺`. No condition is imposed at `x = 0` itself: a theorem that needs
continuity at `0` (e.g. Theorem 5.A.7 for the function `g` it transforms) states it separately. -/
def CompletelyMonotone (φ : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) φ (Set.Ioi 0) ∧
    ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n φ x

end StochasticOrders.LaplaceTransform


