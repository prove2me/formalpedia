-- Prove2me | Definitions.Def_DualityStability_Stability_StablySet
-- name    : DualityStability_Stability_StablySet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:43:14.231918+00:00
-- url     : https://prove2.me/theorems/4724009a-7f2f-4cef-b1db-a500da877d53
-- title:
--   Directional derivative (4.3), unstably set and stably set problems, §4, p. 175
-- statement:
--   Let $F$ be a real topological vector space and $h : F \to [-\infty, +\infty]$ (in the paper, $h(z) = \inf (P(z))$).
--
--   1. When $h(0)$ is finite, the **directional derivative** of $h$ at $0$ in the direction $z$ is
--
--   $$
--   h'(0; z) = \lim_{\varepsilon \downarrow 0} \frac{h(\varepsilon z) - h(0)}{\varepsilon} \in [-\infty, +\infty]. \qquad (4.3)
--   $$
--
--   2. $(P)$ is **unstably set** if $h(0) = \inf (P)$ is finite and in every neighbourhood of $0$ one can choose vectors $z$ for which this directional derivative is a negative number of arbitrarily large magnitude: for every neighbourhood $U$ of $0$ and every real $M$ there is $z \in U$ with $h'(0; z) < -M$ (the value $-\infty$ qualifies).
--
--   3. $(P)$ is **stably set** if it is consistent, i.e. $h(0) = \inf (P) < +\infty$, but not unstably set. In particular $\inf (P) = -\infty$ counts as stably set.
--
--   Stability is the property that Theorem 1 guarantees and that the main duality theorem of the paper characterizes.
--
--   **Formalization Note** The definitions are stated for an arbitrary function $h$ so they also apply to the dual problem through $(P')$. The limit (4.3) is written as the lower limit `Filter.liminf` of $\varepsilon^{-1}(h(\varepsilon z) - h(0))$ along $\varepsilon \to 0^+$, computed in `EReal`; it equals the limit whenever the limit exists, and for convex $h$ finite at $0$ the quotient is nondecreasing in $\varepsilon$, so the limit exists (the paper's "exists by the convexity in Lemma 2"). Consistency of $(P)$ is $\inf (P) < +\infty$ (p. 173).
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 175, (4.3) and the definitions of 'unstably set' and 'stably set'; p. 173 (consistency ⇔ inf (P) < +∞)

import Mathlib

namespace DualityStability.Stability

/-- Rockafellar (1967), (4.3), p. 175: the one-sided directional derivative at `0` of a function
`h : F → [−∞, +∞]`,
`h′(0; z) = lim_{ε↓0} [h(εz) − h(0)]/ε`.
It is written as the lower limit along `ε → 0⁺`, which is the limit whenever the limit exists
(for a convex `h` finite at `0` the difference quotient is nondecreasing in `ε`, so the limit
exists in `[−∞, +∞]`). The quotient is `ε⁻¹ · (h(εz) − h(0))`, computed in `EReal`. -/
noncomputable def dirDeriv0 {F : Type*} [AddCommGroup F] [Module ℝ F] (h : F → EReal) (z : F) :
    EReal :=
  Filter.liminf (fun ε : ℝ => ((ε⁻¹ : ℝ) : EReal) * (h (ε • z) - h 0)) (nhdsWithin 0 (Set.Ioi 0))

/-- Rockafellar (1967), p. 175: with `h(z) = inf (P(z))`, the problem `(P)` is *unstably set* if
`inf (P) = h(0)` is finite and in every neighbourhood of `0` one can choose vectors `z` for which
the directional derivative (4.3) is a negative number of arbitrarily large magnitude (the value
`−∞` included, as the paper's parenthetical shows). -/
def UnstablySet {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] (h : F → EReal) :
    Prop :=
  ∃ r : ℝ, h 0 = (r : EReal) ∧
    ∀ U ∈ nhds (0 : F), ∀ M : ℝ, ∃ z ∈ U, dirDeriv0 h z < ((-M : ℝ) : EReal)

/-- Rockafellar (1967), p. 175: `(P)` is *stably set* if it is consistent (`inf (P) = h(0) < +∞`,
p. 173) but not unstably set. In particular `h(0) = −∞` is stably set. -/
def StablySet {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] (h : F → EReal) :
    Prop :=
  h 0 < ⊤ ∧ ¬ UnstablySet h

end DualityStability.Stability


