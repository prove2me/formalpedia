-- Prove2me | Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
-- name    : RockafellarMaxMono_Shared_ProperConvex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:59:48.122448+00:00
-- url     : https://prove2.me/theorems/b750c28d-910d-4e74-a099-c030ebcf1ff0
-- title:
--   Proper convex function $V \to (-\infty, +\infty]$
-- statement:
--   Let $V$ be a real normed space. A **proper convex function** on $V$ is a function $f$ from $V$ to $(-\infty, +\infty]$, not identically $+\infty$, such that
--
--   $$
--   f((1-\lambda)x + \lambda y) \le (1-\lambda) f(x) + \lambda f(y)
--   $$
--
--   whenever $x \in V$, $y \in V$ and $0 < \lambda < 1$. On the right-hand side the usual conventions of $(-\infty,+\infty]$ apply: $\mu \cdot (+\infty) = +\infty$ for $\mu > 0$ and $a + (+\infty) = +\infty$.
--
--   This is the class of functions to which Rockafellar's Theorem A applies; the definition is stated on an arbitrary real normed space so that it can be applied both to a Banach space $E$ and to its dual $E^*$ (where the conjugate $f^*$ lives).
--
--   It serves chunk 01-maximal-monotone (p. 209; the hypothesis of Theorem A, p. 209, and of the lemmas of §§2–3, pp. 210–213, where it is applied both on $E$ and to the conjugate $f^*$ on $E^*$) and chunk 02-cyclic-characterization (p. 209; the hypothesis of Theorem B, p. 209, and of the lemmas of §§2–4, pp. 210–215).
--
--   **Formalization Note** The value set $(-\infty,+\infty]$ is encoded as `EReal` together with the clause "$f(x) \ne -\infty$ for every $x$". "Not identically $+\infty$" is the clause "$f(x) \ne +\infty$ for some $x$". The convexity inequality is the paper's own, with $\lambda$ written `t`, computed in `EReal`.
-- source:
--   Rockafellar, On the maximal monotonicity of subdifferential mappings, Pacific J. Math. 33 (1970), p. 209, definition of a proper convex function

import Mathlib

namespace RockafellarMaxMono.Shared

/-- Rockafellar (1970), p. 209: a *proper convex function* on a real normed space `V` is a
function `f : V → (−∞, +∞]`, not identically `+∞`, such that
`f((1 − λ)x + λy) ≤ (1 − λ)f(x) + λf(y)` whenever `x, y ∈ V` and `0 < λ < 1`.
The value set `(−∞, +∞]` is encoded as `EReal` together with the requirement that `f`
never takes the value `⊥ = −∞`. -/
def ProperConvex {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : V → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ (∃ x, f x ≠ ⊤) ∧
    ∀ (x y : V) (t : ℝ), 0 < t → t < 1 →
      f ((1 - t) • x + t • y) ≤ ((1 - t : ℝ) : EReal) * f x + ((t : ℝ) : EReal) * f y

end RockafellarMaxMono.Shared


