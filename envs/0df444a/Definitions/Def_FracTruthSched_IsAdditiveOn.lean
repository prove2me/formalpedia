-- Prove2me | Definitions.Def_FracTruthSched_IsAdditiveOn
-- name    : FracTruthSched_IsAdditiveOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:13.674505+00:00
-- url     : https://prove2.me/theorems/9c8b7a02-e943-43b3-a38a-d294684ab284
-- title:
--   Additivity of a function within a set of coordinates
-- statement:
--   Let $V$ be a function of nonnegative values $a=(a_d)$. $V$ is **additive within** a set $S$ of coordinates if, for every nonnegative $a$, with $a^0$ denoting $a$ with the coordinates in $S$ set to $0$,
--   $$V(a)-V(a^0)=\sum_{e\in S}\big(V(a^0+a_e\mathbf 1_e)-V(a^0)\big).$$
--   Equivalently, the increment from raising one value in $S$ does not depend on the other values in $S$. The values outside $S$ are arbitrary and fixed, so this is additivity within $S$ for every fixed choice of the other values.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, §2.3, Additivity and symmetry, p.6

import Mathlib

set_option autoImplicit false

namespace FracTruthSched

/-- **Additivity within a set of coordinates** (Anastasiadis et al., arXiv:2611.06642v1, §2.3,
*Additivity and symmetry*, p.6: "The function V is additive if V(a) − V(0_D) = Σ_{e∈D} (V(a_e 1_e) −
V(0_D)) for every a ∈ R^D_{≥0} … When we say that V is additive … within a subset of D, we apply
these definitions to that subset, with the values on the rest of D fixed"): for every nonnegative
`a`, writing `a⁰` for `a` with the coordinates in `S` set to `0`,
`V(a) − V(a⁰) = Σ_{e∈S} (V(a⁰ + a_e 1_e) − V(a⁰))`.

**Formalization Note.** `a⁰ + a_e 1_e` is `Function.update a⁰ e (a e)`. The values outside `S` are
those of `a`, arbitrary and nonnegative, so this is additivity within `S` for every fixed choice of
the other values. -/
def IsAdditiveOn {τ : Type*} [DecidableEq τ] (V : (τ → ℝ) → ℝ) (S : Finset τ) : Prop :=
  ∀ a : τ → ℝ, (∀ e, 0 ≤ a e) →
    V a - V (fun d => if d ∈ S then 0 else a d) =
      ∑ e ∈ S, (V (Function.update (fun d => if d ∈ S then 0 else a d) e (a e)) -
        V (fun d => if d ∈ S then 0 else a d))

end FracTruthSched


