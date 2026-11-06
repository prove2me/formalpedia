-- Prove2me | Definitions.Def_FracTruthSched_IsSymmetricOn
-- name    : FracTruthSched_IsSymmetricOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:14.105404+00:00
-- url     : https://prove2.me/theorems/30dcc500-37d2-4a75-a0b6-5189dabec71b
-- title:
--   Symmetry of a function within a set of coordinates
-- statement:
--   A function $V$ of nonnegative values is **symmetric within** a set $S$ of coordinates if it is unchanged by every permutation of the coordinates in $S$, with the values outside $S$ fixed: $V(a\circ\sigma)=V(a)$ for every nonnegative $a$ and every permutation $\sigma$ fixing all coordinates outside $S$.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, §2.3, Additivity and symmetry, p.6

import Mathlib

set_option autoImplicit false

namespace FracTruthSched

/-- **Symmetry within a set of coordinates** (Anastasiadis et al., arXiv:2611.06642v1, §2.3,
*Additivity and symmetry*, p.6: "The function V is symmetric if it is unchanged by every permutation
of the coordinates in D. When we say that V is … symmetric within a subset of D, we apply these
definitions to that subset, with the values on the rest of D fixed"): `V(a ∘ σ) = V(a)` for every
nonnegative `a` and every permutation `σ` fixing every coordinate outside `S`. -/
def IsSymmetricOn {τ : Type*} (V : (τ → ℝ) → ℝ) (S : Finset τ) : Prop :=
  ∀ σ : Equiv.Perm τ, (∀ e, e ∉ S → σ e = e) → ∀ a : τ → ℝ, (∀ e, 0 ≤ a e) → V (a ∘ σ) = V a

end FracTruthSched


