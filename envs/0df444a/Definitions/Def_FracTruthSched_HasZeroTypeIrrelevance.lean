-- Prove2me | Definitions.Def_FracTruthSched_HasZeroTypeIrrelevance
-- name    : FracTruthSched_HasZeroTypeIrrelevance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:32:07.800206+00:00
-- url     : https://prove2.me/theorems/575547cf-1410-47b7-a327-2c65bcf6625d
-- title:
--   Zero-type irrelevance (Definition 4, property (iii))
-- statement:
--   The **type** of an edge is the pair of its two endpoint values; it is a **zero type** if at least one of them is zero. An allocation function on $MC_\ell$ satisfies **zero-type irrelevance** if changing one edge from a zero type to another zero type, with all other values fixed, leaves the allocation of every other task (self-loops included) unchanged: if graph inputs $t,t'$ differ only in the endpoint values of an edge $e$ and $e$ has a zero type in both, then $x_{uf}(t)=x_{uf}(t')$ for every machine $u$ and task $f\ne e$.
--
--   The allocation of the changed edge itself may change. This is property (iii) of the padding lemma.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Definition 4, p.9; Lemma 1 (iii), p.9

import Mathlib
import Definitions.Def_FracTruthSched_FracMech
import Definitions.Def_FracTruthSched_IsGraphInput

set_option autoImplicit false

namespace FracTruthSched

/-- **Zero-type irrelevance** (Anastasiadis et al., arXiv:2611.06642v1, Definition 4, p.9: "The type
of an edge is the pair of its two endpoint values. An edge has a zero type if at least one of these
values is zero. An allocation function satisfies zero-type irrelevance if changing one edge from a
zero type to another zero type, with all other values fixed, leaves the allocation of every other
task (including the self-loops) unchanged.").

**Formalization Note.** Two graph inputs `t, t'` that agree on every task `f ≠ e` differ only in the
two endpoint values of the edge `e` (all other entries of column `e` are `0` in both). The zero type
condition is that some endpoint of `e` has value `0`, in `t` and in `t'`. The conclusion covers every
machine and every task `f ≠ e`, self-loops included. -/
def HasZeroTypeIrrelevance {n ℓ : ℕ} (M : FracMech n (CoreTask n ℓ)) : Prop :=
  ∀ t t', IsGraphInput t → IsGraphInput t' → ∀ e : CoreTask n ℓ, e.isLeft →
    (∀ u f, f ≠ e → t u f = t' u f) →
    (∃ u, incident u e ∧ t u e = 0) → (∃ u, incident u e ∧ t' u e = 0) →
    ∀ u f, f ≠ e → M.x t u f = M.x t' u f

end FracTruthSched


