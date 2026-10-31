-- Prove2me | Definitions.Def_GeomRescale_IsMinSet
-- name    : GeomRescale_IsMinSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:14:32.207304+00:00
-- url     : https://prove2.me/theorems/ba02132e-fe82-48ea-af65-23b0db5ae6cc
-- title:
--   $\mathrm{MinSet}(f, w)$, display (4)
-- statement:
--   If $v_1, \dots, v_n$ is the ordering computed by $\mathrm{GreedyMin}(f, w)$, then
--
--   $$\mathrm{MinSet}(f, w) = \operatorname{argmin}\{f(S) : S = \{v_1, \dots, v_i\}\ \exists i \in [n] \text{ or } S = \emptyset\}.$$
--
--   The predicate says that $S$ is such a minimizer for the given order. Any minimizer is allowed.
--
--   **Formalization Note** The weight vector appears only through the order, whose sortedness is stated at each use.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, display (4), p.4

import Mathlib
import Definitions.Def_GeomRescale_pref

namespace GeomRescale

/-- `S` is an element of `MinSet(f, w)` for the order `σ` that `GreedyMin(f, w)` used
(Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, display (4), p.4):
`MinSet(f, w) = argmin {f(S) : S = {v₁, …, v_i} ∃ i ∈ [n] or S = ∅}`.

**Formalization Note.** `pref σ 0 = ∅` covers "or `S = ∅`". Any argmin is allowed, and `σ` is the
order of `GreedyMin`, so the weight vector `w` appears only through `IsSortedBy w σ` at the use. -/
def IsMinSet {n : ℕ} (f : Finset (Fin n) → ℝ) (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    Prop :=
  (∃ i : ℕ, i ≤ n ∧ S = pref σ i) ∧ ∀ i : ℕ, i ≤ n → f S ≤ f (pref σ i)

end GeomRescale


