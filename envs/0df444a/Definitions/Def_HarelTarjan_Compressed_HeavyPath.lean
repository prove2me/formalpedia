-- Prove2me | Definitions.Def_HarelTarjan_Compressed_HeavyPath
-- name    : HarelTarjan_Compressed_HeavyPath
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:50:45.754316+00:00
-- url     : https://prove2.me/theorems/4635cf76-cd87-44bf-b98e-ecbea7d72699
-- title:
--   Heavy and light edges, and the apex of the heavy path containing a vertex
-- statement:
--   The heavy-path decomposition of §4 (p. 343) of Harel and Tarjan.
--
--   Let $T$ be a rooted tree with root $r$. An edge $v \to p_T(v)$ (with $v \ne r$) is **light** if
--   $$2\cdot \mathrm{size}_T(v) \le \mathrm{size}_T(p_T(v))$$
--   and **heavy** otherwise. At most one heavy edge enters each vertex, so the heavy edges partition the vertices of $T$ into **heavy paths**; a vertex with no entering or exiting heavy edge is a single-vertex heavy path.
--
--   The **apex** of a heavy path is its vertex of smallest depth, and $\mathrm{apex}(v)$ is the apex of the heavy path containing $v$. It is obtained from $v$ by climbing heavy edges for as long as they exist:
--   $$\mathrm{apex}(v) = p_T^{k}(v), \qquad k = \min\{\, j \ge 0 : \text{the edge } p_T^{j}(v) \to p_T^{j+1}(v) \text{ is not heavy (or } p_T^j(v) = r) \,\}.$$
--   A vertex $v$ is an apex when $\mathrm{apex}(v) = v$.
--
--   The apex map is the building block of the compressed tree.
--
--   **Formalization Note** `IsHeavy T v` includes $v \ne r$, so the root never has an exiting heavy edge and is always an apex. The file contains the two-line lemma that the minimum above exists (the root qualifies), which `Nat.find` needs.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 343, §4 (light and heavy edges, heavy paths, apex)

import Mathlib
import Definitions.Def_HarelTarjan_Compressed_RootedTree

namespace HarelTarjan.Compressed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edge `v → p_T(v)` is **heavy** (§4, p. 343): `v` is not the root (so the edge exists) and
`2 · size_T(v) > size_T(p_T(v))`. The edge is **light** when `2 · size_T(v) ≤ size_T(p_T(v))`. -/
def IsHeavy (T : RootedTree V) (v : V) : Prop :=
  v ≠ T.root ∧ size T (T.parent v) < 2 * size T v

noncomputable instance (T : RootedTree V) : DecidablePred (IsHeavy T) := fun v => by
  unfold IsHeavy; infer_instance

/-- Some iterate of the parent map from `v` sits at a vertex whose edge to its parent is not heavy
(the root is such a vertex). -/
theorem exists_not_isHeavy_iterate (T : RootedTree V) (v : V) :
    ∃ k : ℕ, ¬ IsHeavy T (T.parent^[k] v) := by
  obtain ⟨i, hi⟩ := T.reaches v
  exact ⟨i, fun h => h.1 hi⟩

/-- The number of heavy edges climbed from `v` to the apex of its heavy path: the least `k` such
that the edge leaving `pᵏ(v)` is not heavy. -/
noncomputable def apexSteps (T : RootedTree V) (v : V) : ℕ := Nat.find (exists_not_isHeavy_iterate T v)

/-- `apex(v)` (§4, p. 343): the apex (vertex of smallest depth) of the heavy path containing `v`.
It is reached from `v` by following heavy edges upward for as long as they exist:
`apex(v) = pᵏ(v)` for the least `k` such that the edge `pᵏ(v) → pᵏ⁺¹(v)` is not heavy. -/
noncomputable def apex (T : RootedTree V) (v : V) : V := T.parent^[apexSteps T v] v

/-- `v` is an apex: it is the top of its own heavy path. -/
def IsApex (T : RootedTree V) (v : V) : Prop := apex T v = v

end HarelTarjan.Compressed


