-- Prove2me | Definitions.Def_RollingProbeQN_Convex_IsStructOrthPartition
-- name    : RollingProbeQN_Convex_IsStructOrthPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:18:55.533244+00:00
-- url     : https://prove2.me/theorems/1602cbc6-076d-4564-93ee-98d0f1201a15
-- title:
--   Structurally orthogonal partition of the columns for a pattern $\mathcal S$
-- statement:
--   A **pattern** is a symmetric set $\mathcal S\subseteq[d]\times[d]$; $\mathcal S_j=\{i:(i,j)\in\mathcal S\}$ is the support of column $j$. A partition $g_1,\dots,g_\chi$ of $[d]$ is **structurally orthogonal** for $\mathcal S$ if no two columns of one group share a row:
--
--   $$\mathcal S_i\cap\mathcal S_j=\emptyset\qquad\text{for all distinct } i,j \text{ in the same group.}$$
--
--   The predicate says that $\mathcal S$ is symmetric, that every group is nonempty, and that the groups are structurally orthogonal. The number $\chi$ of groups is the effective dimension of the paper; in the dense case $\mathcal S=[d]\times[d]$ and the singletons give $\chi=d$.
--
--   **Formalization Note** Indices are 0-based: column $j$ lies in group `grp j : Fin χ`. "Partition into $\chi$ groups" is surjectivity of `grp` (no empty group).
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Definition 2.2, p. 7

import Mathlib

namespace RollingProbeQN.Convex

/-- **Pattern and structurally orthogonal partition (Definition 2.2).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Definition 2.2, p. 7: "A pattern is a symmetric set `S ⊆ [d] × [d]`, and
`S_j = {i : (i, j) ∈ S}` denotes the support of column `j`. A partition `g_1, …, g_χ` of `[d]` is
structurally orthogonal for `S` if no two columns in the same group share a row, that is,
`S_i ∩ S_j = ∅` for all distinct `i, j` in the same group."

`IsStructOrthPartition S grp` says that `S` is symmetric, that the fibres of `grp` form a partition of
the columns into `χ` nonempty groups, and that two distinct columns of one group share no row of `S`.

**Formalization Note.** Indices are 0-based: column `j : Fin d` lies in group `grp j : Fin χ`. A
partition has no empty block, which is surjectivity of `grp`. -/
def IsStructOrthPartition {d χ : ℕ} (S : Set (Fin d × Fin d)) (grp : Fin d → Fin χ) : Prop :=
  (∀ i j : Fin d, (i, j) ∈ S → (j, i) ∈ S) ∧
  Function.Surjective grp ∧
  ∀ i j : Fin d, i ≠ j → grp i = grp j → ∀ r : Fin d, ¬ ((r, i) ∈ S ∧ (r, j) ∈ S)

end RollingProbeQN.Convex


