-- Prove2me | Definitions.Def_MonoTestDAG_IsPMRSWitness
-- name    : MonoTestDAG_IsPMRSWitness
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:08:37.521835+00:00
-- url     : https://prove2.me/theorems/5c39c2b7-7d0d-41c8-9322-8a82ac1c7fce
-- title:
--   Definition 4.3: PMRS graphs and witnesses
-- statement:
--   Fix $\varepsilon\in(0,1/2]$ and $s,n_0\in\mathbb N$. A bipartite graph $U=(L,R;E)$ with $|L|=|R|=n_0$ is an **$(s,\varepsilon)$-PMRS graph** if there is an indexed sequence $M=(M_1,\dots,M_s)$ of matchings in $E$ such that:
--
--   1. (edge-disjoint) $M_i\cap M_j=\emptyset$ for all $i\ne j$;
--   2. (linear size) $|M_i|\ge\varepsilon n_0$ for all $i$;
--   3. (positive) each $M_i$ is a positive matching in $U$.
--
--   Any such sequence is an **$(s,\varepsilon)$-PMRS witness** for $U$.
--
--   **Formalization Note.** The conditions $\varepsilon\in(0,1/2]$, $|L|=|R|$ and $s\ge1$ are part of the predicate. Here $s\in\mathbb N$ is read as a positive integer, since the paper defines $[K]$ only for positive $K$ (p.1); with $s=0$ Lemma 5.2's conclusion is false on an edgeless graph. The module also defines `IsPMRSGraph`.
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), Definition 4.3, p.17

import Mathlib
import Definitions.Def_MonoTestDAG_bipDAG

namespace MonoTestDAG

/-- **Definition 4.3 (PMRS witness).** Fix `ε ∈ (0, 1/2]` and `s, n₀ ∈ ℕ`. For a bipartite graph
`U = (L, R; E)` with `|L| = |R| = n₀`, an indexed sequence `M = (M_1, …, M_s)` of matchings in `E`
is an `(s, ε)`-PMRS witness for `U` if
1. (edge-disjoint) `M_i ∩ M_j = ∅` for all `i ≠ j`;
2. (linear size) `|M_i| ≥ ε n₀` for all `i`;
3. (positive) each `M_i` is a positive matching in `U`.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Definition 4.3, p.17.

**Formalization Note.** The standing conditions of the definition are part of the predicate:
`ε ∈ (0, 1/2]`, `|L| = |R|`, and `s ≥ 1` (`s ∈ ℕ` read as a positive integer, as `[K]` is only
defined for positive `K`, p.1). The matchings are indexed by `Fin s`. -/
def IsPMRSWitness {L R : Type} [Fintype L] [Fintype R] (EU : Finset (L × R)) (ε : ℝ) (s : ℕ)
    (M : Fin s → Finset (L × R)) : Prop :=
  0 < ε ∧ ε ≤ 1 / 2 ∧ 1 ≤ s ∧ Fintype.card L = Fintype.card R ∧
    (∀ i j, i ≠ j → Disjoint (M i) (M j)) ∧
    (∀ i, ε * (Fintype.card L : ℝ) ≤ ((M i).card : ℝ)) ∧
    (∀ i, IsPositiveMatching EU (M i))

/-- **Definition 4.3 (PMRS graph).** `U = (L, R; E)` is an `(s, ε)`-PMRS graph if it has an
`(s, ε)`-PMRS witness. Yoshida, arXiv:2602.15341 (sha256 454609db…), Definition 4.3, p.17. -/
def IsPMRSGraph {L R : Type} [Fintype L] [Fintype R] (EU : Finset (L × R)) (ε : ℝ) (s : ℕ) :
    Prop :=
  ∃ M : Fin s → Finset (L × R), IsPMRSWitness EU ε s M

end MonoTestDAG


