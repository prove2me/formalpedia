-- Prove2me | Definitions.Def_WangKangXue_SpectralTuran_IsMaxCut
-- name    : WangKangXue_SpectralTuran_IsMaxCut
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T14:22:31.85352+00:00
-- url     : https://prove2.me/theorems/a8c7318d-61e9-4c50-8614-97e0f7ce2bc3
-- title:
--   Partitions V_1 ∪ ⋯ ∪ V_r maximising Σ_{i<j} e(V_i, V_j)
-- statement:
--   Let $G$ be a finite simple graph and $r \ge 1$. A partition $V(G) = V_1 \cup \dots \cup V_r$ into $r$ (possibly empty) parts is encoded by a labelling $P : V(G) \to \{1,\dots,r\}$ with $V_i = P^{-1}(i)$. This file defines:
--
--   1. the parts $V_i = \{v : P(v) = i\}$;
--   2. the complete $r$-partite graph $K = K_r(n_1,\dots,n_r)$ on the parts, in which $u \sim v$ iff $u$ and $v$ lie in different parts ($n_i = |V_i|$);
--   3. the number of crossing edges $\sum_{1 \le i < j \le r} e(V_i, V_j)$, i.e. the number of edges of $G$ whose ends lie in different parts (the edges of $G$ that are also edges of $K$);
--   4. **maximum partitions**: $P$ is a maximum partition if
--   $$
--   \sum_{1 \le i < j \le r} e(V_i, V_j) \ \ge\ \sum_{1 \le i < j \le r} e(V'_i, V'_j)
--   $$
--   for every partition $V(G) = V'_1 \cup \dots \cup V'_r$.
--
--   Lemma 3.3 of the paper introduces such a partition of the spectral extremal graph ("such that $\sum_{1\le i<j\le r} e(V_i,V_j)$ attains the maximum"), and all later lemmas are about it.
--
--   **Formalization Note** Parts are allowed to be empty, as in the paper's maximisation; Lemma 3.3 shows that for the graphs of interest they are not.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, p. 4 (Lemma 3.3: the maximising partition) and p. 12 (K = K_r(n_1, …, n_r))

import Mathlib

namespace WangKangXue.SpectralTuran

/-- The part `V_i = P⁻¹(i)` of the vertex partition `V = V_1 ∪ ⋯ ∪ V_r` encoded by a labelling
`P : V → Fin r` (parts may be empty). -/
noncomputable def part {V : Type*} [Fintype V] {r : ℕ} (P : V → Fin r) (i : Fin r) :
    Finset V := by
  classical
  exact Finset.univ.filter (fun v => P v = i)

/-- `K = K_r(n_1, …, n_r)`: the complete `r`-partite graph on the parts of `P`; two vertices
are adjacent iff they lie in different parts. -/
def completePartite {V : Type*} {r : ℕ} (P : V → Fin r) : SimpleGraph V where
  Adj u v := P u ≠ P v
  symm := ⟨fun _ _ h => Ne.symm h⟩
  loopless := ⟨fun _ h => h rfl⟩

open Classical in
/-- `∑_{1 ≤ i < j ≤ r} e(V_i, V_j)`: the number of edges of `G` whose endpoints lie in
different parts of `P` (the edges of `G ⊓ K`). -/
noncomputable def crossEdges {V : Type*} [Fintype V] (G : SimpleGraph V) {r : ℕ}
    (P : V → Fin r) : ℕ :=
  (G ⊓ completePartite P).edgeFinset.card

/-- `P` is a partition `V = V_1 ∪ ⋯ ∪ V_r` (into `r` possibly empty parts) for which
`∑_{1 ≤ i < j ≤ r} e(V_i, V_j)` attains the maximum over all such partitions. -/
def IsMaxCut {V : Type*} [Fintype V] (G : SimpleGraph V) {r : ℕ} (P : V → Fin r) : Prop :=
  ∀ P' : V → Fin r, crossEdges G P' ≤ crossEdges G P

end WangKangXue.SpectralTuran


