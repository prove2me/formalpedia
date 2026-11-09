-- Prove2me | Definitions.Def_AgnosticTNS_LearningSequence
-- name    : AgnosticTNS_LearningSequence
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:13.263446+00:00
-- url     : https://prove2.me/theorems/ea25cdc5-e43d-4116-8208-3741f539f2a5
-- title:
--   Learning sequence
-- statement:
--   Let $G=(V,E)$ be a graph with $V=[n]$. A **learning sequence** for $G$ is a finite family $\mathcal L=(S_i,I_i,F_i)_{i=1}^L$ with:
--   1. $S_i\subseteq V$ is nonempty, $I_i\subseteq[i-1]$ and $F_i\subseteq V$ for every $i\in[L]$;
--   2. $S_i=F_i\sqcup\bigsqcup_{j\in I_i}S_j$ (a disjoint union) for every $i$;
--   3. the sets $F_1,\dots,F_L$ are pairwise disjoint;
--   4. the directed graph on $[L]$ with an edge $i\to j$ whenever $j\in I_i$ is a rooted tree with root $L$;
--   5. $S_L=V$.
--
--   $I_i$ are the children of step $i$ in the dependency tree and $F_i$ the vertices first introduced at step $i$.
--
--   **Formalization Note** Steps are `Fin L` with $L\ge1$ (0-based), the root is step $L-1$; $I_i\subseteq[i-1]$ is $j\in I_i\Rightarrow j<i$. Condition 4 is stated as: every non-root step lies in exactly one $I_i$ and the root in none, which, since edges point to smaller indices, is exactly a rooted tree with root $L$. The definition only uses the vertex set of $G$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Definition 2.3, p.13

import Mathlib

namespace AgnosticTNS

/-- **Learning sequence**, Definition 2.3, p.13 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). A learning sequence for a graph
`G = (V, E)` with `V = [n]` is a finite family `(S_i, I_i, F_i)_{i=1}^L` with
1. `S_i ⊆ V` nonempty, `I_i ⊆ [i − 1]`, `F_i ⊆ V`;
2. `S_i = F_i ⊔ ⨆_{j ∈ I_i} S_j` (a disjoint union);
3. `F_1, …, F_L` pairwise disjoint;
4. the directed graph on `[L]` with an edge `i → j` whenever `j ∈ I_i` is a rooted tree with root `L`;
5. `S_L = V`.

**Formalization Note** Steps are `Fin L` (0-based); the root, the paper's step `L`, is `⟨L − 1, _⟩`,
and `L ≥ 1`. `I_i ⊆ [i − 1]` is `j ∈ I_i → j < i`. Condition 4: every non-root step lies in exactly
one `I_i` and the root lies in none; since edges point to smaller indices this is exactly a rooted
tree with root `L`. The definition uses only the vertex set of `G`, so it is stated for `Fin n`. -/
structure LearningSequence (n : ℕ) where
  /-- the length `L` -/
  L : ℕ
  L_pos : 0 < L
  /-- the vertex set `S_i` represented at step `i` -/
  S : Fin L → Finset (Fin n)
  /-- the children `I_i` of step `i` -/
  I : Fin L → Finset (Fin L)
  /-- the fresh vertices `F_i` of step `i` -/
  F : Fin L → Finset (Fin n)
  S_nonempty : ∀ i, (S i).Nonempty
  I_lt : ∀ i, ∀ j ∈ I i, j < i
  S_eq : ∀ i, S i = F i ∪ (I i).biUnion S
  F_disjoint_S : ∀ i, ∀ j ∈ I i, Disjoint (F i) (S j)
  S_disjoint : ∀ i, ∀ j ∈ I i, ∀ k ∈ I i, j ≠ k → Disjoint (S j) (S k)
  F_disjoint : ∀ i j, i ≠ j → Disjoint (F i) (F j)
  parent_unique : ∀ j : Fin L, j.val ≠ L - 1 → ∃! i, j ∈ I i
  root_no_parent : ∀ i, (⟨L - 1, by omega⟩ : Fin L) ∉ I i
  S_root : S ⟨L - 1, by omega⟩ = Finset.univ

end AgnosticTNS


