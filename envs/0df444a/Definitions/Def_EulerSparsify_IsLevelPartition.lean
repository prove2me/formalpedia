-- Prove2me | Definitions.Def_EulerSparsify_IsLevelPartition
-- name    : EulerSparsify_IsLevelPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:37:01.684724+00:00
-- url     : https://prove2.me/theorems/758df47e-74e7-4e6d-91e6-4cf8d8e2b0e0
-- title:
--   The guarantee of Lemma 4.2 for a vertex partition
-- statement:
--   Let $G=(V,E)$ be a finite graph (weights $1$ in Lemma 4.2), and let $\beta>0$, $p$, $\eta$ and $C$ be reals. A family $\{U_i\}_{i\in[I]}$ of vertex sets satisfies the guarantee if
--
--   1. it is a partition of $V$ (pairwise disjoint, covering every vertex; empty parts are allowed);
--   2. every induced subgraph $G[U_i]$ is connected and $\mathrm{diam}_{\mathrm{ER}}(G[U_i])\le C/\beta$;
--   3. the number of edges whose endpoints lie in different parts satisfies
--   $$\Bigl|E\setminus\bigcup_{i\in[I]}E(G[U_i])\Bigr|\le\eta\beta^{1-p}\Bigl[\sum_{i\in[I]}\bigl(\beta|U_i|+\mathrm{vol}_G(U_i)\bigr)^p-\bigl(\beta|V|+\mathrm{vol}(G)\bigr)^p\Bigr].$$
--
--   **Formalization Note** In Lemma 4.2 the constant $C=C(p,\eta)$ realises $O_{p,\eta}(1/\beta)$. An empty part contributes $0^p=0$. Powers are real powers.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Lemma 4.2, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph_restrict
import Definitions.Def_EulerSparsify_DiGraph_DiamERLe
import Definitions.Def_EulerSparsify_DiGraph_volReg

namespace EulerSparsify

/-- **The guarantee of Lemma 4.2** (p.12, PDF p.14) for one vertex partition.
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Lemma 4.2: "computes a partitioning {U_i}_{i∈[I]} of the vertices such that
1. ER diameter: diam_ER(G[U_i]) ≤ O_{p,η}(1/β)
2. Cut size: |E ∖ ⋃_{i∈[I]} E(G[U_i])| ≤ ηβ^{1−p} [Σ_{i∈I} (β|U_i| + vol_G(U_i))^p − (β|V| + vol(G))^p]".

`IsLevelPartition G β p η C U` says that `{U_i}_{i ∈ Fin I}` is a partition of `V` (pairwise
disjoint, covering every vertex), that every induced subgraph `G[U_i]` is connected with ER
diameter at most `C/β`, and that the number of edges with endpoints in two different parts is at
most `ηβ^{1−p}[Σ_i (β|U_i| + vol_G(U_i))^p − (β|V| + vol_G(V))^p]`.

**Formalization Note.** `O_{p,η}(1/β)` is `C/β` with `C` depending only on `p`, `η` (quantified
in Lemma 4.2's statement). Empty parts are allowed (`0^p = 0`). Powers are real powers. -/
def IsLevelPartition {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DiGraph V E) (β p η C : ℝ) {I : ℕ} (U : Fin I → Finset V) : Prop :=
  (∀ i i', i ≠ i' → Disjoint (U i) (U i')) ∧ (∀ v, ∃ i, v ∈ U i) ∧
  (∀ i, (G.restrict (G.inducedEdges (U i))).DiamERLe (U i) (C / β)) ∧
  (((Finset.univ.filter fun e => ∀ i, e ∉ G.inducedEdges (U i)).card : ℝ) ≤
    η * β ^ (1 - p) *
      (∑ i, (β * (U i).card + G.vol (U i)) ^ p - (β * Fintype.card V + G.vol Finset.univ) ^ p))

end EulerSparsify


