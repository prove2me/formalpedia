-- Prove2me | Definitions.Def_GenTuranHard_blowUp
-- name    : GenTuranHard_blowUp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:34:22.229748+00:00
-- url     : https://prove2.me/theorems/0cd2a022-4393-46ed-b01f-fefaf1dd0d5b
-- title:
--   Blow-ups $T(s)$, “$F$ is a subgraph of a blow-up of $T$”, and the $B$-blow-up $G(B)$
-- statement:
--   For a graph $T$ and positive cluster sizes $s : V(T) \to \mathbb Z_{>0}$, the **blow-up** of $T$ replaces each vertex $w$ by an independent set (cluster) of $s(w)$ vertices and each edge by a complete bipartite graph between the corresponding clusters (p.3). Unless a common cluster size is specified, cluster sizes may differ (p.5). A graph $F$ **is a subgraph of a blow-up of $T$** if $F$ has a copy in the blow-up of $T$ for some positive cluster sizes.
--
--   For a finite graph $G$ on $\{0,\dots,n-1\}$ and a positive integer $B$, the **$B$-blow-up** $G(B)$ has vertex set $\{0, \dots, nB - 1\}$; the cluster $C_v$ of a vertex $v$ is $\{vB, \dots, vB + B - 1\}$, so vertex $i$ lies in the cluster of $\lfloor i/B \rfloor$, and $i, j$ are adjacent iff $\lfloor i/B\rfloor \lfloor j/B\rfloor$ is an edge of $G$ (p.4).
--
--   The first notion is the hypothesis of the goal theorem ("no $F \in \mathcal F$ is a subgraph of a blow-up of $T$"); the second builds the graph $Z$ of the reduction.
--
--   **Formalization Note** The general blow-up has vertex set $\bigsqcup_w \{0,\dots,s(w)-1\}$. The homomorphism criterion of p.4 ("$F$ is a subgraph of a blow-up of $T$ iff there is a homomorphism $F \to T$") is a theorem, not the definition.
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), p.3 (blow-up), p.4 (m-blow-up G(m), clusters), p.5 (unequal positive cluster sizes)

import Mathlib
import Definitions.Def_GenTuranHard_FinGraph

set_option autoImplicit false

namespace GenTuranHard

/-- The **blow-up** of `T` with cluster sizes `s` (Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256
dc85633a…, p.3 and pp.4–5): every vertex `w` of `T` is replaced by an independent set (cluster) of
`s w` vertices, `Fin (s w)`, and every edge by a complete bipartite graph between the corresponding
clusters. -/
def blowUp {W : Type} (T : SimpleGraph W) (s : W → ℕ) : SimpleGraph (Σ w, Fin (s w)) where
  Adj a b := T.Adj a.1 b.1
  symm := ⟨fun _ _ h => T.adj_symm h⟩
  loopless := ⟨fun _ h => T.loopless.irrefl _ h⟩

/-- "`F` is a subgraph of a blow-up of `T`" (p.3, p.5: "Unless a common cluster size is specified, a
blow-up may have unequal positive cluster sizes"): `F` has a copy in the blow-up of `T` for some
positive cluster sizes. -/
def InBlowUp {U W : Type} (F : SimpleGraph U) (T : SimpleGraph W) : Prop :=
  ∃ s : W → ℕ, (∀ w, 0 < s w) ∧ F.IsContained (blowUp T s)

/-- The cluster of a vertex of the uniform `B`-blow-up of an `n`-vertex graph: vertex `i` of
`Fin (n * B)` lies in the cluster of vertex `i / B` (it is the `(i % B)`-th vertex of that cluster). -/
def clusterOf (n B : ℕ) (i : Fin (n * B)) : Fin n :=
  ⟨i.val / B, Nat.div_lt_of_lt_mul (lt_of_lt_of_eq i.2 (Nat.mul_comm n B))⟩

/-- The **`B`-blow-up** `G(B)` of a finite graph `G` (p.4): each vertex `v` becomes the cluster
`C_v = {v·B, …, v·B + B − 1}` of `Fin (v(G)·B)`, an independent set, and each edge `uv` becomes the
complete bipartite graph between `C_u` and `C_v`. -/
def uBlowUp (G : FinGraph) (B : ℕ) : FinGraph :=
  ⟨G.1 * B, G.2.comap (clusterOf G.1 B)⟩

end GenTuranHard


