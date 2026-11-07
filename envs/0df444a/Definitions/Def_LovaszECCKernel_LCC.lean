-- Prove2me | Definitions.Def_LovaszECCKernel_LCC
-- name    : LovaszECCKernel_LCC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:08.388698+00:00
-- url     : https://prove2.me/theorems/251783be-7830-4bda-befc-64bed01a993c
-- title:
--   The Lovász Clique Cover (LCC) of a deletion sequence
-- statement:
--   For an m.c.d.s. $\mathcal S=(C_1,\dots,C_t)$ with $t_2$ cliques of size at least two, the **Lovász Clique Cover** is the set $\mathcal C$ of cliques consisting of
--
--   1. (Type-A) $C_1,\dots,C_{t_2}$;
--   2. (Type-B) $\{v\}\cup(N_G(v)\cap C_i)$ for every $i\in\{1,\dots,t_2\}$ and every $v\in N_{G_i}(C_i)$,
--
--   where $G_1=G$, $G_{i+1}=G_i-C_i$, and $N_{G_i}(C_i)$ is the set of vertices of $G_i$ outside $C_i$ with a neighbour in $C_i$. Lovász's proof shows that $\mathcal C$ is an edge clique cover with at most $\mathrm{Lb}(G)$ cliques; the lemmas of the mission improve on it.
--
--   The number of Type-B index pairs is $\sum_{i\le t_2}|N_{G_i}(C_i)|$.
--
--   **Formalization Note** $\mathcal C$ is a finite set of cliques and $|\mathcal C|$ its cardinality. `typeBCount` counts the Type-B cliques by their index pairs $(i,v)$, i.e. with multiplicity. Indices are $0$-based as for m.c.d.s.
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), Definition 2, p.19 (= PDF p.19)

import Mathlib
import Definitions.Def_LovaszECCKernel_IsMCDS

set_option autoImplicit false

namespace LovaszECCKernel

open Classical in
/-- The **neighbourhood** `N_{G_i}(C_i)` of a clique in the graph `G_i = G[U]` (Fomin, Golovach,
Khargeliia, Sagunov, Simonov, *Stability Meets Kernelization: Algorithmic Extensions of the Lovász
and Erdős–Goodman–Pósa Theorems*, STOC 2027 submission (manuscript sha256 a9d53ab8…), §2, p.15 and
Definition 2, p.19 (= PDF pp.15, 19)): "For a set of vertices X, N_G(X) = (⋃_{v∈X} N_G(v)) \ X".

**Formalization Note** The vertices of `U \ C` with a neighbour in `C`. -/
noncomputable def nbhdIn {V : Type*} (G : SimpleGraph V) (U C : Finset V) : Finset V :=
  (U \ C).filter (fun v => ∃ u ∈ C, G.Adj u v)

/-- The number of **Type-B cliques** of the Lovász Clique Cover of a clique deletion sequence,
counted by their indices `(i, v)` (Fomin et al., STOC 2027 submission (manuscript sha256
a9d53ab8…), Definition 2, p.19 (= PDF p.19)): "(Type-B) Cliques {v} ∪ (N_G(v) ∩ Ci) for every
i ∈ {1, . . . , t2} and v ∈ N_{Gi}(Ci)", that is `Σ_{i ≤ t₂} |N_{G_i}(C_i)|`.

**Formalization Note** Counted with multiplicity over the pairs `(i, v)`, which is at least the
number of distinct Type-B cliques (the two coincide for an m.c.d.s.). Indices are 0-based:
`L.getD i ∅` is the paper's `C_{i+1}` and `remaining L i` the vertex set of `G_{i+1}`. -/
noncomputable def typeBCount {V : Type*} [Fintype V] (G : SimpleGraph V) (L : List (Finset V)) : ℕ :=
  ∑ i ∈ Finset.range (typeA L), (nbhdIn G (remaining L i) (L.getD i ∅)).card

open Classical in
/-- The **Lovász Clique Cover** (LCC) of a clique deletion sequence (Fomin et al., STOC 2027
submission (manuscript sha256 a9d53ab8…), Definition 2, p.19 (= PDF p.19)): "For a m.c.d.s.
S = (C1, C2, . . . , Ct), the Lovász Clique Cover is a set of cliques of G consisting of
(Type-A) C1, C2, . . . , Ct2 (all cliques of S of size at least 2);
(Type-B) Cliques {v} ∪ (N_G(v) ∩ Ci) for every i ∈ {1, . . . , t2} and v ∈ N_{Gi}(Ci). (Here,
G1 := G and Gi+1 := Gi − Ci.)"

**Formalization Note** A set (`Finset`) of cliques, as in the paper; `|C|` is its cardinality.
`t₂` is `typeA L`, the first `t₂` entries of an m.c.d.s. being its cliques of size at least `2`.
Indices are 0-based as in `remaining`. -/
noncomputable def LCC {V : Type*} [Fintype V] (G : SimpleGraph V) (L : List (Finset V)) :
    Finset (Finset V) :=
  (L.take (typeA L)).toFinset ∪
    (Finset.range (typeA L)).biUnion (fun i =>
      (nbhdIn G (remaining L i) (L.getD i ∅)).image
        (fun v => insert v ((L.getD i ∅).filter (fun u => G.Adj v u))))

end LovaszECCKernel


