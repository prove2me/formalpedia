-- Prove2me | Definitions.Def_LovaszECCKernel_IsMCDS
-- name    : LovaszECCKernel_IsMCDS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:55:03.360894+00:00
-- url     : https://prove2.me/theorems/0dacbd2b-5425-4ff0-96bc-5b44aa4173c6
-- title:
--   Maximal clique deletion sequences (m.c.d.s.) and the number $t_2$ of Type-A cliques
-- statement:
--   For a graph $G$, a sequence $C_1,\dots,C_t$ of cliques is a **maximal clique deletion sequence** (m.c.d.s.) if
--
--   1. $\bigcup_{i=1}^t C_i=V(G)$;
--   2. each $C_i$ is an inclusion-wise maximal clique of $G_i$, where $G_1=G$ and $G_{i+1}=G_i-C_i$;
--   3. there is $t_2$ such that $|C_i|>1$ for $i\le t_2$ and $|C_i|=1$ for $i>t_2$.
--
--   The cliques $C_i$ partition $V(G)$, the cliques of size at least two come first, and their number $t_2$ is the number of **Type-A** cliques of the Lovász Clique Cover.
--
--   **Formalization Note** A sequence is a list indexed from $0$ (the Lean entry $i$ is the paper's $C_{i+1}$); `remaining L i` is the vertex set of the paper's $G_{i+1}$, and maximality is among cliques of $G$ inside it. The third condition is read with $t_2\in\{0,\dots,t\}$: in an edgeless graph every clique is a singleton and $t_2=0$; the printed $t_2\in[t]$ would leave edgeless graphs without an m.c.d.s., while Lovász's construction and the proof of Lemma 8 use them. The empty graph has the empty sequence.
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), Definition 1, p.19 (= PDF p.19)

import Mathlib

set_option autoImplicit false

namespace LovaszECCKernel

open Classical in
/-- The vertex set of the graph `G_{i+1}` of a clique deletion sequence (Fomin, Golovach,
Khargeliia, Sagunov, Simonov, *Stability Meets Kernelization: Algorithmic Extensions of the Lovász
and Erdős–Goodman–Pósa Theorems*, STOC 2027 submission (manuscript sha256 a9d53ab8…),
Definition 1, p.19 (= PDF p.19): "G1 := G and Gi+1 := Gi − Ci").

**Formalization Note** The sequence is a list `L = [C₁, C₂, …]`, indexed from `0` in Lean:
`remaining L i = V \ (C₁ ∪ ⋯ ∪ C_i)` is the vertex set of the paper's `G_{i+1}`, the graph from
which the Lean entry `L[i]` (the paper's `C_{i+1}`) is chosen. `G_{i+1}` is the subgraph of `G`
induced on it. -/
noncomputable def remaining {V : Type*} [Fintype V] (L : List (Finset V)) (i : ℕ) : Finset V :=
  Finset.univ \ (L.take i).foldr (· ∪ ·) ∅

/-- `C` is an (inclusion-wise) **maximal clique of the induced subgraph** `G[U]`
(Fomin et al., STOC 2027 submission (manuscript sha256 a9d53ab8…), Definition 1, p.19
(= PDF p.19): "Ci is an (inclusion-wise) maximal clique in the graph Gi").

**Formalization Note** A clique of `G[U]` is a clique of `G` contained in `U`; `C` is maximal among
those. For `U = ∅` the only such clique is `∅`. -/
def IsMaxCliqueIn {V : Type*} (G : SimpleGraph V) (U C : Finset V) : Prop :=
  C ⊆ U ∧ G.IsClique (C : Set V) ∧
    ∀ D : Finset V, C ⊆ D → D ⊆ U → G.IsClique (D : Set V) → D = C

open Classical in
/-- A **maximal clique deletion sequence** (m.c.d.s.) (Fomin et al., STOC 2027 submission
(manuscript sha256 a9d53ab8…), Definition 1, p.19 (= PDF p.19)): "For a (non-empty) graph G, a
sequence C1, C2, . . . , Ct ⊆ V(G) of cliques of G is a maximal clique deletion sequence (m.c.d.s.)
if
• ⋃_{i=1}^{t} Ci = V(G), and
• for every i ∈ [t], Ci is an (inclusion-wise) maximal clique in the graph Gi, where G1 := G and
  Gi+1 := Gi − Ci, and
• there is t2 ∈ [t] such that |Ci| > 1 for i ≤ t2 and |Ci| = 1 for i > t2."

**Formalization Note** The sequence is a list indexed from `0` (`L[i]` is the paper's `C_{i+1}`).
The third bullet is read with `t₂ ∈ {0, …, t}`: in an edgeless graph every `C_i` is a singleton and
`t₂ = 0` (Lovász's construction and step 7 of the proof of Lemma 8 produce this case); the paper's
`t₂ ∈ [t]` would leave edgeless graphs without any m.c.d.s. The empty graph (`V = ∅`) has the empty
list as its m.c.d.s. The bullets force every `C_i` to be non-empty, so the list partitions `V`. -/
def IsMCDS {V : Type*} [Fintype V] (G : SimpleGraph V) (L : List (Finset V)) : Prop :=
  L.foldr (· ∪ ·) ∅ = Finset.univ ∧
  (∀ i (h : i < L.length), IsMaxCliqueIn G (remaining L i) L[i]) ∧
  ∃ t₂ ≤ L.length, ∀ i (h : i < L.length), (i < t₂ → 1 < L[i].card) ∧ (t₂ ≤ i → L[i].card = 1)

/-- The number `t₂` of cliques of size at least `2` in a clique deletion sequence, i.e. the number
of **Type-A cliques** of its Lovász Clique Cover (Fomin et al., STOC 2027 submission (manuscript
sha256 a9d53ab8…), Definitions 1–2, p.19 (= PDF p.19): "(Type-A) C1, C2, . . . , Ct2 (all cliques of
S of size at least 2)").

**Formalization Note** For an m.c.d.s. these are the first `t₂` entries of the list. -/
def typeA {V : Type*} (L : List (Finset V)) : ℕ := L.countP (fun C => 2 ≤ C.card)

end LovaszECCKernel


