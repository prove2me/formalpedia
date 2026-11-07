-- Prove2me | Definitions.Def_GyoriLovasz_IsLabelPartition
-- name    : GyoriLovasz_IsLabelPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:51:38.84517+00:00
-- url     : https://prove2.me/theorems/c813ab38-ff4c-4661-a8df-28c6c014f415
-- title:
--   The output labels form a valid partition
-- statement:
--   An output is a list $L$ of labels, one for each vertex. The part $V_i$ is the set of vertices with label $i$. The output is **correct** for an input with terminals $(t_i,c_i)_{i<k}$ if $L$ has length $n$, every label is below $k$, and for every $i<k$
--   $$t_i\in V_i,\qquad |V_i|=c_i+1,\qquad G[V_i]\text{ is connected to } t_i.$$
--   Since every vertex carries exactly one label below $k$, the parts are disjoint and cover the vertex set.
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Theorem 1, p.5

import Mathlib
import Definitions.Def_GyoriLovasz_ConnectedTo
import Definitions.Def_GyoriLovasz_Instance

namespace GyoriLovasz

/-- The part `V_i` of a label list: the vertices `x < n` whose label is `i`. -/
def partOf (n : ℕ) (L : List ℕ) (i : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun x => L[x]? = some i

/-- **The output of the algorithm is a valid partition.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Theorem 1, p.5: "partitions the vertices of the graph into
V_1, ..., V_k, such that t_i ∈ V_i, |V_i| = c_i + 1, and the induced subgraph G[V_i] is connected to t_i."

**Formalization Note.** The output is a list with one label below `k` for each vertex, so the parts are automatically
disjoint and cover `V`. For each `i < k`, with `(t_i, c_i)` entry `i` of `terms`: `t_i` is in part `i` (a clause of
`ConnectedTo`), the part has `c_i + 1` vertices, and it is connected to `t_i`. -/
def IsLabelPartition (I : Instance) (L : List ℕ) : Prop :=
  L.length = I.n ∧ (∀ l ∈ L, l < I.terms.length) ∧
    ∀ (i : ℕ) (hi : i < I.terms.length),
      (partOf I.n L i).card = I.terms[i].2 + 1 ∧ ConnectedTo I.toDG (partOf I.n L i) I.terms[i].1

end GyoriLovasz


