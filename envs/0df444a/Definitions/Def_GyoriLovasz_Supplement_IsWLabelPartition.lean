-- Prove2me | Definitions.Def_GyoriLovasz_Supplement_IsWLabelPartition
-- name    : GyoriLovasz_Supplement_IsWLabelPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:11:24.722932+00:00
-- url     : https://prove2.me/theorems/0827df01-6b8d-46e8-8f10-163a01eb9193
-- title:
--   Valid weighted partition: each part connected to its terminal, weight at most $c_t + w_{\max} - 1$
-- statement:
--   Let a weighted input with terminals $t_1,\dots,t_k$, capacities $c_1,\dots,c_k$ and weights $w_v$ be given. An output is a list of labels, one label $\ell(x)\in\{0,\dots,k-1\}$ for each vertex $x$; the part $V_i$ is the set of vertices with label $i$. The output is a **valid weighted partition** when, for every $i$:
--
--   1. $t_i\in V_i$ and $G[V_i]$ is connected to $t_i$, i.e. every $u\in V_i$ has a directed path to $t_i$ all of whose vertices lie in $V_i$;
--   2. the total weight of the non-terminals in $V_i$ satisfies
--   $$
--   \sum_{v\in V_i\setminus T} w_v\le c_i+w_{\max}-1 .
--   $$
--
--   Since every vertex receives exactly one label, the parts are disjoint and cover $V$. Unlike the unweighted case there is no size equality: parts are bounded only by weight.
--
--   **Formalization Note** The subtraction is in the natural numbers; it is exact whenever some non-terminal exists ($w_{\max}\ge 1$), and otherwise every part has weight $0$.
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Theorem 3, p.11; Theorem 4, p.12

import Mathlib
import Definitions.Def_GyoriLovasz_ConnectedTo
import Definitions.Def_GyoriLovasz_IsLabelPartition
import Definitions.Def_GyoriLovasz_Supplement_WInstance

namespace GyoriLovasz

namespace Supplement

/-- **The output of the weighted algorithm is a valid partition.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani,
*Breaking the Exponential Barrier*, arXiv:2608.30945 (held file sha256 3f80f82d…780e), Theorem 3, p.11, Theorem 4,
p.12: "partitions V(G) into parts ⟨V_t⟩_{t∈T} such that t ∈ V_t, G[V_t] is connected to t, and
∑_{v∈V_t\T} w_v ≤ c_t + w_max − 1 for every terminal t ∈ T."

**Formalization Note.** The output is a list with one label below `k` for each vertex, so the parts (`partOf`, from the
published `IsLabelPartition` module) are disjoint and cover `V`. For each `i < k`, with `(t_i, c_i)` entry `i` of
`terms`: part `i` is connected to `t_i` (which includes `t_i ∈` part `i`) and the weight of its non-terminals is at most
`c_i + w_max − 1`. The subtraction is in `ℕ`; it is exact whenever there is a non-terminal (`w_max ≥ 1` by positive
weights), and otherwise every part has weight `0`. There is no size condition. -/
def IsWLabelPartition (I : WInstance) (L : List ℕ) : Prop :=
  L.length = I.base.n ∧ (∀ l ∈ L, l < I.base.terms.length) ∧
    ∀ (i : ℕ) (hi : i < I.base.terms.length),
      ConnectedTo I.base.toDG (partOf I.base.n L i) I.base.terms[i].1 ∧
        ∑ v ∈ partOf I.base.n L i \ I.base.termSet, I.w v ≤ I.base.terms[i].2 + I.wmax - 1

end Supplement

end GyoriLovasz


