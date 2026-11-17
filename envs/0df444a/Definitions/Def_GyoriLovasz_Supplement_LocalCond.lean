-- Prove2me | Definitions.Def_GyoriLovasz_Supplement_LocalCond
-- name    : GyoriLovasz_Supplement_LocalCond
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:13:03.158639+00:00
-- url     : https://prove2.me/theorems/f3533f60-05a4-4c39-846d-3b541453dbce
-- title:
--   Local connected set $\mathcal L(T')$ and the local connectivity condition
-- statement:
--   Let $G=(V,E)$ be a directed graph with terminal set $T\subseteq V$, $|T|=k$, $|V|=n$, and capacities $c_t\in\mathbb N$. For $T'\subseteq T$, a non-terminal $v\in V\setminus T$ is **locally connected** to $T'$ if there are $|T'|$ internally vertex-disjoint paths from $v$ to vertices of $T'$; by convention, a pre-terminal of some $t\in T'$ (a non-terminal with an edge to $t$) is locally connected to $T'$. The **local connected set** $\mathcal L(T')$ is the set of non-terminals locally connected to $T'$.
--
--   $G$ satisfies the **local connectivity condition** with respect to capacities $c$ with $\sum_{t\in T}c_t=n-k$ if
--
--   $$
--   |\mathcal L(T')|\ge\sum_{t\in T'}c_t\qquad\text{for every } T'\subseteq T .
--   $$
--
--   Every $k$-$T$-connected graph satisfies it (Lemma A.4); it is the hypothesis of Theorems 7 and 8.
--
--   **Formalization Note** The definition is made only for capacities with $\sum_{t\in T}c_t=n-k$, so this equation, written $\sum_t c_t=|V\setminus T|$, is the first clause of the condition.
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Definition A.2, pp.54–55; Definition A.3, p.55

import Mathlib
import Definitions.Def_GyoriLovasz_PT
import Definitions.Def_GyoriLovasz_Supplement_IDFamily

namespace GyoriLovasz

namespace Supplement

open Classical in
/-- **The local connected set `L(T′)`.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential
Barrier*, arXiv:2608.30945 (held file sha256 3f80f82d…780e), Definition A.2, pp.54–55: "A vertex v ∈ V \ T is locally
connected to T′ if there exist |T′| internally vertex-disjoint paths from v to vertices of T′. By convention, a
pre-terminal of some t ∈ T′ is considered to have arbitrarily many paths to t, and hence is locally connected to T′. The
local connected set of T′, denoted by L(T′), is the set of all non-terminal vertices v ∈ V \ T that are locally
connected to T′."

**Formalization Note.** The pre-terminal convention is the disjunct `v ∈ PT G T T'` (the published pre-terminals). -/
noncomputable def localSet {V : Type*} [DecidableEq V] (G : DG V) (T T' : Finset V) : Finset V :=
  (G.verts \ T).filter fun v => v ∈ PT G T T' ∨ IDFamily G T' v T'.card

/-- **The local connectivity condition.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential
Barrier*, arXiv:2608.30945 (held file sha256 3f80f82d…780e), Definition A.3, p.55: "A directed graph G = (V, E) with
|V| = n and terminal set T ⊆ V with |T| = k satisfies the local connectivity condition with respect to capacities c
satisfying ∑_{t∈T} c_t = n − k if, for every subset T′ ⊆ T, the local connected set of T′ has size at least the total
capacity of the terminals in T′. Equivalently, for every subset T′ ⊆ T: |L(T′)| ≥ ∑_{t∈T′} c_t."

**Formalization Note.** The definition is made only for capacities with `∑ c_t = n − k`, so that equation, written
`∑ c_t = |V \ T|` (equal to `n − k` for `T ⊆ V`), is the first clause. `c` is total; only `c` on `T` is read. -/
def LocalCond {V : Type*} [DecidableEq V] (G : DG V) (T : Finset V) (c : V → ℕ) : Prop :=
  ∑ t ∈ T, c t = (G.verts \ T).card ∧ ∀ T' ⊆ T, ∑ t ∈ T', c t ≤ (localSet G T T').card

end Supplement

end GyoriLovasz


