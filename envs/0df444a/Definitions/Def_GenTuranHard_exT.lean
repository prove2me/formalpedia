-- Prove2me | Definitions.Def_GenTuranHard_exT
-- name    : GenTuranHard_exT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:34:17.988525+00:00
-- url     : https://prove2.me/theorems/71381c65-7a1f-40c9-85f8-22a9c1fbf088
-- title:
--   $\mathrm{ex}(G,T,\mathcal F)$ and $\mathrm{ex}'(G,T,\mathcal F)$
-- statement:
--   Let $G$ and $T$ be finite graphs and $\mathcal F$ a family of graphs. A **copy** of $T$ in $H$ is a not necessarily induced subgraph of $H$ isomorphic to $T$; copies with different vertex sets or different edge sets are counted separately, and $N(H, T)$ denotes their number (p.4). Then (Definition 1.1, p.2, and p.4)
--
--   $$
--   \mathrm{ex}(G, T, \mathcal F) = \max\{N(H, T) : H \subseteq G,\ H \text{ is } \mathcal F\text{-free}\},
--   $$
--   $$
--   \mathrm{ex}'(G, T, \mathcal F) = \max\{N(H, T) : H \subseteq G,\ V(H) = V(G),\ H \text{ is } \mathcal F\text{-free}\}.
--   $$
--
--   The first maximum ranges over all subgraphs of $G$ (any vertex subset and edge subset), the second over spanning subgraphs only. They differ when members of $\mathcal F$ have isolated vertices. These are the two objective functions whose approximation is shown NP-hard.
--
--   **Formalization Note** $N(H, T)$ is Mathlib's `copyCount`, the number of subgraphs of $H$ isomorphic to $T$; isolated vertices of $T$ are mapped to vertices of $H$. The maxima are finite maxima in $\mathbb N$ (value $0$ if no subgraph qualifies, which cannot happen when no member of $\mathcal F$ is empty, since the empty subgraph is then $\mathcal F$-free).
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), Definition 1.1, p.2; §2, p.4

import Mathlib
import Definitions.Def_GenTuranHard_FinGraph

set_option autoImplicit false

namespace GenTuranHard

open scoped Classical in
/-- **ex(G, T, 𝓕)** (Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256 dc85633a…, Definition 1.1 (i),
p.2, and p.4): the maximum number `N(H, T)` of copies of `T` in an `𝓕`-free subgraph `H` of `G`,
`max{N(H, T) : H ⊆ G, H is 𝓕-free}`. A subgraph has an arbitrary vertex subset and edge subset.
`N(H, T)` is Mathlib's `copyCount`: the number of subgraphs of `H` isomorphic to `T`, so copies with
different vertex sets or edge sets are counted separately, and isolated vertices of `T` are mapped to
vertices of `H`.

**Formalization Note** The maximum is a `Finset.sup` in `ℕ` over the finitely many subgraphs of `G`;
when no subgraph is `𝓕`-free the value is `0` (this cannot happen when no member of `𝓕` is empty,
since then the empty subgraph is `𝓕`-free). -/
noncomputable def exT {V W : Type} [Fintype V] (G : SimpleGraph V)
    (T : SimpleGraph W) (Fam : Set FinGraph) : ℕ :=
  (Finset.univ.filter (fun H : G.Subgraph => FamFree Fam H.coe)).sup
    (fun H => H.coe.copyCount T)

open scoped Classical in
/-- **ex′(G, T, 𝓕)** (Definition 1.1 (ii), p.2, and p.4): the maximum number of copies of `T` in an
`𝓕`-free **spanning** subgraph of `G`, `max{N(H, T) : H ⊆ G, V(H) = V(G), H is 𝓕-free}`.

**Formalization Note** As for `exT`, with the extra condition `H.verts = univ`; `0` when no spanning
subgraph is `𝓕`-free. -/
noncomputable def exSpan {V W : Type} [Fintype V] (G : SimpleGraph V)
    (T : SimpleGraph W) (Fam : Set FinGraph) : ℕ :=
  (Finset.univ.filter (fun H : G.Subgraph => H.verts = Set.univ ∧ FamFree Fam H.coe)).sup
    (fun H => H.coe.copyCount T)

end GenTuranHard


