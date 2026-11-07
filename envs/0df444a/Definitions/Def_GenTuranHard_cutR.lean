-- Prove2me | Definitions.Def_GenTuranHard_cutR
-- name    : GenTuranHard_cutR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:34:19.489731+00:00
-- url     : https://prove2.me/theorems/2d69d42b-7b95-43f0-9c06-5c39fcbf9c02
-- title:
--   $\mathrm{cut}_r(G)$ and the dense class $\mathcal G_k$
-- statement:
--   For a graph $G$ and an integer $r$, the **Max $r$-Colorable Subgraph** value is (§2.1, p.5)
--
--   $$
--   \mathrm{cut}_r(G) = \max\{e(H) : H \subseteq G,\ V(H) = V(G),\ \chi(H) \le r\},
--   $$
--
--   the largest number of edges of an $r$-colorable spanning subgraph of $G$.
--
--   For constants $\mu > 0$ and $n_0$, the **dense class** is (p.12)
--
--   $$
--   \mathcal G_k = \{G : v(G) \ge n_0,\ \delta(G) \ge (1 - \mu)\, v(G)\},
--   $$
--
--   where $\delta(G)$ is the minimum degree; in the paper $\mu = \mu(k)$ and $n_0 = n_0(k)$ are supplied by Lemma 3.4. The reduction starts from computing $\mathrm{cut}_{k-1}$ on $\mathcal G_k$.
--
--   **Formalization Note** $\chi(H) \le r$ is $r$-colorability. The maximum is a finite maximum in $\mathbb N$. The class is a predicate on finite graphs with the constants as parameters.
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), §2.1, p.5 (cut_r); p.12 (𝒢_k)

import Mathlib
import Definitions.Def_GenTuranHard_FinGraph

set_option autoImplicit false

namespace GenTuranHard

open scoped Classical in
/-- **cut_r(G)** (Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256 dc85633a…, §2.1, p.5): the maximum
number of edges of a spanning subgraph `H` of `G` with `χ(H) ≤ r`,
`cut_r(G) = max{e(H) : H ⊆ G, V(H) = V(G), χ(H) ≤ r}` (Max `r`-Colorable Subgraph).

**Formalization Note** A spanning subgraph is a graph `H ≤ G` on the same vertex type, and
`χ(H) ≤ r` is `H.Colorable r`. The maximum is a `Finset.sup` over the finitely many such `H` (the empty
graph is one of them for every `r ≥ 1`). -/
noncomputable def cutR (r : ℕ) {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
    (Finset.univ.filter (fun H : SimpleGraph V => H ≤ G ∧ H.Colorable r)).sup edgeCount

open scoped Classical in
/-- Membership in the dense class `𝒢_k = {G : v(G) ≥ n₀, δ(G) ≥ (1 − µ)v(G)}` (p.12) for given
constants `µ` and `n₀` (Lemma 3.4 supplies them). `δ(G)` is the minimum degree. -/
noncomputable def InGk (μ : ℝ) (n0 : ℕ) (G : FinGraph) : Prop :=
 n0 ≤ G.1 ∧ (1 - μ) * (G.1 : ℝ) ≤ (G.2.minDegree : ℝ)

end GenTuranHard


